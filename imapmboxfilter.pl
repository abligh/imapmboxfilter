#! /usr/bin/env perl

# imapmboxfilter.pl
#
# Copyright (C) 2012 Alex Bligh <alex@alex.org.uk>
# All rights reserved.
#
# Redistribution and use in source and binary forms are permitted
# provided that the above copyright notice and this paragraph are
# duplicated in all such forms and that any documentation,
# advertising materials, and other materials related to such
# distribution and use acknowledge that the software was developed
# by the author. The name of the author may not be used to endorse
# or promote products derived from this software without specific
# prior written permission.
#
# THIS SOFTWARE IS PROVIDED "AS IS" AND WITHOUT ANY EXPRESS OR
# IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
# PURPOSE.

# Inspired by imapfilter.pl  Lars Eggert <lars.eggert@gmail.com>
# but almost entirely rewritten bar daemonize.

use warnings;
use strict;

use IO::Socket::SSL qw(inet4);
use IO::Select;
use IO::Socket::INET;
use Net::hostent;
use POSIX ();
use Getopt::Long;
use FindBin;
use Time::HiRes qw( sleep usleep gettimeofday tv_interval );
use Errno qw( EAGAIN EWOULDBLOCK );

my $maxbuffer = 1024*1024;

my $option_debug = 0;
my $option_local = "localhost:1143";
my $option_remote;
my $option_ssl = 0;
my $option_kill;
my $option_timeout = 3600;
my $option_statfile;

my $pidfile;
my $uid = $<;
my $un = (getpwuid($<))[0];
if ($uid)
{
    $pidfile = "/tmp/".$FindBin::Script.".$un.pid";
}
else
{
    $pidfile = "/var/run/".$FindBin::Script.".pid";
}

my %datatomua;
my %datatoimap;
my %sessionactive;
my %muanum;
my %imapnum;
my %nummua;
my %numimap;
my %muaclose;
my %imapclose;
my %stattime;
my %starttime;
my %statread;
my %statwrite;
my %laststatread;
my %laststatwrite;

my $connection = 0;

# these need to be perl regexps matching the IMAP folders to omit
my @omit = ("INBOX\.archive.*", "archive");

STDOUT->autoflush(1);
STDERR->autoflush(1);

sub Syntax
{
    print STDERR <<STOP;

Usage: $FindBin::Script [options] OMITREGEXP ...

Options:
  -s, --ssl                   Use SSL for remote server
  -l, --local ADDR:[PORT]     Use ADDR:PORT to listen on
  -r, --remote ADDR:[PORT]    Use ADDR:PORT as remote server
  -t, --timeout SECS          Use SECS as timeout
  -f, --statfile FILE         Write stats to FILE
  -d, --debug                 Do not fork and print debugging
  -k, --kill                  Kill existing instance of daemon
  -h, --help                  Print this message

OMITREGEXP is a perl regexp matching a mailbox to omit.
Put as many as you like on the command line, but remember
quoting.

STOP
    return;
}

sub ParseOptions
{
    if (!GetOptions (
             "help|h" => sub { Syntax(); exit(0); },
             "ssl|s" => \$option_ssl,
             "local|l=s" => \$option_local,
             "remote|r=s" => \$option_remote,
	     "timeout|t=i" => \$option_timeout,
	     "statfile|f=s" => \$option_statfile,
             "debug|d" => \$option_debug,
	     "kill|k" => \$option_kill
        ))
    {
        Syntax();
        die "Bad options";
    }

    die ("No local address given") unless (defined($option_local));
    die ("No remote address given") unless (defined($option_remote));
    $option_ssl = 1 if ($option_remote =~ /:993$/);

    @omit = @ARGV if ($#ARGV >= 0);
}

# Daemonize!
sub daemon () {
    sub _fork {
        if (defined (my $pid = fork)) { return $pid; }
        else { die "cannot fork: $!"; }
    }

    # fork and exit parent
    if (_fork) { exit 0; }

    # detach ourselves from the terminal
    POSIX::setsid or die "cannot detach from controlling terminal";

    # prevent possibility of acquiring a controlling terminal
    $SIG{'HUP'} = 'IGNORE';
    if (_fork) { exit 0; }

    # change working directory
    chdir "/";

    # clear file creation mask
    umask 0;

    # close open file descriptors
    foreach my $i (0..POSIX::sysconf(&POSIX::_SC_OPEN_MAX)) { POSIX::close $i; }

    # Reopen stderr, stdout, stdin to /dev/null
    open STDIN,  "+>/dev/null";
    open STDOUT, "| /usr/bin/logger -p user.notice";
    open STDERR, "+>&STDOUT";
    STDOUT->autoflush(1);
    STDERR->autoflush(1);
    $SIG{'INT'} = 'IGNORE';
    $SIG{'PIPE'} = 'IGNORE';
    $SIG{'CHLD'} = 'IGNORE';
    $SIG{'TERM'} = 'IGNORE';

    my $childpid;

    do
    {
        $SIG{'TERM'} = 'IGNORE';
        $childpid = _fork;

        # if we are the child, set signal handlers and return                                                                                                  
        if (!$childpid)
        {
            # wait until the parent has put our PID file in place                                                                                              
            Timer::HiRes::sleep (0.1) until (-r $pidfile);
            $SIG{'INT'} = 'IGNORE';
            $SIG{'PIPE'} = 'IGNORE';
            $SIG{'CHLD'} = 'IGNORE';
            $SIG{'TERM'} = sub { kill 9, getppid; unlink($pidfile); exit 0; };
            return;
        }

        $SIG{'TERM'} = sub { kill 15, $childpid; };
        # we are the watcher process                                                                                                                           
        open (my $pf, ">$pidfile") || die ("Cannot write to pidfile: $!");
        print $pf "$childpid\n";
        close $pf;

        # Loop whilst the child exists                                                                                                                         
        sleep 1 while (kill 0, $childpid);
    } while (-r $pidfile); # child unlinks PID on clean exit                                                                                                   
    $SIG{'TERM'} = 'IGNORE';
    exit 0;
}

sub KillExisting
{
    while ( -r $pidfile )
    {
        open (my $pf, "<$pidfile") || die ("Cannot open $pidfile: $!");
        my $pid = <$pf>;
        chomp ($pid);
        close ($pid);
        unless (($pid=~/^\d+$/) && (kill 0, $pid))
        {
            print STDERR "$FindBin::Script removing stale PID file\n";
            # PID file is stale                                                                                                                                
            unlink ($pidfile);
            return;
        }
        # up to child to delete pidfile;                                                                                                                       
        kill 15, $pid;
        # wait for the existing PID to exit, and also its parent                                                                                               
        my $i;
        for ($i=100; $i && (kill 0, $pid); $i--)
        {
	    Time::HiRes::sleep (0.1);
        }
        return if ($i);
        print STDERR "$FindBin::Script could not kill old daemon nicely, playing hardball\n";
        kill 9, $pid unless ($i);
        for ($i=100; $i && (kill 0, $pid); $i--)
        {
	    Time::HiRes::sleep (0.1);
        }
        sleep(1);
    }
}

sub CloseConnection
{
    my $mc = shift @_;
    my $muafd = $nummua{$mc};
    my $imapfd = $numimap{$mc};
    printf "$FindBin::Script [%d] closing connection\n", $mc if ($option_debug);
    $muafd->close() if (defined($muafd));
    $imapfd->close() if (defined($imapfd));
    delete $datatomua{$mc};
    delete $datatoimap{$mc};
    delete $sessionactive{$mc};
    delete $muaclose{$mc};
    delete $imapclose{$mc};
    delete $nummua{$mc};
    delete $numimap{$mc};
    delete $stattime{$mc};
    delete $starttime{$mc};
    delete $statread{$mc};
    delete $statwrite{$mc};
    delete $laststatread{$mc};
    delete $laststatwrite{$mc};
    delete $muanum{$muafd} if (defined($muafd));
    delete $imapnum{$imapfd} if (defined($imapfd));
    $imapfd = undef;
    $muafd = undef;
}

sub MarkActive
{
    my $mc = shift @_;
    $sessionactive{$mc} = [gettimeofday];
}

ParseOptions;

KillExisting unless $option_debug;
exit 0 if ($option_kill);

daemon unless $option_debug;

my $inbound = new IO::Socket::INET(LocalHost => $option_local,
                                   Listen => 50,
                                   ReuseAddr => 1);
die "cannot open proxy socket on $option_local - not root?" unless $inbound;
print "$FindBin::Script [*] listening on $option_local\n" if $option_debug;

my $laststat = [gettimeofday];

while (1)
{
    my $readable;
    my $writeable;
    my $exceptions;
    my $mc;
    my $fd;
    
    my $selectread = IO::Select->new($inbound);
    my $selectwrite = IO::Select->new();
    foreach $mc (keys %sessionactive)
    {
	my $muafd = $nummua{$mc};
	my $imapfd = $numimap{$mc};
	if (defined($datatomua{$mc}) &&
	    (length($datatomua{$mc})>0) &&
	    ($datatomua{$mc} =~ m/\r\n/m)
	    )
	{
	    $selectwrite->add($muafd);
	}
	if (defined($datatoimap{$mc}) && (length($datatoimap{$mc})>0))
	{
	    $selectwrite->add($imapfd);
	}
	unless (defined($muaclose{$mc}) || (defined($datatoimap{$mc}) && (length($datatoimap{$mc}) > $maxbuffer)))
	{
	    $selectread->add($muafd);
	}
	unless (defined($imapclose{$mc}) || (defined($datatomua{$mc}) && (length($datatomua{$mc}) > $maxbuffer) && (($datatomua{$mc} =~ m/\r\n/m)) ))
	{
	    $selectread->add($imapfd);
	}
    }

    ($readable, $writeable) = IO::Select->select ($selectread, $selectwrite, undef, 1);

    foreach $fd (@$readable)
    {
        if ($fd == $inbound)
	{
	    # a MUA is opening a new connection to us, open relay to server

            my $muafd = $inbound->accept;
	    $mc = $connection++;
            printf "$FindBin::Script [%d] connected to MUA\n",$mc if $option_debug;

            my $imapfd = $option_ssl?(new IO::Socket::SSL($option_remote)):(new IO::Socket::INET($option_remote));
	    
            unless (defined $imapfd)
	    {
                $muafd->close;
                printf "$FindBin::Script [%d] cannot connect to $option_remote: $!\n", $mc if $option_debug;
            }
	    else
	    {
		$muafd->blocking(0);
		$imapfd->blocking(0);
		$nummua{$mc} = $muafd;
		$numimap{$mc} = $imapfd;
		$mc = $mc;
		$muanum{$muafd}= $mc;
		$imapnum{$imapfd}= $mc;
		$datatomua{$mc}="";
		$datatoimap{$mc}="";
		$stattime{$mc} = [gettimeofday];
		$starttime{$mc} = $stattime{$mc};
		$statread{$mc} = 0;
		$statwrite{$mc} = 0;
		$laststatread{$mc} = 0;
		$laststatwrite{$mc} = 0;
		delete $sessionactive{$mc};
		delete $muaclose{$mc};
		delete $imapclose{$mc};
		MarkActive($mc);
                printf "$FindBin::Script [%d] connected to $option_remote using %s\n", $mc, $option_ssl?"ssl":"raw" if $option_debug;
            }
        }
        elsif ($fd and exists $muanum{$fd})
	{
	    # the MUA is sending something to the IMAP server, read the data
	    my $mc = $muanum{$fd};
	    my $muafd = $nummua{$mc};
	    my $imapfd = $numimap{$mc};
	    my $data;
	    my $result = sysread $muafd, $data, 8192;
	    if (!defined($result))
	    {
		if (($! != EAGAIN) && ($! != EWOULDBLOCK))
		{
		    printf "$FindBin::Script [%d] mua sysread $!\n", $mc if $option_debug;
		    CloseConnection($fd);
		}
	    }
	    elsif ($result == 0)
	    {
		$muaclose{$mc} = 1;
	    }
	    else
	    {
		$datatoimap{$mc}.=$data;
		MarkActive($mc);
	    }
	}
        elsif ($fd and exists $imapnum{$fd})
	{
	    # the IMAP server is sending something to the MUA, read the data
	    my $mc = $imapnum{$fd};
	    my $muafd = $nummua{$mc};
	    my $imapfd = $numimap{$mc};
	    my $data;
	    my $result = sysread $imapfd, $data, 8192;
	    if (!defined($result))
	    {
		if (($! != EAGAIN) && ($! != EWOULDBLOCK))
		{
		    printf "$FindBin::Script [%d] imap sysread $!\n", $mc if $option_debug;
		    CloseConnection($fd);
		}
	    }
	    elsif ($result == 0)
	    {
		$imapclose{$mc} = 1;
	    }
	    else
	    {
		$datatomua{$mc}.=$data;
		MarkActive($mc);
	    }
	}
    }

    foreach $fd (@$writeable)
    {
	if ($fd and exists $muanum{$fd})
	{
	    # the MUA connection is writeable
	    my $mc = $muanum{$fd};
	    my $muafd = $nummua{$mc};
	    my $imapfd = $numimap{$mc};

	    if ($datatomua{$mc} !~ /\r\n/)
	    {
		printf "$FindBin::Script [%d] Internal logic error - no break\n", $mc if $option_debug;
		next;
	    }

	    # Replace data to write by the bit (if anything) after the final \r\n
	    my $d1=$datatomua{$mc};
	    $datatomua{$mc} =~ s/^(.*\r\n)(.*)$/$2/s;
	    my $d2=$datatomua{$mc};
	    my $towrite=$1;

	    if (!defined($towrite) || ($towrite eq ""))
	    {
		printf "$FindBin::Script [%d] Internal logic error - could not get write string\nD1=<<<%s>>>\nD2=<<<%s>>>\nTW=<<<%s>>>", $mc, $d1, $d2, defined($towrite)?$towrite:'undef' if $option_debug;
		next;
	    }

	    foreach my $pattern (@omit)
	    {
		$towrite =~
		    s/^\* LIST (\([^)]*\))? "[^"]" "?$pattern[^\r\n]*"?\r\n//gm;
	    }
	    
	    my $result = syswrite $muafd, $towrite;
	    if (!defined($result))
	    {
		# restore unwritten data to write
		$datatomua{$mc} = $towrite.$datatomua{$mc};
		if (($! != EAGAIN) && ($! != EWOULDBLOCK))
		{
		    printf "$FindBin::Script [%d] mua syswrite $!\n", $mc if $option_debug;
		    CloseConnection($fd);
		}
	    }
	    else
	    {
		$statread{$mc}+=$result;
		if ($result != length($towrite))
		{
		    # restore partially written data
		    $datatomua{$mc} = substr($towrite, $result).$datatomua{$mc};
		}
		MarkActive($mc);
	    }
	}
        elsif ($fd and exists $imapnum{$fd})
	{
	    # the IMAP connection is writeable
	    my $mc = $imapnum{$fd};
	    my $muafd = $nummua{$mc};
	    my $imapfd = $numimap{$mc};
	    my $result = syswrite $imapfd, $datatoimap{$mc};
	    if (!defined($result))
	    {
		if (($! != EAGAIN) && ($! != EWOULDBLOCK))
		{
		    printf "$FindBin::Script [%d] imap syswrite $!\n", $mc if $option_debug;
		    CloseConnection($fd);
		}
	    }
	    else
	    {
		$statwrite{$mc}+=$result;
		if ($result == length($datatoimap{$mc}))
		{
		    $datatoimap{$mc} = "";
		}
		else
		{
		    $datatoimap{$mc} = substr($datatoimap{$mc}, $result);
		}
		MarkActive($mc);
	    }
	}

    }

    my $now = [gettimeofday];
    my $statfile;
    if (defined($option_statfile) && (tv_interval($laststat, $now) > 5))
    {
	open ($statfile, ">", $option_statfile.".new") 
    }
    foreach $mc (keys %sessionactive)
    {
	if ( (!defined($datatomua{$mc}) || length($datatomua{$mc})==0) &&
	     (!defined($datatoimap{$mc}) || length($datatoimap{$mc})==0) &&
	     (defined($muaclose{$mc}) || defined($imapclose{$mc}))
	     )
	{
            printf "$FindBin::Script [%d] closing connection MUA=%d, IMAP=%d\n",
	    $mc,
	    defined($muaclose{$mc})?1:0,
	    defined($imapclose{$mc})?1:0
		if $option_debug;
	    CloseConnection($mc);
	    next;
	}

	my $running = tv_interval($starttime{$mc}, $now);
	$running = 0.001 if ($running < 0.001);

	my $statinterval = tv_interval($laststat, $now);
	$statinterval = 0.001 if ($statinterval < 0.001);

	if (defined($statfile))
	{
	    printf $statfile "$FindBin::Script [%d] read=%d write=%d rbuf=%d wbuf=%d rbps=%d wbps=%d ival=%d\n", $mc, $statread{$mc}, $statwrite{$mc}, length($datatomua{$mc}), length($datatoimap{$mc}), ($statread{$mc}-$laststatread{$mc})/$statinterval, ($statwrite{$mc}-$laststatwrite{$mc})/$statinterval, $statinterval;
	    $laststatread{$mc} = $statread{$mc};
	    $laststatwrite{$mc} = $statwrite{$mc};
	}

	my $interval = tv_interval($stattime{$mc}, $now);
	if (($interval > 5) && $option_debug)
	{
	    $stattime{$mc} = $now;
	    printf "$FindBin::Script [%d] read=%d write=%d rbuf=%d wbuf=%d rbps=%d wbps=%d\n", $mc, $statread{$mc}, $statwrite{$mc}, length($datatomua{$mc}), length($datatoimap{$mc}), $statread{$mc}/$running, $statwrite{$mc}/$running;
	}

	$interval = tv_interval($sessionactive{$mc}, $now);
	if ($interval > $option_timeout)
	{
	    printf "$FindBin::Script [%d] closing connection as idle for %d seconds\n", $mc, $interval if $option_debug;
	    CloseConnection($mc);
	    next;
	}
    }

    if (defined($statfile))
    {
	close ($statfile);
	rename ($option_statfile.".new", $option_statfile);
	$laststat = $now;
    }
}
$inbound->close;
die "$FindBin::Script terminated (should never happen)";
