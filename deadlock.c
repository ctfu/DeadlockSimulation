/*******************************************************************/
/* Chuntao Fu                                                      */
/* Last Modified: 04/12/2015                                       */
/* This program is a program that similates the deadlock detections*/
/* with limited numbers of total process and limited numbers of    */
/* types of resources. Eeach type of resource will only have one   */
/* one instance.                                                   */
/*******************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXSTEP 25	/* max action steps for any process */
#define MAXPROC 10	/* max processes in any simulation */
#define MAXRSRC 20	/* max resources in any simulation */

FILE *f;		/* input stream */


/*-----------------------------------------------------------------*/
/* There are several arrays used to record information about the   */
/* processes and the resources. Since process IDs and resoure IDs  */
/* start with 1, the 0th entry in each array is unused. That is,   */
/* many arrays are treated as if they are 1-origin arrays, and not */
/* 0-origin arrays. This makes the code easier to understand at    */
/* the cost of one array entry.                                    */
/*-----------------------------------------------------------------*/

/*------------------------------------------------------------------*/
/* This is an array of structures with one entry for every process. */
/* Each entry contains the "program" that will be executed by the   */
/* process (ns, a, and n), the index in the a and n arrays of the   */
/* next action to be taken, the state of the process, the total     */
/* time used by the process, and the time when it ended.            */
/*------------------------------------------------------------------*/
struct process {
    int ns;		/* # of action pairs for this process */
    int a[MAXSTEP];	/* actions */
    int n[MAXSTEP];	/* parameters (resource ID or time) */
    int ip;		/* index to next action */
    int state;		/* process state */
    			    /* -1 = finished */
    			    /* 0 = ready (or running) */
    			    /* 1..nr = blocked, waiting on resource */
    int runtime;	/* time used */
    int endtime;	/* time process ended */
} proc[MAXPROC+1];

int trace;		/* trace option value */

int simno;		/* simulation number */
int t;			/* simulation time */
int np;			/* total # of processes (1..MAXPROC) */
int nr;			/* total # of resources (1..MAXRSRC) */

int crstate[MAXRSRC+1]; //store a copy of the resources state
struct states{  
    int state;
}cproc[MAXPROC+1];      //store a copy of each process state

/*--------------------------------------------------------------------*/
/* The following two items represent a very simple queue that records */
/* the "ready" processes (actually, the indices in the "proc" array   */
/* of the ready processes). The number of entries in the queue is     */
/* nready. If nready > 0, then the first entry in the queue is in     */
/* ready[0], and the last entry is in ready[nready-1]. This could be  */
/* made a lot "swifter" with dynamic allocation (i.e. using a linked  */
/* list for the queue), but in this case, we're not so concerned with */
/* the efficiency of the solution.                                    */
/*--------------------------------------------------------------------*/
int nready;		/* # of ready processes (0..np) */
int ready[MAXPROC];	/* the ready queue (each in 1..np) */


int running;		/* ID of the running process (1..np) */

/*------------------------------------------------------------------*/
/* The next three arrays are used to record information about the   */
/* resources. rstate[r] is 0 if resource r is not being used. If    */
/* resource r is being used by process p, then rstate[r] = p.       */
/* If there are any processes waiting for the resource, then their  */
/* process IDs will appear on a queue associated with the resource  */
/* being awaited. For example, suppose process 3 "owns" resource 4, */
/* and processes 1 and 2 (in that order) have attempted to gain     */
/* mutually-exclusive access to the resource. We'd then have this:  */
/*	rstate[4] = 3		process 3 owns resource 4           */
/*	nrw[4] = 2		2 procs are waiting for resource 4  */
/*	rw[4][0] = 1		process 1 is first waiting proc     */
/*	rw[4][1] = 2		process 2 is second waiting proc    */
/*------------------------------------------------------------------*/
int rstate[MAXRSRC+1];	/* resource state */
			    /* 0 = unused */
			    /* 1..np = owned by process */
int rw[MAXRSRC+1][MAXPROC+1];	/* queues of waiting processes */
int nrw[MAXRSRC+1];		/* # of procs on each queue */

/*-------------------------------------------------------*/
/* Get the next simulation and return 1; return 0 at end */
/*-------------------------------------------------------*/
/* XXX This could be modified to detect input errors.    */
/* XXX But the problem statement guarantees that student */
/* XXX solutions will not need to deal with errors. It   */
/* XXX is still appropriate to include such tests so     */
/* XXX additional test data cases can be validated.      */
/*-------------------------------------------------------*/
int getinput(void)
{
    int i, j;

    fscanf(f,"%d%d",&np,&nr);		/* # processes, # resources */
    if (np == 0 && nr== 0) return 0;	/* end of input */

    for (i=1;i<=np;i++) {		/* get data for processes 1 ... np */
	fscanf(f,"%d",&proc[i].ns);	/* # of steps for process i */
	for (j=0;j<proc[i].ns;j++) {
	    fscanf(f,"%d",&proc[i].a[j]);	    /* action for step j */
	    fscanf(f,"%d",&proc[i].n[j]);	    /* parameter for step j */
	}
    }
    return 1;
}

/*-------------------------------------------------------------------*/
/* Deadlock detection algorithm.                                     */
/* See if deadlock exists in the current state.                      */
/* If deadlock is detected, display the appropriate information (the */
/* processes and resources involved) and return 1.                   */
/* If deadlock is not detected, return 0.                            */
/*-------------------------------------------------------------------*/
int deadlock(void)
{
    struct graph{
        int e;   // the index of the node's edge
        int v;   // variable to check if the node has been visited
    }node[MAXPROC + MAXRSRC + 1];   //a graph node for resources allocation graph

    int i, j, k, flag, index;
    
    for(i = 1; i <= np; i++){   //initialize the copy of each
        cproc[i].state = 0;     //process state to 0
    }

    for(i = 1; i <= nr; i++){   //initialize the copy of each resource state to 0
        crstate[i] = 0;
    }

    /*The algorithm to build a resources graph*/
    for(i = 1; i <= np + nr; i++){
        if(i <= np){    //build the graph node for each of the process
            if(cproc[i].state != proc[i].state){    //if any process state changes
                if(proc[i].state > 0){  //if the process is blocked waiting for any resource
                    cproc[i].state = proc[i].state;
                    node[i].e = proc[i].state;  //set the process edge pints to its
                    node[i].v = 0;              //waiting resources
                }else if(proc[i].state == -1){ //if the process has been termininated
                    cproc[i].state = proc[i].state;
                    node[i].e = 0;
                    node[i].v = 0;
                }else if(proc[i].state == 0){ //if the process is unblocked
                    cproc[i].state = proc[i].state;
                    node[i].e = 0;
                    node[i].v = 0;
                }
            }else{          //no changes to the process state
                node[i].e = 0;
                node[i].v = 0;
            }
        }else{      //build the graph node for each of the resources
            if(crstate[i-np] != rstate[i-np]){  //if any resources state changes
                if(rstate[i-np] != 0){  //if the resource is allocated by a process
                    crstate[i-np] = rstate[i-np];
                    node[i].e = rstate[i-np];   //set the resource edge points to its
                    node[i].v = 0;              //owner process
                }else{  //if the resource is released
                    crstate[i-np] = rstate[i-np];
                    node[i].e = 0;
                    node[i].v = 0;
                }
            }else{      //no changes to the resource state
                node[i].e = 0;
                node[i].v = 0;
            }
        }
    }

    /*The algorithm for cycle detection within the resources graph*/
    /*set the node[i].v to 1 if the node has been visited when.   */
    /*If the node has been visited twice, then there is a cycle.  */

    for(i = 1; i <= np + nr; i++){
        index = i;
        flag = 0;
        while(!flag){
            if(node[index].e != 0){ //if the node has edge?
                if(node[index].v == 1){     //if the node has been visited? if true, deadlock
                    printf("Deadlock detected at time %d involving...\n", t);
                    printf("\tprocesses: ");
                    for(j = 1; j <= np; j++){   //print the correlative processes
                        for(k = 1; k <= nr; k++){
                            if(node[j].v == 1 && rstate[k] == j){
                                 printf("%d ", j);
                             }
                        }
                    }
                    printf("\n\tresources: ");  //printf the correlative resources
                    for(j = 1; j <= np; j++){
                        for(k = 1; k <= nr; k++){
                             if(node[j].v == 1 && rstate[k] == j){
                                 printf("%d ", node[j].e);
                             }
                        }
                    }

                    putchar('\n');

                    return 1;

                }else{      //if the node has not been visited, set v to 1
                    node[index].v = 1;
                }
                if(index <= np){    //search through the edges of each node
                    index = node[index].e + np;
                }else{
                    index = node[index].e;
                }
            }else{  // if the node has no edge, then set the previous v back to 0
                index = i;
                while(!flag){
                    if(node[index].e != 0){
                        if(node[index].v != 0){
                            node[index].v = 0;
                        }
                        if(index <= np){
                            index = node[index].e + np;
                        }else{
                            index = node[index].e;
                        }
                    }else{
                        flag = 1;   //set flag to 1 to stop searching when the node
                    }               //is visiting has no edge
                }
            }
        }
    }

     return 0;
}

/*-----------------------------------------------------*/
/* Add process p (1..np) to the end of the ready queue */
/*-----------------------------------------------------*/
void makeready(int p)
{
    ready[nready++] = p;	/* stash process ID, increment queue length */
}

/*--------------------------------------------------*/
/* Add process p (1..np) to the end of the queue of */
/* processes waiting on resource r (1..nr)          */
/*--------------------------------------------------*/
void makewait(int p, int r)
{
    rw[r][nrw[r]] = p;		/* place the process ID in the right place */
    nrw[r]++;			/* increment the queue length */
}

int main(int argc, char *argv[])
{
    int i, ip, a, n;
    int dd;				/* non-zero if deadlock detected */

    while (argc > 1 && argv[1][0] == '-') {	/* check for -v option (and others?) */
	if (!strcmp(argv[1],"-v")) {
	    trace++;
	    argc--;
	    argv++;
	    continue;
	}
	fprintf(stderr,"Unknown option %s\n", argv[1]);
	exit(1);
    }

    /*--------------------------------------------------*/
    /* Verify correct number of command line arguments. */
    /*--------------------------------------------------*/
    if (argc > 2) {
	fprintf(stderr,"Usage: prog2 [-v] [inputfilename]\n");
	exit(1);
    }

    /*----------------------------------------------*/
    /* Associate appropriate input stream with 'f'. */
    /* Diagnose failure to open input file, if any. */
    /*----------------------------------------------*/
    if (argc == 2) {
	f = fopen(argv[1],"r");
	if (f == NULL) {
	    fprintf(stderr,"Cannot open %s for input.\n", argv[1]);
	    exit(1);
	}
    } else 
	f = stdin;

    /*----------------------------------------*/
    /* Read and process the input data cases. */
    /*----------------------------------------*/
    for (simno=1;;simno++) {
	if (!getinput()) break;		/* get the next set of input data */
	t = 0;				/* set simulation time */

	for (i=1;i<=np;i++) {		/* initialize each process */
	    proc[i].ip = 0;		    /* first action index */
	    proc[i].state = 0;		    /* process state is ready */
	    proc[i].runtime = 0;	    /* no time used yet */
	    ready[i-1] = i;		    /* setup initial ready queue */
	}
	nready = np;

	for (i=1;i<=nr;i++) {		/* initialize each resource */
	    rstate[i] = 0;		    /* unused */
	    nrw[i] = 0;			    /* no waiting processes */
	}

	printf("Simulation %d\n", simno);

	for(;;) {
	    dd = deadlock();		/* check for deadlock */
	    if (dd) break;		/* if it was detected */

	    /*---------------------------------------------*/
	    /* Get a process from the ready queue to run.  */
	    /* If there are no ready processes, we must be */
	    /* done or deadlocked.                         */
	    /*---------------------------------------------*/
	    if (nready == 0) break;		/* no ready processes */
	    running = ready[0];			/* first ready process */
	    for (i=1;i<nready;i++)		/* slow queue removal, */
		ready[i-1] = ready[i];		/* but who cares? */
	    nready--;

	    /*--------------------------------------*/
	    /* Get ip, a, and n for running process */
	    /*--------------------------------------*/
	    ip = proc[running].ip;		/* the "program counter" */
	    a = proc[running].a[ip];		/* what action to perform */
	    n = proc[running].n[ip];		/* parameter for the action */

	    if (trace) {			/* optional trace - not required */
		printf("%d: ", t);
		printf("process %d: ", running);
		printf("(%d,%d)\n", a, n);
	    }

	    /*--------------------------------------------*/
	    /* If the process is requesting a resource... */
	    /*--------------------------------------------*/
	    if (a == 1) {
		/*------------------------------*/
		/* If the resource is available */
		/*------------------------------*/
		if (rstate[n] == 0) {
            rstate[n] = running;    //resource is owned by running process
            if(trace) {
                printf("\t(resource %d allocated)\n", n);
            }
            proc[running].ip++;
            makeready(running);
            t++;
            proc[running].runtime++;


		/*-----------------------------------*/
		/* If the resource is not available. */
		/* Time does NOT increase here!      */
		/*-----------------------------------*/
		} else {
		    if (trace) printf("\t(resource %d unavailable)\n", n);
		    makewait(running,n);		/* add to waiters */
		    proc[running].state = n;		/* mark proc blocked, waiting for n */
		}
	    }

	    /*-------------------------------------------*/
	    /* If the process is releasing a resource... */
	    /*-------------------------------------------*/
	    else if (a == 2) {
            rstate[n] = 0;  //releasing resource n
            if(trace){
                printf("\t(resource %d released)\n", n);
            }
            if(nrw[n] != 0){
                proc[rw[n][0]].state = 0;
                makeready(rw[n][0]);
                if(trace){
                    printf("\t(process %d unblocked)\n", rw[n][0]);
                }
                for(i =1; i<= nrw[n]; i++){
                    rw[n][i-1] = rw[n][i];
                    nrw[n]--;
                }
            }
            if(ip+1 == proc[running].ns){
                proc[running].state = -1;
                proc[running].endtime = t;
                if(trace){
                    printf("\t(process %d terminated)\n", running);
                }
            }else{
                proc[running].ip++;
                makeready(running);
            }
            
            t++;
            proc[running].runtime++;
	    }

	    /*----------------------------------*/
	    /* If the process is "computing"... */
	    /*----------------------------------*/
	    else if (a == 3) {
		n--;			/* reduce remaining computation time */
		if (n == 0) {		/* done with this action? */
		    if (ip+1 == proc[running].ns) {
			proc[running].state = -1;		/* done */
			proc[running].endtime = t;		/* end time */
			if (trace) printf("\t(process %d terminated)\n",
			    running);
		    } else {
			proc[running].ip++;
			makeready(running);
		    }
		} else {		/* process has more computation to do */
		    proc[running].n[ip] = n;
		    makeready(running);
		}
		t++;
		proc[running].runtime++;
	    }

	    /*----------------------------------------------------------*/
	    /* This point should never be reached if the data is valid. */
	    /*----------------------------------------------------------*/
	    else {
		fprintf(stderr,"Bad action (%d)\n", a);
		exit(1);
	    }
	}

	if (!dd) {
	    /*----------------*/
	    /* If no deadlock */
	    /*----------------*/
	    printf("All processes successfully terminated.\n");
	    for (i=1;i<=np;i++) {
		printf("Process %d: run time = %d, ended at %d\n",
		    i, proc[i].runtime, proc[i].endtime);
	    }
	}

	putchar('\n');
    }
}
