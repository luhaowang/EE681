/**CFile****************************************************************



***********************************************************************/


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#include <stdio.h>

#include "base/abc/abc.h"
#include "base/main/mainInt.h"
#include "proof/fraig/fraig.h"
#include "opt/fxu/fxu.h"
#include "opt/cut/cut.h"
#include "map/fpga/fpga.h"
#include "map/if/if.h"
#include "opt/res/res.h"
#include "opt/lpk/lpk.h"
#include "aig/aig/aig.h"
#include "opt/dar/dar.h"

static int Abc_CommandNewCommand     ( Abc_Frame_t * pAbc, int argc, char ** argv );
static Abc_Ntk_t * My_Command_Associative(Abc_Ntk_t * pNtk);
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void newcommand_Init( Abc_Frame_t * pAbc )
{
	Cmd_CommandAdd( pAbc, "Synthesis",    "newcommand",    Abc_CommandNewCommand,       0 );

} 

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void newcommand_End( Abc_Frame_t * pAbc )
{


}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

Abc_Ntk_t * My_Command_Associative(Abc_Ntk_t * pNtk)
{// check abc.h and abcNtk.c(Abc_ntkDup, duplication) freeXXX
	//a new network to return
  printf("inside the My_Command_Associative\n");
	Abc_Ntk_t * new_pNtk;
	Abc_Obj_t * pObj;

	int i, j,k,m;
  int changed = 0;
	//check partial nodes satisfying a certain associative law
	Abc_NtkForEachObj( pNtk, pObj, i)
	{
        //printf("Node ID: %d \n", Abc_ObjId(pObj));
        //printf("FanInNum: %d \n",Abc_ObjFaninNum(pObj));

        if(changed <1 && Abc_ObjFaninNum(pObj) == 2 )
        {
            Abc_Obj_t * pFanin_0 = Abc_ObjFanin0(pObj);
            Abc_Obj_t * pFanin_1 = Abc_ObjFanin1(pObj);
            if(changed <1 && Abc_ObjFaninNum(pFanin_0) == 2 ) // x*(y*z) => (x*y)*z
            {
               //printf("2nd Condition, Node ID: %d\n",Abc_ObjId(pObj) );
               Abc_Obj_t * tempObj;
               Abc_Obj_t * pFanin_0_0 = Abc_ObjFanin0(pFanin_0);
               Abc_Obj_t * pFanin_0_1 = Abc_ObjFanin1(pFanin_0);

               Abc_Obj_t * NewParentNode = Abc_NtkDupObj(pNtk, pObj, 1);
               Abc_Obj_t * NewChildNode = Abc_NtkDupObj(pNtk, pFanin_0, 1);

               int FanoutNum = Abc_ObjFanoutNum(pObj);

               for (j=0; j<FanoutNum; j++)
               {
                tempObj = Abc_ObjFanout(pObj, 0);
                printf("Deleting FandIn %d of %d\n",Abc_ObjId(tempObj),Abc_ObjId(pObj) );
                Abc_ObjDeleteFanin( tempObj , pObj );
                Abc_ObjAddFanin( tempObj, NewParentNode);
               }
               Abc_ObjAddFanin(NewParentNode,pFanin_0_0 );
               NewParentNode->fCompl0 = pFanin_0->fCompl0;
               Abc_ObjAddFanin( NewParentNode, NewChildNode );
               Abc_ObjAddFanin( NewChildNode, pFanin_0_1);
               NewChildNode->fCompl0 = pFanin_0->fCompl1;
               Abc_ObjAddFanin(NewChildNode,pFanin_1 );
               NewChildNode->fCompl1 = pObj->fCompl1;
               

               if(Abc_ObjFanoutNum(pFanin_0)>1)
               {
               		printf("Abc_ObjFanoutNum(pFanin_1) > 1\n" );
               }
               else
               {
               	 Abc_ObjForEachFanin(pFanin_0,tempObj, k )
	               {
	                	Abc_ObjDeleteFanin(pFanin_0,tempObj);
	               }                 
	               Abc_NtkDeleteObj(pFanin_0);      	
               }
	
               Abc_ObjForEachFanin(pObj,tempObj, k )
               {
                	Abc_ObjDeleteFanin(pObj,tempObj);
               }  
               Abc_NtkDeleteObj(pObj);
               changed++;
            }
        }
	}
	new_pNtk = pNtk;
	return new_pNtk;
}

Abc_Ntk_t * My_Command_Distributive(Abc_Ntk_t * pNtk)
{
    printf("inside the My_Command_Distributive\n");
    Abc_Ntk_t * new_pNtk;
    Abc_Obj_t * pObj;
    Abc_Obj_t * pObj_x;
    Abc_Obj_t * pObj_y;
    Abc_Obj_t * pObj_z;
    Abc_Obj_t * pFanin_t1;
    Abc_Obj_t * pFanin_t2;


    int i, j,k,m;
    int same_node_ID = -1;
    int changed = 0;
    //check partial nodes satisfying a certain associative law
    Abc_NtkForEachObj( pNtk, pObj, i)
    {
        if(changed < 1 && Abc_ObjFaninNum(pObj) == 2 && Abc_ObjFaninC0(pObj) && Abc_ObjFaninC1(pObj) )
        {
            Abc_Obj_t * pFanin_0 = Abc_ObjFanin0(pObj);
            Abc_Obj_t * pFanin_1 = Abc_ObjFanin1(pObj);
            if(changed < 1 && Abc_ObjFaninNum(pFanin_0) == 2 && !Abc_ObjFaninC0(pFanin_0) && !Abc_ObjFaninC1(pFanin_0) )
            {
                //printf("Fandin_0 of Node(%d) is Node(%d) \n", Abc_ObjId(pObj),Abc_ObjId(pFanin_0));
                if(changed ==0 && Abc_ObjFaninNum(pFanin_1) == 2 && !Abc_ObjFaninC0(pFanin_1) && !Abc_ObjFaninC1(pFanin_1) )
                {
                    //printf("Fandin_1 of Node(%d) is Node(%d) \n", Abc_ObjId(pObj),Abc_ObjId(pFanin_1));
                    Abc_ObjForEachFanin( pFanin_0, pFanin_t1, k )
                    {
                        Abc_ObjForEachFanin(pFanin_1, pFanin_t2, m)
                        {
                            if(Abc_ObjId(pFanin_t1) == Abc_ObjId(pFanin_t2) )
                            {
                                same_node_ID = Abc_ObjId(pFanin_t1);
                                pObj_x = pFanin_t1;
                            }
                        }
                    }
                }
            }
            //printf("Same Node ID: %d\n", same_node_ID);
            if(same_node_ID != -1)
            {
                Abc_ObjForEachFanin( pFanin_0, pFanin_t1, k )
                {
                    if(Abc_ObjId(pFanin_t1) != same_node_ID)
                    {
                    	//printf("Fanin of pFanin_0: %d \n",Abc_ObjId(pFanin_t1));
                        pObj_y = pFanin_t1;
                    }

                }
                Abc_ObjForEachFanin( pFanin_1, pFanin_t2, m )
                {
                    if(Abc_ObjId(pFanin_t2) != same_node_ID)
                    {
                    	//printf("Fanin of pFanin_1: %d \n",Abc_ObjId(pFanin_t2));
                        pObj_z = pFanin_t2;
                    }
                }
                Abc_Obj_t * tempObj;
                Abc_Obj_t * tempObj_t1;
                Abc_Obj_t * NewParentNode = Abc_NtkDupObj(pNtk, pObj, 1);
                Abc_Obj_t * NewChildNode = Abc_NtkDupObj(pNtk, pFanin_1, 1);    
                int FanoutNum = Abc_ObjFanoutNum(pObj);

                for (j=0; j<FanoutNum; j++)
                {
                    tempObj = Abc_ObjFanout(pObj, 0);
                    Abc_ObjDeleteFanin( tempObj , pObj );
                    Abc_ObjAddFanin( tempObj, NewParentNode);
                }

                for (j=0; j<FanoutNum; j++)
                {
                	tempObj = Abc_ObjFanout(NewParentNode, j);
                	//printf("ParentNode Fanout is : %d\n",Abc_ObjId(tempObj) );
                	Abc_ObjForEachFanin(tempObj,tempObj_t1,k)
                	{
                		if(Abc_ObjId(tempObj_t1) == Abc_ObjId(NewParentNode) )
                		{
                			//printf("ParentNode Fanout's fanIn matched is : %d, k is : %d\n",Abc_ObjId(NewParentNode),k );
                			if(k==0) tempObj->fCompl0 = 1;
                			if(k==1) tempObj->fCompl1 = 1;
                		}

                	}
                }



                // begin to create and connect new network
                Abc_ObjAddFanin( NewParentNode, pObj_x );
                Abc_ObjAddFanin( NewParentNode, NewChildNode );
                NewParentNode->fCompl0 = 0;
                NewParentNode->fCompl1 = 1;
                // Abc_ObjForEachFanin(NewParentNode,tempObj,k)
                // {
                //     if(Abc_ObjId(tempObj) == Abc_ObjId(NewChildNode) )
                //     {
                //         if(k==0) NewParentNode->fCompl0 = 1;
                //         if(k==1) NewParentNode->fCompl1 = 1;
                //         if(k>1) printf("Error for the Fanin!\n");
                //     }
                // }
                Abc_ObjAddFanin( NewChildNode, pObj_y);
                Abc_ObjAddFanin(NewChildNode,pObj_z );
                NewChildNode->fCompl0 = 1;
                NewChildNode->fCompl1 = 1;
                Abc_ObjForEachFanin(pObj,tempObj, k )
                {
                	Abc_ObjDeleteFanin(pObj,tempObj);
                }
                Abc_ObjForEachFanin(pFanin_0,tempObj, k )
                {
                	Abc_ObjDeleteFanin(pFanin_0,tempObj);
                }
                Abc_ObjForEachFanin(pFanin_1,tempObj, k )
                {
                	Abc_ObjDeleteFanin(pFanin_1,tempObj);
                }
                Abc_NtkDeleteObj(pObj);
                Abc_NtkDeleteObj(pFanin_0);
                Abc_NtkDeleteObj(pFanin_1);
                changed++;
            }
        }
    }
    new_pNtk = pNtk;
    return new_pNtk;
}

int Abc_CommandNewCommand ( Abc_Frame_t * pAbc, int argc, char ** argv )
{// pAbc is current network
	FILE * pOut, *pErr;
	Abc_Ntk_t * pNtk, * pNtkRes;
	
	int c;
  int fAllNodes;
  int fRecord;
  int fCleanup;

  int limit= 50;  // Switch for controlling how many times each function runs
	int count;
	
	
	
	
	printf("New Command is running!\n");
	
	//acquire current network information
	pNtk = Abc_FrameReadNtk(pAbc);
	pOut = Abc_FrameReadOut(pAbc);
	pErr = Abc_FrameReadErr(pAbc);
	
	// set the defaults for possible future strash
    fAllNodes = 0;
    fCleanup  = 1;
    fRecord   = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "acrh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'a':
            fAllNodes ^= 1;
            break;
        case 'c':
            fCleanup ^= 1;
            break;
        case 'r':
            fRecord ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
	
	
	if ( pNtk == NULL)
	{//no network
		fprintf( Abc_FrameReadErr(pAbc), "Empty network.\n");
		return 1;
	}
	
	if(!(Abc_NtkIsStrash(pNtk)))
	{//not AIG data structure
		fprintf(pOut, "The circuit should be strashed. Strashing begins.\n");
		pNtkRes = Abc_NtkStrash( pNtk, fAllNodes, fCleanup, fRecord);
	
		if (pNtkRes == NULL)
		{
			fprintf(pErr, "Strashing has failed.\n");
			return 1;
		}
		
		//replace not AIG graph with new AIG
		Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
		//update network information after replacement 
		pNtk = Abc_FrameReadNtk(pAbc);
        pOut = Abc_FrameReadOut(pAbc);
        pErr = Abc_FrameReadErr(pAbc);
		
		//check new network
		if ( pNtk == NULL )
        {
            fprintf( Abc_FrameReadErr(pAbc), "Empty network.\n" );
            return 1;
        }
        if (!( Abc_NtkIsStrash(pNtk) ))
        {//fail again without knowing exact reasons
            fprintf( pOut, "The circuit should be strashed.\n" );
            return 1;
        }		
	}
	
	if (!( Abc_NtkHasAig(pNtk) ))
    {//not effective hashed AIG 
        fprintf( pOut, "The circuit should be in the AIG form.\n" );
        return 0;
    }
	for(count = 0;count < limit; count ++)
	{
		pNtk= My_Command_Associative(pNtk);
	}

	for(count = 0;count < limit; count ++)
	{
		pNtk = My_Command_Distributive(pNtk);
	}
	//replace not AIG graph with new AIG
	pNtkRes = pNtk;
	pNtkRes = Abc_NtkStrash( pNtkRes, fAllNodes, fCleanup, fRecord);
	Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
	pNtk = Abc_FrameReadNtk(pAbc);
    pOut = Abc_FrameReadOut(pAbc);
    pErr = Abc_FrameReadErr(pAbc);
	
	
	return 0;
	
usage:
    fprintf( pErr, "usage: newcommand [-acrh]\n" );
    fprintf( pErr, "\t       replace some gates in a given AIG. (If not a strashed AIG, we strash it. [-acr] are the options working for strashing.)\n" );
    fprintf( pErr, "\t-a    : toggles between using all nodes and DFS nodes [default = %s]\n", fAllNodes? "all": "DFS" );
    fprintf( pErr, "\t-c    : toggles cleanup to remove the dagling AIG nodes [default = %s]\n", fCleanup? "all": "DFS" );
    fprintf( pErr, "\t-r    : enables using the record of AIG subgraphs [default = %s]\n", fRecord? "yes": "no" );
    fprintf( pErr, "\t-h    : print the command usage\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


