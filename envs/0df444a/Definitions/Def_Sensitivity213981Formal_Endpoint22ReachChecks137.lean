-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks137
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks137
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:11.522233+00:00
-- url     : https://prove2.me/theorems/9ef002e0-00b2-48a1-82ef-7087b1fecf99
-- title:
--   Endpoint22 Reach Checks137 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks137 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1355root`, `ThreeBoundEndpoint22Reachable.t6_1355jobs0`, `ThreeBoundEndpoint22Reachable.t6_1355jobs`, `ThreeBoundEndpoint22Reachable.t6_1356root`, `ThreeBoundEndpoint22Reachable.t6_1356jobs0`, `ThreeBoundEndpoint22Reachable.t6_1356jobs`, `ThreeBoundEndpoint22Reachable.t6_1343jobs2`, `ThreeBoundEndpoint22Reachable.t6_1357root`, `ThreeBoundEndpoint22Reachable.t6_1357jobs0`, `ThreeBoundEndpoint22Reachable.t6_1357jobs`, `ThreeBoundEndpoint22Reachable.t6_1358root`, `ThreeBoundEndpoint22Reachable.t6_1358jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks137.lean, lines 1–715.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans081
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
open ThreeBoundEndpoint22Packed (tree)

def t6_1343root : Job := ⟨plan7578,[],none,⟨15,10,0⟩⟩
def t6_1343jobs0 : List Job := [⟨plan5935,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5935,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5935,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1343jobs1 : List Job := [⟨plan5935,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1343jobs2 : List Job := [⟨plan5935,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1343jobs : List Job := t6_1343jobs0++t6_1343jobs1++t6_1343jobs2




def t6_1344root : Job := ⟨plan7579,[],none,⟨15,10,0⟩⟩
def t6_1344jobs0 : List Job := [⟨plan7579,[],none,⟨15,10,0⟩⟩]

def t6_1344jobs : List Job := t6_1344jobs0




def t6_1345root : Job := ⟨plan7872,[],none,⟨15,15,0⟩⟩
def t6_1345jobs0 : List Job := [⟨plan7872,[],none,⟨15,15,0⟩⟩]

def t6_1345jobs : List Job := t6_1345jobs0




def t6_1346root : Job := ⟨plan7873,[],none,⟨15,15,0⟩⟩
def t6_1346jobs0 : List Job := [⟨plan7873,[],none,⟨15,15,0⟩⟩]

def t6_1346jobs : List Job := t6_1346jobs0




def t6_1347root : Job := ⟨plan7874,[],none,⟨15,15,0⟩⟩
def t6_1347jobs0 : List Job := [⟨plan7874,[],none,⟨15,15,0⟩⟩]

def t6_1347jobs : List Job := t6_1347jobs0




def t6_1348root : Job := ⟨plan7875,[],none,⟨15,15,0⟩⟩
def t6_1348jobs0 : List Job := [⟨plan7875,[],none,⟨15,15,0⟩⟩]

def t6_1348jobs : List Job := t6_1348jobs0




def t6_1349root : Job := ⟨plan7876,[],none,⟨15,15,0⟩⟩
def t6_1349jobs0 : List Job := [⟨plan7876,[],none,⟨15,15,0⟩⟩]

def t6_1349jobs : List Job := t6_1349jobs0




def t6_1350root : Job := ⟨plan7877,[],none,⟨15,15,0⟩⟩
def t6_1350jobs0 : List Job := [⟨plan7877,[],none,⟨15,15,0⟩⟩]

def t6_1350jobs : List Job := t6_1350jobs0




def t6_1351root : Job := ⟨plan7878,[],none,⟨15,15,0⟩⟩
def t6_1351jobs0 : List Job := [⟨plan7878,[],none,⟨15,15,0⟩⟩]

def t6_1351jobs : List Job := t6_1351jobs0




def t6_1352root : Job := ⟨plan7879,[],none,⟨15,15,0⟩⟩
def t6_1352jobs0 : List Job := [⟨plan7879,[],none,⟨15,15,0⟩⟩]

def t6_1352jobs : List Job := t6_1352jobs0




def t6_1353root : Job := ⟨plan7880,[],none,⟨15,15,0⟩⟩
def t6_1353jobs0 : List Job := [⟨plan7880,[],none,⟨15,15,0⟩⟩]

def t6_1353jobs : List Job := t6_1353jobs0




def t6_1354root : Job := ⟨plan7881,[],none,⟨15,15,0⟩⟩
def t6_1354jobs0 : List Job := [⟨plan7881,[],none,⟨15,15,0⟩⟩]

def t6_1354jobs : List Job := t6_1354jobs0




def t6_1355root : Job := ⟨plan7882,[],none,⟨15,15,0⟩⟩
def t6_1355jobs0 : List Job := [⟨plan7882,[],none,⟨15,15,0⟩⟩]

def t6_1355jobs : List Job := t6_1355jobs0




def t6_1356root : Job := ⟨plan6658,[],none,⟨15,3,0⟩⟩
def t6_1356jobs0 : List Job := [⟨plan6658,[],none,⟨15,3,0⟩⟩]

def t6_1356jobs : List Job := t6_1356jobs0




def t6_1357root : Job := ⟨plan7071,[],none,⟨15,6,0⟩⟩
def t6_1357jobs0 : List Job := [⟨plan7071,[],none,⟨15,6,0⟩⟩]

def t6_1357jobs : List Job := t6_1357jobs0




def t6_1358root : Job := ⟨plan7072,[],none,⟨15,6,0⟩⟩
def t6_1358jobs0 : List Job := [⟨plan7072,[],none,⟨15,6,0⟩⟩]

def t6_1358jobs : List Job := t6_1358jobs0




def t6_1359root : Job := ⟨plan7073,[],none,⟨15,6,0⟩⟩
def t6_1359jobs0 : List Job := [⟨plan7073,[],none,⟨15,6,0⟩⟩]

def t6_1359jobs : List Job := t6_1359jobs0




def t6_1360root : Job := ⟨plan7580,[],none,⟨15,10,0⟩⟩
def t6_1360jobs0 : List Job := [⟨plan7580,[],none,⟨15,10,0⟩⟩]

def t6_1360jobs : List Job := t6_1360jobs0




def t6_1361root : Job := ⟨plan7581,[],none,⟨15,10,0⟩⟩
def t6_1361jobs0 : List Job := [⟨plan7581,[],none,⟨15,10,0⟩⟩]

def t6_1361jobs : List Job := t6_1361jobs0




def t6_1362root : Job := ⟨plan7582,[],none,⟨15,10,0⟩⟩
def t6_1362jobs0 : List Job := [⟨plan7582,[],none,⟨15,10,0⟩⟩]

def t6_1362jobs : List Job := t6_1362jobs0




def t6_1363root : Job := ⟨plan7583,[],none,⟨15,10,0⟩⟩
def t6_1363jobs0 : List Job := [⟨plan5951,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5951,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5951,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5951,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1363jobs1 : List Job := [⟨plan5951,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1363jobs : List Job := t6_1363jobs0++t6_1363jobs1




def t6_1364root : Job := ⟨plan7584,[],none,⟨15,10,0⟩⟩
def t6_1364jobs0 : List Job := [⟨plan7584,[],none,⟨15,10,0⟩⟩]

def t6_1364jobs : List Job := t6_1364jobs0




def t6_1365root : Job := ⟨plan7585,[],none,⟨15,10,0⟩⟩
def t6_1365jobs0 : List Job := [⟨plan7585,[],none,⟨15,10,0⟩⟩]

def t6_1365jobs : List Job := t6_1365jobs0




def t6_1366root : Job := ⟨plan7883,[],none,⟨15,15,0⟩⟩
def t6_1366jobs0 : List Job := [⟨plan7883,[],none,⟨15,15,0⟩⟩]

def t6_1366jobs : List Job := t6_1366jobs0




def t6_1367root : Job := ⟨plan7884,[],none,⟨15,15,0⟩⟩
def t6_1367jobs0 : List Job := [⟨plan7884,[],none,⟨15,15,0⟩⟩]

def t6_1367jobs : List Job := t6_1367jobs0




def t6_1368root : Job := ⟨plan7885,[],none,⟨15,15,0⟩⟩
def t6_1368jobs0 : List Job := [⟨plan7885,[],none,⟨15,15,0⟩⟩]

def t6_1368jobs : List Job := t6_1368jobs0




def t6_1369root : Job := ⟨plan7886,[],none,⟨15,15,0⟩⟩
def t6_1369jobs0 : List Job := [⟨plan7886,[],none,⟨15,15,0⟩⟩]

def t6_1369jobs : List Job := t6_1369jobs0




def t6_1370root : Job := ⟨plan7887,[],none,⟨15,15,0⟩⟩
def t6_1370jobs0 : List Job := [⟨plan7887,[],none,⟨15,15,0⟩⟩]

def t6_1370jobs : List Job := t6_1370jobs0




def t6_1371root : Job := ⟨plan7888,[],none,⟨15,15,0⟩⟩
def t6_1371jobs0 : List Job := [⟨plan7888,[],none,⟨15,15,0⟩⟩]

def t6_1371jobs : List Job := t6_1371jobs0




def t6_1372root : Job := ⟨plan7889,[],none,⟨15,15,0⟩⟩
def t6_1372jobs0 : List Job := [⟨plan7889,[],none,⟨15,15,0⟩⟩]

def t6_1372jobs : List Job := t6_1372jobs0




def t6_1373root : Job := ⟨plan7586,[],none,⟨15,10,0⟩⟩
def t6_1373jobs0 : List Job := [⟨plan7586,[],none,⟨15,10,0⟩⟩]

def t6_1373jobs : List Job := t6_1373jobs0




def t6_1374root : Job := ⟨plan7890,[],none,⟨15,15,0⟩⟩
def t6_1374jobs0 : List Job := [⟨plan7890,[],none,⟨15,15,0⟩⟩]

def t6_1374jobs : List Job := t6_1374jobs0




def t6_1375root : Job := ⟨plan7891,[],none,⟨15,15,0⟩⟩
def t6_1375jobs0 : List Job := [⟨plan7891,[],none,⟨15,15,0⟩⟩]

def t6_1375jobs : List Job := t6_1375jobs0




def t6_1376root : Job := ⟨plan7892,[],none,⟨15,15,0⟩⟩
def t6_1376jobs0 : List Job := [⟨plan7892,[],none,⟨15,15,0⟩⟩]

def t6_1376jobs : List Job := t6_1376jobs0




def t6_1377root : Job := ⟨plan7893,[],none,⟨15,15,0⟩⟩
def t6_1377jobs0 : List Job := [⟨plan7893,[],none,⟨15,15,0⟩⟩]

def t6_1377jobs : List Job := t6_1377jobs0




def t6_1378root : Job := ⟨plan7894,[],none,⟨15,15,0⟩⟩
def t6_1378jobs0 : List Job := [⟨plan7894,[],none,⟨15,15,0⟩⟩]

def t6_1378jobs : List Job := t6_1378jobs0




def t6_1379root : Job := ⟨plan7895,[],none,⟨15,15,0⟩⟩
def t6_1379jobs0 : List Job := [⟨plan7895,[],none,⟨15,15,0⟩⟩]

def t6_1379jobs : List Job := t6_1379jobs0




def t6_1380root : Job := ⟨plan7896,[],none,⟨15,15,0⟩⟩
def t6_1380jobs0 : List Job := [⟨plan7896,[],none,⟨15,15,0⟩⟩]

def t6_1380jobs : List Job := t6_1380jobs0




def t6_1381root : Job := ⟨plan7897,[],none,⟨15,15,0⟩⟩
def t6_1381jobs0 : List Job := [⟨plan7897,[],none,⟨15,15,0⟩⟩]

def t6_1381jobs : List Job := t6_1381jobs0




def t6_1382root : Job := ⟨plan7898,[],none,⟨15,15,0⟩⟩
def t6_1382jobs0 : List Job := [⟨plan7898,[],none,⟨15,15,0⟩⟩]

def t6_1382jobs : List Job := t6_1382jobs0




def t6_1383root : Job := ⟨plan7899,[],none,⟨15,15,0⟩⟩
def t6_1383jobs0 : List Job := [⟨plan7899,[],none,⟨15,15,0⟩⟩]

def t6_1383jobs : List Job := t6_1383jobs0




def t6_1384root : Job := ⟨plan7900,[],none,⟨15,15,0⟩⟩
def t6_1384jobs0 : List Job := [⟨plan7900,[],none,⟨15,15,0⟩⟩]

def t6_1384jobs : List Job := t6_1384jobs0




def t6_1385root : Job := ⟨plan7901,[],none,⟨15,15,0⟩⟩
def t6_1385jobs0 : List Job := [⟨plan7901,[],none,⟨15,15,0⟩⟩]

def t6_1385jobs : List Job := t6_1385jobs0




def t6_1386root : Job := ⟨plan7902,[],none,⟨15,15,0⟩⟩
def t6_1386jobs0 : List Job := [⟨plan7902,[],none,⟨15,15,0⟩⟩]

def t6_1386jobs : List Job := t6_1386jobs0




def t6_1387root : Job := ⟨plan7903,[],none,⟨15,15,0⟩⟩
def t6_1387jobs0 : List Job := [⟨plan7903,[],none,⟨15,15,0⟩⟩]

def t6_1387jobs : List Job := t6_1387jobs0




def t6_1388root : Job := ⟨plan7904,[],none,⟨15,15,0⟩⟩
def t6_1388jobs0 : List Job := [⟨plan7904,[],none,⟨15,15,0⟩⟩]

def t6_1388jobs : List Job := t6_1388jobs0




def t6_1389root : Job := ⟨plan7905,[],none,⟨15,15,0⟩⟩
def t6_1389jobs0 : List Job := [⟨plan7905,[],none,⟨15,15,0⟩⟩]

def t6_1389jobs : List Job := t6_1389jobs0




def t6_1390root : Job := ⟨plan7906,[],none,⟨15,15,0⟩⟩
def t6_1390jobs0 : List Job := [⟨plan7906,[],none,⟨15,15,0⟩⟩]

def t6_1390jobs : List Job := t6_1390jobs0




def t6_1391root : Job := ⟨plan7907,[],none,⟨15,15,0⟩⟩
def t6_1391jobs0 : List Job := [⟨plan7907,[],none,⟨15,15,0⟩⟩]

def t6_1391jobs : List Job := t6_1391jobs0




def t6_1392root : Job := ⟨plan7908,[],none,⟨15,15,0⟩⟩
def t6_1392jobs0 : List Job := [⟨plan7908,[],none,⟨15,15,0⟩⟩]

def t6_1392jobs : List Job := t6_1392jobs0




def t6_1393root : Job := ⟨plan7909,[],none,⟨15,15,0⟩⟩
def t6_1393jobs0 : List Job := [⟨plan7909,[],none,⟨15,15,0⟩⟩]

def t6_1393jobs : List Job := t6_1393jobs0




def t6_1394root : Job := ⟨plan7910,[],none,⟨15,15,0⟩⟩
def t6_1394jobs0 : List Job := [⟨plan7910,[],none,⟨15,15,0⟩⟩]

def t6_1394jobs : List Job := t6_1394jobs0




def t6_1395root : Job := ⟨plan7911,[],none,⟨15,15,0⟩⟩
def t6_1395jobs0 : List Job := [⟨plan7911,[],none,⟨15,15,0⟩⟩]

def t6_1395jobs : List Job := t6_1395jobs0




def t6_1396root : Job := ⟨plan7912,[],none,⟨15,15,0⟩⟩
def t6_1396jobs0 : List Job := [⟨plan7912,[],none,⟨15,15,0⟩⟩]

def t6_1396jobs : List Job := t6_1396jobs0




def t6_1397root : Job := ⟨plan7913,[],none,⟨15,15,0⟩⟩
def t6_1397jobs0 : List Job := [⟨plan7913,[],none,⟨15,15,0⟩⟩]

def t6_1397jobs : List Job := t6_1397jobs0




def t6_1398root : Job := ⟨plan7914,[],none,⟨15,15,0⟩⟩
def t6_1398jobs0 : List Job := [⟨plan7914,[],none,⟨15,15,0⟩⟩]

def t6_1398jobs : List Job := t6_1398jobs0




def t6_1399root : Job := ⟨plan7915,[],none,⟨15,15,0⟩⟩
def t6_1399jobs0 : List Job := [⟨plan7915,[],none,⟨15,15,0⟩⟩]

def t6_1399jobs : List Job := t6_1399jobs0




def t6_1400root : Job := ⟨plan7916,[],none,⟨15,15,0⟩⟩
def t6_1400jobs0 : List Job := [⟨plan7916,[],none,⟨15,15,0⟩⟩]

def t6_1400jobs : List Job := t6_1400jobs0




def t6_1401root : Job := ⟨plan7917,[],none,⟨15,15,0⟩⟩
def t6_1401jobs0 : List Job := [⟨plan7917,[],none,⟨15,15,0⟩⟩]

def t6_1401jobs : List Job := t6_1401jobs0




def t6_1402root : Job := ⟨plan7918,[],none,⟨15,15,0⟩⟩
def t6_1402jobs0 : List Job := [⟨plan7918,[],none,⟨15,15,0⟩⟩]

def t6_1402jobs : List Job := t6_1402jobs0




def t6_1403root : Job := ⟨plan7919,[],none,⟨15,15,0⟩⟩
def t6_1403jobs0 : List Job := [⟨plan7919,[],none,⟨15,15,0⟩⟩]

def t6_1403jobs : List Job := t6_1403jobs0




def t6_1404root : Job := ⟨plan7920,[],none,⟨15,15,0⟩⟩
def t6_1404jobs0 : List Job := [⟨plan7920,[],none,⟨15,15,0⟩⟩]

def t6_1404jobs : List Job := t6_1404jobs0




def t6_1405root : Job := ⟨plan7921,[],none,⟨15,15,0⟩⟩
def t6_1405jobs0 : List Job := [⟨plan7921,[],none,⟨15,15,0⟩⟩]

def t6_1405jobs : List Job := t6_1405jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


