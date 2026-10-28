-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks039
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks039
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:24.864007+00:00
-- url     : https://prove2.me/theorems/a4a7ab32-a719-40d0-8f40-95087e63730c
-- title:
--   Endpoint22 Reach Checks039 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks039 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1319root`, `ThreeBoundEndpoint22Reachable.t5_1319jobs0`, `ThreeBoundEndpoint22Reachable.t5_1319jobs`, `ThreeBoundEndpoint22Reachable.t5_1320root`, `ThreeBoundEndpoint22Reachable.t5_1320jobs0`, `ThreeBoundEndpoint22Reachable.t5_1320jobs`, `ThreeBoundEndpoint22Reachable.t5_1307jobs2`, `ThreeBoundEndpoint22Reachable.t5_1321root`, `ThreeBoundEndpoint22Reachable.t5_1321jobs0`, `ThreeBoundEndpoint22Reachable.t5_1321jobs`, `ThreeBoundEndpoint22Reachable.t5_1322root`, `ThreeBoundEndpoint22Reachable.t5_1322jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks039.lean, lines 1–614.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans054
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

def t5_1307root : Job := ⟨plan4886,[],none,⟨10,6,0⟩⟩
def t5_1307jobs0 : List Job := [⟨plan3081,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan3081,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan3081,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1307jobs1 : List Job := [⟨plan3081,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1307jobs2 : List Job := [⟨plan3081,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1307jobs : List Job := t5_1307jobs0++t5_1307jobs1++t5_1307jobs2




def t5_1308root : Job := ⟨plan4887,[],none,⟨10,6,0⟩⟩
def t5_1308jobs0 : List Job := [⟨plan4887,[],none,⟨10,6,0⟩⟩]

def t5_1308jobs : List Job := t5_1308jobs0




def t5_1309root : Job := ⟨plan5169,[],none,⟨10,10,0⟩⟩
def t5_1309jobs0 : List Job := [⟨plan5169,[],none,⟨10,10,0⟩⟩]

def t5_1309jobs : List Job := t5_1309jobs0




def t5_1310root : Job := ⟨plan5170,[],none,⟨10,10,0⟩⟩
def t5_1310jobs0 : List Job := [⟨plan5170,[],none,⟨10,10,0⟩⟩]

def t5_1310jobs : List Job := t5_1310jobs0




def t5_1311root : Job := ⟨plan5171,[],none,⟨10,10,0⟩⟩
def t5_1311jobs0 : List Job := [⟨plan5171,[],none,⟨10,10,0⟩⟩]

def t5_1311jobs : List Job := t5_1311jobs0




def t5_1312root : Job := ⟨plan5172,[],none,⟨10,10,0⟩⟩
def t5_1312jobs0 : List Job := [⟨plan5172,[],none,⟨10,10,0⟩⟩]

def t5_1312jobs : List Job := t5_1312jobs0




def t5_1313root : Job := ⟨plan5173,[],none,⟨10,10,0⟩⟩
def t5_1313jobs0 : List Job := [⟨plan5173,[],none,⟨10,10,0⟩⟩]

def t5_1313jobs : List Job := t5_1313jobs0




def t5_1314root : Job := ⟨plan5174,[],none,⟨10,10,0⟩⟩
def t5_1314jobs0 : List Job := [⟨plan5174,[],none,⟨10,10,0⟩⟩]

def t5_1314jobs : List Job := t5_1314jobs0




def t5_1315root : Job := ⟨plan5175,[],none,⟨10,10,0⟩⟩
def t5_1315jobs0 : List Job := [⟨plan5175,[],none,⟨10,10,0⟩⟩]

def t5_1315jobs : List Job := t5_1315jobs0




def t5_1316root : Job := ⟨plan4388,[],none,⟨10,3,0⟩⟩
def t5_1316jobs0 : List Job := [⟨plan4388,[],none,⟨10,3,0⟩⟩]

def t5_1316jobs : List Job := t5_1316jobs0




def t5_1317root : Job := ⟨plan4888,[],none,⟨10,6,0⟩⟩
def t5_1317jobs0 : List Job := [⟨plan4888,[],none,⟨10,6,0⟩⟩]

def t5_1317jobs : List Job := t5_1317jobs0




def t5_1318root : Job := ⟨plan4889,[],none,⟨10,6,0⟩⟩
def t5_1318jobs0 : List Job := [⟨plan4889,[],none,⟨10,6,0⟩⟩]

def t5_1318jobs : List Job := t5_1318jobs0




def t5_1319root : Job := ⟨plan4890,[],none,⟨10,6,0⟩⟩
def t5_1319jobs0 : List Job := [⟨plan4890,[],none,⟨10,6,0⟩⟩]

def t5_1319jobs : List Job := t5_1319jobs0




def t5_1320root : Job := ⟨plan5176,[],none,⟨10,10,0⟩⟩
def t5_1320jobs0 : List Job := [⟨plan5176,[],none,⟨10,10,0⟩⟩]

def t5_1320jobs : List Job := t5_1320jobs0




def t5_1321root : Job := ⟨plan5177,[],none,⟨10,10,0⟩⟩
def t5_1321jobs0 : List Job := [⟨plan5177,[],none,⟨10,10,0⟩⟩]

def t5_1321jobs : List Job := t5_1321jobs0




def t5_1322root : Job := ⟨plan5178,[],none,⟨10,10,0⟩⟩
def t5_1322jobs0 : List Job := [⟨plan5178,[],none,⟨10,10,0⟩⟩]

def t5_1322jobs : List Job := t5_1322jobs0




def t5_1323root : Job := ⟨plan5179,[],none,⟨10,10,0⟩⟩
def t5_1323jobs0 : List Job := [⟨plan5179,[],none,⟨10,10,0⟩⟩]

def t5_1323jobs : List Job := t5_1323jobs0




def t5_1324root : Job := ⟨plan4891,[],none,⟨10,6,0⟩⟩
def t5_1324jobs0 : List Job := [⟨plan4891,[],none,⟨10,6,0⟩⟩]

def t5_1324jobs : List Job := t5_1324jobs0




def t5_1325root : Job := ⟨plan5180,[],none,⟨10,10,0⟩⟩
def t5_1325jobs0 : List Job := [⟨plan5180,[],none,⟨10,10,0⟩⟩]

def t5_1325jobs : List Job := t5_1325jobs0




def t5_1326root : Job := ⟨plan5181,[],none,⟨10,10,0⟩⟩
def t5_1326jobs0 : List Job := [⟨plan5181,[],none,⟨10,10,0⟩⟩]

def t5_1326jobs : List Job := t5_1326jobs0




def t5_1327root : Job := ⟨plan5182,[],none,⟨10,10,0⟩⟩
def t5_1327jobs0 : List Job := [⟨plan5182,[],none,⟨10,10,0⟩⟩]

def t5_1327jobs : List Job := t5_1327jobs0




def t5_1328root : Job := ⟨plan5183,[],none,⟨10,10,0⟩⟩
def t5_1328jobs0 : List Job := [⟨plan5183,[],none,⟨10,10,0⟩⟩]

def t5_1328jobs : List Job := t5_1328jobs0




def t5_1329root : Job := ⟨plan5184,[],none,⟨10,10,0⟩⟩
def t5_1329jobs0 : List Job := [⟨plan5184,[],none,⟨10,10,0⟩⟩]

def t5_1329jobs : List Job := t5_1329jobs0




def t5_1330root : Job := ⟨plan5185,[],none,⟨10,10,0⟩⟩
def t5_1330jobs0 : List Job := [⟨plan5185,[],none,⟨10,10,0⟩⟩]

def t5_1330jobs : List Job := t5_1330jobs0




def t5_1331root : Job := ⟨plan5186,[],none,⟨10,10,0⟩⟩
def t5_1331jobs0 : List Job := [⟨plan5186,[],none,⟨10,10,0⟩⟩]

def t5_1331jobs : List Job := t5_1331jobs0




def t5_1332root : Job := ⟨plan5187,[],none,⟨10,10,0⟩⟩
def t5_1332jobs0 : List Job := [⟨plan5187,[],none,⟨10,10,0⟩⟩]

def t5_1332jobs : List Job := t5_1332jobs0




def t5_1333root : Job := ⟨plan5188,[],none,⟨10,10,0⟩⟩
def t5_1333jobs0 : List Job := [⟨plan5188,[],none,⟨10,10,0⟩⟩]

def t5_1333jobs : List Job := t5_1333jobs0




def t5_1334root : Job := ⟨plan5189,[],none,⟨10,10,0⟩⟩
def t5_1334jobs0 : List Job := [⟨plan5189,[],none,⟨10,10,0⟩⟩]

def t5_1334jobs : List Job := t5_1334jobs0




def t5_1335root : Job := ⟨plan5190,[],none,⟨10,10,0⟩⟩
def t5_1335jobs0 : List Job := [⟨plan5190,[],none,⟨10,10,0⟩⟩]

def t5_1335jobs : List Job := t5_1335jobs0




def t5_1336root : Job := ⟨plan5191,[],none,⟨10,10,0⟩⟩
def t5_1336jobs0 : List Job := [⟨plan5191,[],none,⟨10,10,0⟩⟩]

def t5_1336jobs : List Job := t5_1336jobs0




def t5_1337root : Job := ⟨plan5192,[],none,⟨10,10,0⟩⟩
def t5_1337jobs0 : List Job := [⟨plan5192,[],none,⟨10,10,0⟩⟩]

def t5_1337jobs : List Job := t5_1337jobs0




def t5_1338root : Job := ⟨plan5193,[],none,⟨10,10,0⟩⟩
def t5_1338jobs0 : List Job := [⟨plan5193,[],none,⟨10,10,0⟩⟩]

def t5_1338jobs : List Job := t5_1338jobs0




def t5_1339root : Job := ⟨plan5194,[],none,⟨10,10,0⟩⟩
def t5_1339jobs0 : List Job := [⟨plan5194,[],none,⟨10,10,0⟩⟩]

def t5_1339jobs : List Job := t5_1339jobs0




def t5_1340root : Job := ⟨plan5195,[],none,⟨10,10,0⟩⟩
def t5_1340jobs0 : List Job := [⟨plan5195,[],none,⟨10,10,0⟩⟩]

def t5_1340jobs : List Job := t5_1340jobs0




def t5_1341root : Job := ⟨plan5196,[],none,⟨10,10,0⟩⟩
def t5_1341jobs0 : List Job := [⟨plan5196,[],none,⟨10,10,0⟩⟩]

def t5_1341jobs : List Job := t5_1341jobs0




def t5_1342root : Job := ⟨plan5197,[],none,⟨10,10,0⟩⟩
def t5_1342jobs0 : List Job := [⟨plan5197,[],none,⟨10,10,0⟩⟩]

def t5_1342jobs : List Job := t5_1342jobs0




def t5_1343root : Job := ⟨plan5198,[],none,⟨10,10,0⟩⟩
def t5_1343jobs0 : List Job := [⟨plan5198,[],none,⟨10,10,0⟩⟩]

def t5_1343jobs : List Job := t5_1343jobs0




def t5_1344root : Job := ⟨plan5199,[],none,⟨10,10,0⟩⟩
def t5_1344jobs0 : List Job := [⟨plan5199,[],none,⟨10,10,0⟩⟩]

def t5_1344jobs : List Job := t5_1344jobs0




def t5_1345root : Job := ⟨plan5200,[],none,⟨10,10,0⟩⟩
def t5_1345jobs0 : List Job := [⟨plan5200,[],none,⟨10,10,0⟩⟩]

def t5_1345jobs : List Job := t5_1345jobs0




def t5_1346root : Job := ⟨plan5201,[],none,⟨10,10,0⟩⟩
def t5_1346jobs0 : List Job := [⟨plan5201,[],none,⟨10,10,0⟩⟩]

def t5_1346jobs : List Job := t5_1346jobs0




def t5_1347root : Job := ⟨plan5202,[],none,⟨10,10,0⟩⟩
def t5_1347jobs0 : List Job := [⟨plan5202,[],none,⟨10,10,0⟩⟩]

def t5_1347jobs : List Job := t5_1347jobs0




def t5_1348root : Job := ⟨plan5203,[],none,⟨10,10,0⟩⟩
def t5_1348jobs0 : List Job := [⟨plan5203,[],none,⟨10,10,0⟩⟩]

def t5_1348jobs : List Job := t5_1348jobs0




def t5_1349root : Job := ⟨plan5204,[],none,⟨10,10,0⟩⟩
def t5_1349jobs0 : List Job := [⟨plan5204,[],none,⟨10,10,0⟩⟩]

def t5_1349jobs : List Job := t5_1349jobs0




def t5_1350root : Job := ⟨plan5205,[],none,⟨10,10,0⟩⟩
def t5_1350jobs0 : List Job := [⟨plan5205,[],none,⟨10,10,0⟩⟩]

def t5_1350jobs : List Job := t5_1350jobs0




def t5_1351root : Job := ⟨plan5206,[],none,⟨10,10,0⟩⟩
def t5_1351jobs0 : List Job := [⟨plan5206,[],none,⟨10,10,0⟩⟩]

def t5_1351jobs : List Job := t5_1351jobs0




def t5_1352root : Job := ⟨plan5207,[],none,⟨10,10,0⟩⟩
def t5_1352jobs0 : List Job := [⟨plan5207,[],none,⟨10,10,0⟩⟩]

def t5_1352jobs : List Job := t5_1352jobs0




def t5_1353root : Job := ⟨plan5208,[],none,⟨10,10,0⟩⟩
def t5_1353jobs0 : List Job := [⟨plan5208,[],none,⟨10,10,0⟩⟩]

def t5_1353jobs : List Job := t5_1353jobs0




def t5_1354root : Job := ⟨plan3754,[],none,⟨10,0,0⟩⟩
def t5_1354jobs0 : List Job := [⟨plan3754,[],none,⟨10,0,0⟩⟩]

def t5_1354jobs : List Job := t5_1354jobs0




def t5_1355root : Job := ⟨plan3976,[],none,⟨10,1,0⟩⟩
def t5_1355jobs0 : List Job := [⟨plan3976,[],none,⟨10,1,0⟩⟩]

def t5_1355jobs : List Job := t5_1355jobs0




def t5_1356root : Job := ⟨plan3977,[],none,⟨10,1,0⟩⟩
def t5_1356jobs0 : List Job := [⟨plan3977,[],none,⟨10,1,0⟩⟩]

def t5_1356jobs : List Job := t5_1356jobs0




def t5_1357root : Job := ⟨plan3978,[],none,⟨10,1,0⟩⟩
def t5_1357jobs0 : List Job := [⟨plan3978,[],none,⟨10,1,0⟩⟩]

def t5_1357jobs : List Job := t5_1357jobs0




def t5_1358root : Job := ⟨plan3755,[],none,⟨10,0,0⟩⟩
def t5_1358jobs0 : List Job := [⟨plan3755,[],none,⟨10,0,0⟩⟩]

def t5_1358jobs : List Job := t5_1358jobs0




def t5_1359root : Job := ⟨plan3979,[],none,⟨10,1,0⟩⟩
def t5_1359jobs0 : List Job := [⟨plan3979,[],none,⟨10,1,0⟩⟩]

def t5_1359jobs : List Job := t5_1359jobs0




def t5_1360root : Job := ⟨plan3980,[],none,⟨10,1,0⟩⟩
def t5_1360jobs0 : List Job := [⟨plan3980,[],none,⟨10,1,0⟩⟩]

def t5_1360jobs : List Job := t5_1360jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


