-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks134
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks134
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:31.788356+00:00
-- url     : https://prove2.me/theorems/1a5a4b7d-e78e-40fe-a21e-e192f1d4251f
-- title:
--   Endpoint22 Reach Checks134 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks134 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1300root`, `ThreeBoundEndpoint22Reachable.t6_1300jobs0`, `ThreeBoundEndpoint22Reachable.t6_1300jobs`, `ThreeBoundEndpoint22Reachable.t6_1301root`, `ThreeBoundEndpoint22Reachable.t6_1301jobs0`, `ThreeBoundEndpoint22Reachable.t6_1301jobs`, `ThreeBoundEndpoint22Reachable.t6_1302root`, `ThreeBoundEndpoint22Reachable.t6_1302jobs0`, `ThreeBoundEndpoint22Reachable.t6_1288jobs`, `ThreeBoundEndpoint22Reachable.t6_1302jobs`, `ThreeBoundEndpoint22Reachable.t6_1303root`, `ThreeBoundEndpoint22Reachable.t6_1303jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks134.lean, lines 1–489.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans081
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

def t6_1288root : Job := ⟨plan7566,[],none,⟨15,10,0⟩⟩
def t6_1288jobs0 : List Job := [⟨plan5862,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5862,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5862,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5862,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1288jobs1 : List Job := [⟨plan5862,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1288jobs : List Job := t6_1288jobs0++t6_1288jobs1




def t6_1289root : Job := ⟨plan7567,[],none,⟨15,10,0⟩⟩
def t6_1289jobs0 : List Job := [⟨plan7567,[],none,⟨15,10,0⟩⟩]

def t6_1289jobs : List Job := t6_1289jobs0




def t6_1290root : Job := ⟨plan7568,[],none,⟨15,10,0⟩⟩
def t6_1290jobs0 : List Job := [⟨plan7568,[],none,⟨15,10,0⟩⟩]

def t6_1290jobs : List Job := t6_1290jobs0




def t6_1291root : Job := ⟨plan7839,[],none,⟨15,15,0⟩⟩
def t6_1291jobs0 : List Job := [⟨plan7839,[],none,⟨15,15,0⟩⟩]

def t6_1291jobs : List Job := t6_1291jobs0




def t6_1292root : Job := ⟨plan7840,[],none,⟨15,15,0⟩⟩
def t6_1292jobs0 : List Job := [⟨plan7840,[],none,⟨15,15,0⟩⟩]

def t6_1292jobs : List Job := t6_1292jobs0




def t6_1293root : Job := ⟨plan7841,[],none,⟨15,15,0⟩⟩
def t6_1293jobs0 : List Job := [⟨plan7841,[],none,⟨15,15,0⟩⟩]

def t6_1293jobs : List Job := t6_1293jobs0




def t6_1294root : Job := ⟨plan7842,[],none,⟨15,15,0⟩⟩
def t6_1294jobs0 : List Job := [⟨plan7842,[],none,⟨15,15,0⟩⟩]

def t6_1294jobs : List Job := t6_1294jobs0




def t6_1295root : Job := ⟨plan7843,[],none,⟨15,15,0⟩⟩
def t6_1295jobs0 : List Job := [⟨plan7843,[],none,⟨15,15,0⟩⟩]

def t6_1295jobs : List Job := t6_1295jobs0




def t6_1296root : Job := ⟨plan7844,[],none,⟨15,15,0⟩⟩
def t6_1296jobs0 : List Job := [⟨plan7844,[],none,⟨15,15,0⟩⟩]

def t6_1296jobs : List Job := t6_1296jobs0




def t6_1297root : Job := ⟨plan7845,[],none,⟨15,15,0⟩⟩
def t6_1297jobs0 : List Job := [⟨plan7845,[],none,⟨15,15,0⟩⟩]

def t6_1297jobs : List Job := t6_1297jobs0




def t6_1298root : Job := ⟨plan7569,[],none,⟨15,10,0⟩⟩
def t6_1298jobs0 : List Job := [⟨plan7569,[],none,⟨15,10,0⟩⟩]

def t6_1298jobs : List Job := t6_1298jobs0




def t6_1299root : Job := ⟨plan7846,[],none,⟨15,15,0⟩⟩
def t6_1299jobs0 : List Job := [⟨plan7846,[],none,⟨15,15,0⟩⟩]

def t6_1299jobs : List Job := t6_1299jobs0




def t6_1300root : Job := ⟨plan7847,[],none,⟨15,15,0⟩⟩
def t6_1300jobs0 : List Job := [⟨plan7847,[],none,⟨15,15,0⟩⟩]

def t6_1300jobs : List Job := t6_1300jobs0




def t6_1301root : Job := ⟨plan7848,[],none,⟨15,15,0⟩⟩
def t6_1301jobs0 : List Job := [⟨plan7848,[],none,⟨15,15,0⟩⟩]

def t6_1301jobs : List Job := t6_1301jobs0




def t6_1302root : Job := ⟨plan7849,[],none,⟨15,15,0⟩⟩
def t6_1302jobs0 : List Job := [⟨plan7849,[],none,⟨15,15,0⟩⟩]

def t6_1302jobs : List Job := t6_1302jobs0




def t6_1303root : Job := ⟨plan7850,[],none,⟨15,15,0⟩⟩
def t6_1303jobs0 : List Job := [⟨plan7850,[],none,⟨15,15,0⟩⟩]

def t6_1303jobs : List Job := t6_1303jobs0




def t6_1304root : Job := ⟨plan7851,[],none,⟨15,15,0⟩⟩
def t6_1304jobs0 : List Job := [⟨plan7851,[],none,⟨15,15,0⟩⟩]

def t6_1304jobs : List Job := t6_1304jobs0




def t6_1305root : Job := ⟨plan7852,[],none,⟨15,15,0⟩⟩
def t6_1305jobs0 : List Job := [⟨plan7852,[],none,⟨15,15,0⟩⟩]

def t6_1305jobs : List Job := t6_1305jobs0




def t6_1306root : Job := ⟨plan7853,[],none,⟨15,15,0⟩⟩
def t6_1306jobs0 : List Job := [⟨plan7853,[],none,⟨15,15,0⟩⟩]

def t6_1306jobs : List Job := t6_1306jobs0




def t6_1307root : Job := ⟨plan7854,[],none,⟨15,15,0⟩⟩
def t6_1307jobs0 : List Job := [⟨plan7854,[],none,⟨15,15,0⟩⟩]

def t6_1307jobs : List Job := t6_1307jobs0




def t6_1308root : Job := ⟨plan7855,[],none,⟨15,15,0⟩⟩
def t6_1308jobs0 : List Job := [⟨plan7855,[],none,⟨15,15,0⟩⟩]

def t6_1308jobs : List Job := t6_1308jobs0




def t6_1309root : Job := ⟨plan7856,[],none,⟨15,15,0⟩⟩
def t6_1309jobs0 : List Job := [⟨plan7856,[],none,⟨15,15,0⟩⟩]

def t6_1309jobs : List Job := t6_1309jobs0




def t6_1310root : Job := ⟨plan7857,[],none,⟨15,15,0⟩⟩
def t6_1310jobs0 : List Job := [⟨plan7857,[],none,⟨15,15,0⟩⟩]

def t6_1310jobs : List Job := t6_1310jobs0




def t6_1311root : Job := ⟨plan7858,[],none,⟨15,15,0⟩⟩
def t6_1311jobs0 : List Job := [⟨plan7858,[],none,⟨15,15,0⟩⟩]

def t6_1311jobs : List Job := t6_1311jobs0




def t6_1312root : Job := ⟨plan7859,[],none,⟨15,15,0⟩⟩
def t6_1312jobs0 : List Job := [⟨plan7859,[],none,⟨15,15,0⟩⟩]

def t6_1312jobs : List Job := t6_1312jobs0




def t6_1313root : Job := ⟨plan7860,[],none,⟨15,15,0⟩⟩
def t6_1313jobs0 : List Job := [⟨plan7860,[],none,⟨15,15,0⟩⟩]

def t6_1313jobs : List Job := t6_1313jobs0




def t6_1314root : Job := ⟨plan7861,[],none,⟨15,15,0⟩⟩
def t6_1314jobs0 : List Job := [⟨plan7861,[],none,⟨15,15,0⟩⟩]

def t6_1314jobs : List Job := t6_1314jobs0




def t6_1315root : Job := ⟨plan7862,[],none,⟨15,15,0⟩⟩
def t6_1315jobs0 : List Job := [⟨plan7862,[],none,⟨15,15,0⟩⟩]

def t6_1315jobs : List Job := t6_1315jobs0




def t6_1316root : Job := ⟨plan7863,[],none,⟨15,15,0⟩⟩
def t6_1316jobs0 : List Job := [⟨plan7863,[],none,⟨15,15,0⟩⟩]

def t6_1316jobs : List Job := t6_1316jobs0




def t6_1317root : Job := ⟨plan7864,[],none,⟨15,15,0⟩⟩
def t6_1317jobs0 : List Job := [⟨plan7864,[],none,⟨15,15,0⟩⟩]

def t6_1317jobs : List Job := t6_1317jobs0




def t6_1318root : Job := ⟨plan7865,[],none,⟨15,15,0⟩⟩
def t6_1318jobs0 : List Job := [⟨plan7865,[],none,⟨15,15,0⟩⟩]

def t6_1318jobs : List Job := t6_1318jobs0




def t6_1319root : Job := ⟨plan7866,[],none,⟨15,15,0⟩⟩
def t6_1319jobs0 : List Job := [⟨plan7866,[],none,⟨15,15,0⟩⟩]

def t6_1319jobs : List Job := t6_1319jobs0




def t6_1320root : Job := ⟨plan7867,[],none,⟨15,15,0⟩⟩
def t6_1320jobs0 : List Job := [⟨plan7867,[],none,⟨15,15,0⟩⟩]

def t6_1320jobs : List Job := t6_1320jobs0




def t6_1321root : Job := ⟨plan7868,[],none,⟨15,15,0⟩⟩
def t6_1321jobs0 : List Job := [⟨plan7868,[],none,⟨15,15,0⟩⟩]

def t6_1321jobs : List Job := t6_1321jobs0




def t6_1322root : Job := ⟨plan7869,[],none,⟨15,15,0⟩⟩
def t6_1322jobs0 : List Job := [⟨plan7869,[],none,⟨15,15,0⟩⟩]

def t6_1322jobs : List Job := t6_1322jobs0




def t6_1323root : Job := ⟨plan7870,[],none,⟨15,15,0⟩⟩
def t6_1323jobs0 : List Job := [⟨plan7870,[],none,⟨15,15,0⟩⟩]

def t6_1323jobs : List Job := t6_1323jobs0




def t6_1324root : Job := ⟨plan7871,[],none,⟨15,15,0⟩⟩
def t6_1324jobs0 : List Job := [⟨plan7871,[],none,⟨15,15,0⟩⟩]

def t6_1324jobs : List Job := t6_1324jobs0




def t6_1325root : Job := ⟨plan6420,[],none,⟨15,1,0⟩⟩
def t6_1325jobs0 : List Job := [⟨plan6420,[],none,⟨15,1,0⟩⟩]

def t6_1325jobs : List Job := t6_1325jobs0




def t6_1326root : Job := ⟨plan6655,[],none,⟨15,3,0⟩⟩
def t6_1326jobs0 : List Job := [⟨plan5523,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5523,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,0⟩⟩,⟨plan5523,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-1)⟩⟩,⟨plan5523,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,2⟩⟩,⟨plan5523,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,1⟩⟩]

def t6_1326jobs1 : List Job := [⟨plan5523,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,0⟩⟩]

def t6_1326jobs : List Job := t6_1326jobs0++t6_1326jobs1




def t6_1327root : Job := ⟨plan6656,[],none,⟨15,3,0⟩⟩
def t6_1327jobs0 : List Job := [⟨plan5524,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5524,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,0⟩⟩,⟨plan5524,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1327jobs1 : List Job := [⟨plan5524,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,2⟩⟩]

def t6_1327jobs2 : List Job := [⟨plan5524,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,1⟩⟩]

def t6_1327jobs3 : List Job := [⟨plan5524,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,0⟩⟩]

def t6_1327jobs : List Job := t6_1327jobs0++t6_1327jobs1++t6_1327jobs2++t6_1327jobs3




def t6_1328root : Job := ⟨plan6657,[],none,⟨15,3,0⟩⟩
def t6_1328jobs0 : List Job := [⟨plan5525,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5525,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,0⟩⟩,⟨plan5525,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-1)⟩⟩,⟨plan5525,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,2⟩⟩,⟨plan5525,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,1⟩⟩]

def t6_1328jobs1 : List Job := [⟨plan5525,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,0⟩⟩]

def t6_1328jobs : List Job := t6_1328jobs0++t6_1328jobs1




def t6_1329root : Job := ⟨plan7065,[],none,⟨15,6,0⟩⟩
def t6_1329jobs0 : List Job := [⟨plan7065,[],none,⟨15,6,0⟩⟩]

def t6_1329jobs : List Job := t6_1329jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


