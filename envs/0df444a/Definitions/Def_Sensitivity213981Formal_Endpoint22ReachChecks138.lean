-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks138
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks138
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:00.17309+00:00
-- url     : https://prove2.me/theorems/aa122ed9-7946-4ac3-b41e-37ede5adc2e0
-- title:
--   Endpoint22 Reach Checks138 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks138 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1419root`, `ThreeBoundEndpoint22Reachable.t6_1419jobs0`, `ThreeBoundEndpoint22Reachable.t6_1419jobs`, `ThreeBoundEndpoint22Reachable.t6_1420root`, `ThreeBoundEndpoint22Reachable.t6_1420jobs0`, `ThreeBoundEndpoint22Reachable.t6_1420jobs`, `ThreeBoundEndpoint22Reachable.t6_1421root`, `ThreeBoundEndpoint22Reachable.t6_1421jobs0`, `ThreeBoundEndpoint22Reachable.t6_1421jobs`, `ThreeBoundEndpoint22Reachable.t6_1422root`, `ThreeBoundEndpoint22Reachable.t6_1422jobs0`, `ThreeBoundEndpoint22Reachable.t6_1422jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks138.lean, lines 1–381.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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

def t6_1406root : Job := ⟨plan7922,[],none,⟨15,15,0⟩⟩
def t6_1406jobs0 : List Job := [⟨plan7922,[],none,⟨15,15,0⟩⟩]

def t6_1406jobs : List Job := t6_1406jobs0




def t6_1407root : Job := ⟨plan7923,[],none,⟨15,15,0⟩⟩
def t6_1407jobs0 : List Job := [⟨plan7923,[],none,⟨15,15,0⟩⟩]

def t6_1407jobs : List Job := t6_1407jobs0




def t6_1408root : Job := ⟨plan7924,[],none,⟨15,15,0⟩⟩
def t6_1408jobs0 : List Job := [⟨plan7924,[],none,⟨15,15,0⟩⟩]

def t6_1408jobs : List Job := t6_1408jobs0




def t6_1409root : Job := ⟨plan7925,[],none,⟨15,15,0⟩⟩
def t6_1409jobs0 : List Job := [⟨plan7925,[],none,⟨15,15,0⟩⟩]

def t6_1409jobs : List Job := t6_1409jobs0




def t6_1410root : Job := ⟨plan7926,[],none,⟨15,15,0⟩⟩
def t6_1410jobs0 : List Job := [⟨plan7926,[],none,⟨15,15,0⟩⟩]

def t6_1410jobs : List Job := t6_1410jobs0




def t6_1411root : Job := ⟨plan6659,[],none,⟨15,3,0⟩⟩
def t6_1411jobs0 : List Job := [⟨plan6659,[],none,⟨15,3,0⟩⟩]

def t6_1411jobs : List Job := t6_1411jobs0




def t6_1412root : Job := ⟨plan6421,[],none,⟨15,1,0⟩⟩
def t6_1412jobs0 : List Job := [⟨plan6421,[],none,⟨15,1,0⟩⟩]

def t6_1412jobs : List Job := t6_1412jobs0




def t6_1413root : Job := ⟨plan6660,[],none,⟨15,3,0⟩⟩
def t6_1413jobs0 : List Job := [⟨plan6660,[],none,⟨15,3,0⟩⟩]

def t6_1413jobs : List Job := t6_1413jobs0




def t6_1414root : Job := ⟨plan6661,[],none,⟨15,3,0⟩⟩
def t6_1414jobs0 : List Job := [⟨plan6661,[],none,⟨15,3,0⟩⟩]

def t6_1414jobs : List Job := t6_1414jobs0




def t6_1415root : Job := ⟨plan6662,[],none,⟨15,3,0⟩⟩
def t6_1415jobs0 : List Job := [⟨plan6662,[],none,⟨15,3,0⟩⟩]

def t6_1415jobs : List Job := t6_1415jobs0




def t6_1416root : Job := ⟨plan7074,[],none,⟨15,6,0⟩⟩
def t6_1416jobs0 : List Job := [⟨plan7074,[],none,⟨15,6,0⟩⟩]

def t6_1416jobs : List Job := t6_1416jobs0




def t6_1417root : Job := ⟨plan7075,[],none,⟨15,6,0⟩⟩
def t6_1417jobs0 : List Job := [⟨plan7075,[],none,⟨15,6,0⟩⟩]

def t6_1417jobs : List Job := t6_1417jobs0




def t6_1418root : Job := ⟨plan7076,[],none,⟨15,6,0⟩⟩
def t6_1418jobs0 : List Job := [⟨plan7076,[],none,⟨15,6,0⟩⟩]

def t6_1418jobs : List Job := t6_1418jobs0




def t6_1419root : Job := ⟨plan7077,[],none,⟨15,6,0⟩⟩
def t6_1419jobs0 : List Job := [⟨plan7077,[],none,⟨15,6,0⟩⟩]

def t6_1419jobs : List Job := t6_1419jobs0




def t6_1420root : Job := ⟨plan7078,[],none,⟨15,6,0⟩⟩
def t6_1420jobs0 : List Job := [⟨plan7078,[],none,⟨15,6,0⟩⟩]

def t6_1420jobs : List Job := t6_1420jobs0




def t6_1421root : Job := ⟨plan7079,[],none,⟨15,6,0⟩⟩
def t6_1421jobs0 : List Job := [⟨plan7079,[],none,⟨15,6,0⟩⟩]

def t6_1421jobs : List Job := t6_1421jobs0




def t6_1422root : Job := ⟨plan7080,[],none,⟨15,6,0⟩⟩
def t6_1422jobs0 : List Job := [⟨plan7080,[],none,⟨15,6,0⟩⟩]

def t6_1422jobs : List Job := t6_1422jobs0




def t6_1423root : Job := ⟨plan7081,[],none,⟨15,6,0⟩⟩
def t6_1423jobs0 : List Job := [⟨plan7081,[],none,⟨15,6,0⟩⟩]

def t6_1423jobs : List Job := t6_1423jobs0




def t6_1424root : Job := ⟨plan6317,[],none,⟨15,0,0⟩⟩
def t6_1424jobs0 : List Job := [⟨plan6317,[],none,⟨15,0,0⟩⟩]

def t6_1424jobs : List Job := t6_1424jobs0




def t6_1425root : Job := ⟨plan6422,[],none,⟨15,1,0⟩⟩
def t6_1425jobs0 : List Job := [⟨plan6422,[],none,⟨15,1,0⟩⟩]

def t6_1425jobs : List Job := t6_1425jobs0




def t6_1426root : Job := ⟨plan6423,[],none,⟨15,1,0⟩⟩
def t6_1426jobs0 : List Job := [⟨plan6423,[],none,⟨15,1,0⟩⟩]

def t6_1426jobs : List Job := t6_1426jobs0




def t6_1427root : Job := ⟨plan6424,[],none,⟨15,1,0⟩⟩
def t6_1427jobs0 : List Job := [⟨plan6424,[],none,⟨15,1,0⟩⟩]

def t6_1427jobs : List Job := t6_1427jobs0




def t6_1428root : Job := ⟨plan6663,[],none,⟨15,3,0⟩⟩
def t6_1428jobs0 : List Job := [⟨plan6663,[],none,⟨15,3,0⟩⟩]

def t6_1428jobs : List Job := t6_1428jobs0




def t6_1429root : Job := ⟨plan6664,[],none,⟨15,3,0⟩⟩
def t6_1429jobs0 : List Job := [⟨plan5448,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5448,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨14,2,0⟩⟩]

def t6_1429jobs1 : List Job := [⟨plan5448,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1429jobs : List Job := t6_1429jobs0++t6_1429jobs1




def t6_1430root : Job := ⟨plan6665,[],none,⟨15,3,0⟩⟩
def t6_1430jobs0 : List Job := [⟨plan6665,[],none,⟨15,3,0⟩⟩]

def t6_1430jobs : List Job := t6_1430jobs0




def t6_1431root : Job := ⟨plan6666,[],none,⟨15,3,0⟩⟩
def t6_1431jobs0 : List Job := [⟨plan5450,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_1431jobs1 : List Job := [⟨plan5450,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨14,2,0⟩⟩]

def t6_1431jobs2 : List Job := [⟨plan5450,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1431jobs : List Job := t6_1431jobs0++t6_1431jobs1++t6_1431jobs2




def t6_1432root : Job := ⟨plan6667,[],none,⟨15,3,0⟩⟩
def t6_1432jobs0 : List Job := [⟨plan5451,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5451,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨14,2,0⟩⟩]

def t6_1432jobs1 : List Job := [⟨plan5451,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1432jobs : List Job := t6_1432jobs0++t6_1432jobs1




def t6_1433root : Job := ⟨plan6668,[],none,⟨15,3,0⟩⟩
def t6_1433jobs0 : List Job := [⟨plan6668,[],none,⟨15,3,0⟩⟩]

def t6_1433jobs : List Job := t6_1433jobs0




def t6_1434root : Job := ⟨plan7082,[],none,⟨15,6,0⟩⟩
def t6_1434jobs0 : List Job := [⟨plan7082,[],none,⟨15,6,0⟩⟩]

def t6_1434jobs : List Job := t6_1434jobs0




def t6_1435root : Job := ⟨plan7083,[],none,⟨15,6,0⟩⟩
def t6_1435jobs0 : List Job := [⟨plan5563,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5563,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1435jobs1 : List Job := [⟨plan5563,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1435jobs : List Job := t6_1435jobs0++t6_1435jobs1




def t6_1436root : Job := ⟨plan7084,[],none,⟨15,6,0⟩⟩
def t6_1436jobs0 : List Job := [⟨plan7084,[],none,⟨15,6,0⟩⟩]

def t6_1436jobs : List Job := t6_1436jobs0




def t6_1437root : Job := ⟨plan7085,[],none,⟨15,6,0⟩⟩
def t6_1437jobs0 : List Job := [⟨plan3363,[⟨8,0,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_1437jobs1 : List Job := [⟨plan3363,[⟨8,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_1437jobs2 : List Job := [⟨plan3363,[⟨8,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_1437jobs : List Job := t6_1437jobs0++t6_1437jobs1++t6_1437jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


