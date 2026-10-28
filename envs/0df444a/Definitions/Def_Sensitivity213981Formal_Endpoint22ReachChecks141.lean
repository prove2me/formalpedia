-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks141
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks141
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:48.099647+00:00
-- url     : https://prove2.me/theorems/c5f8a87c-a0f4-428c-9277-92767f6924f1
-- title:
--   Endpoint22 Reach Checks141 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks141 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1499jobs1`, `ThreeBoundEndpoint22Reachable.t6_1499jobs2`, `ThreeBoundEndpoint22Reachable.t6_1499jobs`, `ThreeBoundEndpoint22Reachable.t6_1500root`, `ThreeBoundEndpoint22Reachable.t6_1500jobs0`, `ThreeBoundEndpoint22Reachable.t6_1500jobs1`, `ThreeBoundEndpoint22Reachable.t6_1500jobs`, `ThreeBoundEndpoint22Reachable.t6_1501root`, `ThreeBoundEndpoint22Reachable.t6_1501jobs0`, `ThreeBoundEndpoint22Reachable.t6_1501jobs`, `ThreeBoundEndpoint22Reachable.t6_1502root`, `ThreeBoundEndpoint22Reachable.t6_1502jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks141.lean, lines 1–165.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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

def t6_1493root : Job := ⟨plan7099,[],none,⟨15,6,0⟩⟩
def t6_1493jobs0 : List Job := [⟨plan5623,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5623,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1493jobs1 : List Job := [⟨plan5623,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1493jobs : List Job := t6_1493jobs0++t6_1493jobs1




def t6_1494root : Job := ⟨plan7100,[],none,⟨15,6,0⟩⟩
def t6_1494jobs0 : List Job := [⟨plan7100,[],none,⟨15,6,0⟩⟩]

def t6_1494jobs : List Job := t6_1494jobs0




def t6_1495root : Job := ⟨plan7101,[],none,⟨15,6,0⟩⟩
def t6_1495jobs0 : List Job := [⟨plan3363,[⟨8,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨8,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩]

def t6_1495jobs1 : List Job := [⟨plan3363,[⟨8,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3363,[⟨8,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_1495jobs2 : List Job := [⟨plan3363,[⟨8,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3363,[⟨8,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_1495jobs : List Job := t6_1495jobs0++t6_1495jobs1++t6_1495jobs2




def t6_1496root : Job := ⟨plan7102,[],none,⟨15,6,0⟩⟩
def t6_1496jobs0 : List Job := [⟨plan3364,[⟨8,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3364,[⟨8,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨8,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3364,[⟨8,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨8,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3364,[⟨8,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨8,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3364,[⟨8,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3364,[⟨8,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨8,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3364,[⟨8,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_1496jobs1 : List Job := [⟨plan3364,[⟨8,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3364,[⟨8,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3364,[⟨8,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3364,[⟨8,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨8,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨8,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩]

def t6_1496jobs2 : List Job := [⟨plan3364,[⟨8,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨8,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3364,[⟨8,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3364,[⟨8,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_1496jobs : List Job := t6_1496jobs0++t6_1496jobs1++t6_1496jobs2




def t6_1497root : Job := ⟨plan7103,[],none,⟨15,6,0⟩⟩
def t6_1497jobs0 : List Job := [⟨plan7103,[],none,⟨15,6,0⟩⟩]

def t6_1497jobs : List Job := t6_1497jobs0




def t6_1498root : Job := ⟨plan7104,[],none,⟨15,6,0⟩⟩
def t6_1498jobs0 : List Job := [⟨plan5628,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩]

def t6_1498jobs1 : List Job := [⟨plan5628,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1498jobs2 : List Job := [⟨plan5628,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1498jobs : List Job := t6_1498jobs0++t6_1498jobs1++t6_1498jobs2




def t6_1499root : Job := ⟨plan7105,[],none,⟨15,6,0⟩⟩
def t6_1499jobs0 : List Job := [⟨plan3367,[⟨8,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩]

def t6_1499jobs1 : List Job := [⟨plan3367,[⟨8,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_1499jobs2 : List Job := [⟨plan3367,[⟨8,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_1499jobs : List Job := t6_1499jobs0++t6_1499jobs1++t6_1499jobs2




def t6_1500root : Job := ⟨plan7106,[],none,⟨15,6,0⟩⟩
def t6_1500jobs0 : List Job := [⟨plan5630,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5630,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1500jobs1 : List Job := [⟨plan5630,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1500jobs : List Job := t6_1500jobs0++t6_1500jobs1




def t6_1501root : Job := ⟨plan7107,[],none,⟨15,6,0⟩⟩
def t6_1501jobs0 : List Job := [⟨plan7107,[],none,⟨15,6,0⟩⟩]

def t6_1501jobs : List Job := t6_1501jobs0




def t6_1502root : Job := ⟨plan7617,[],none,⟨15,10,0⟩⟩
def t6_1502jobs0 : List Job := [⟨plan7617,[],none,⟨15,10,0⟩⟩]

def t6_1502jobs : List Job := t6_1502jobs0




def t6_1503root : Job := ⟨plan7618,[],none,⟨15,10,0⟩⟩
def t6_1503jobs0 : List Job := [⟨plan7618,[],none,⟨15,10,0⟩⟩]

def t6_1503jobs : List Job := t6_1503jobs0




def t6_1504root : Job := ⟨plan7619,[],none,⟨15,10,0⟩⟩
def t6_1504jobs0 : List Job := [⟨plan7619,[],none,⟨15,10,0⟩⟩]

def t6_1504jobs : List Job := t6_1504jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


