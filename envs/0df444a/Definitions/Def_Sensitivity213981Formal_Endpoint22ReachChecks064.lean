-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks064
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks064
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:14.937506+00:00
-- url     : https://prove2.me/theorems/e04a2f21-b621-4c77-b4b9-18fa0b868272
-- title:
--   Endpoint22 Reach Checks064 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks064 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_569jobs0`, `ThreeBoundEndpoint22Reachable.t6_569jobs1`, `ThreeBoundEndpoint22Reachable.t6_569jobs2`, `ThreeBoundEndpoint22Reachable.t6_569jobs`, `ThreeBoundEndpoint22Reachable.t6_570root`, `ThreeBoundEndpoint22Reachable.t6_570jobs0`, `ThreeBoundEndpoint22Reachable.t6_570jobs`, `ThreeBoundEndpoint22Reachable.t6_571root`, `ThreeBoundEndpoint22Reachable.t6_571jobs0`, `ThreeBoundEndpoint22Reachable.t6_571jobs1`, `ThreeBoundEndpoint22Reachable.t6_571jobs2`, `ThreeBoundEndpoint22Reachable.t6_571jobs3`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks064.lean, lines 1–164.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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

def t6_561root : Job := ⟨plan6559,[],none,⟨15,3,0⟩⟩
def t6_561jobs0 : List Job := [⟨plan3319,[⟨2,0,3⟩,⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3319,[⟨2,0,3⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3319,[⟨2,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3319,[⟨2,0,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨2,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨2,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨2,1,2⟩,⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨2,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨2,1,2⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3319,[⟨2,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_561jobs1 : List Job := [⟨plan3319,[⟨2,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨2,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨2,1,3⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨12,3,(-4)⟩⟩]

def t6_561jobs2 : List Job := [⟨plan3319,[⟨2,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨2,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-6)⟩⟩,⟨plan3319,[⟨2,2,1⟩,⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨11,3,(-2)⟩⟩]

def t6_561jobs3 : List Job := [⟨plan3319,[⟨2,2,1⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨11,3,(-3)⟩⟩]

def t6_561jobs4 : List Job := [⟨plan3319,[⟨2,2,1⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_561jobs5 : List Job := [⟨plan3319,[⟨2,2,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨11,3,(-4)⟩⟩]

def t6_561jobs6 : List Job := [⟨plan3319,[⟨2,2,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨11,3,(-5)⟩⟩,⟨plan3319,[⟨2,2,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨11,3,(-6)⟩⟩]

def t6_561jobs : List Job := t6_561jobs0++t6_561jobs1++t6_561jobs2++t6_561jobs3++t6_561jobs4++t6_561jobs5++t6_561jobs6




def t6_562root : Job := ⟨plan6560,[],none,⟨15,3,0⟩⟩
def t6_562jobs0 : List Job := [⟨plan5461,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5461,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_562jobs1 : List Job := [⟨plan5461,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_562jobs2 : List Job := [⟨plan5461,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_562jobs3 : List Job := [⟨plan5461,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5461,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_562jobs : List Job := t6_562jobs0++t6_562jobs1++t6_562jobs2++t6_562jobs3




def t6_563root : Job := ⟨plan6561,[],none,⟨15,3,0⟩⟩
def t6_563jobs0 : List Job := [⟨plan6561,[],none,⟨15,3,0⟩⟩]

def t6_563jobs : List Job := t6_563jobs0




def t6_564root : Job := ⟨plan6304,[],none,⟨15,0,0⟩⟩
def t6_564jobs0 : List Job := [⟨plan6304,[],none,⟨15,0,0⟩⟩]

def t6_564jobs : List Job := t6_564jobs0




def t6_565root : Job := ⟨plan6380,[],none,⟨15,1,0⟩⟩
def t6_565jobs0 : List Job := [⟨plan6380,[],none,⟨15,1,0⟩⟩]

def t6_565jobs : List Job := t6_565jobs0




def t6_566root : Job := ⟨plan6381,[],none,⟨15,1,0⟩⟩
def t6_566jobs0 : List Job := [⟨plan5388,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5388,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩,⟨plan5388,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩,⟨plan5388,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩]

def t6_566jobs1 : List Job := [⟨plan5388,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5388,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_566jobs : List Job := t6_566jobs0++t6_566jobs1




def t6_567root : Job := ⟨plan6382,[],none,⟨15,1,0⟩⟩
def t6_567jobs0 : List Job := [⟨plan6382,[],none,⟨15,1,0⟩⟩]

def t6_567jobs : List Job := t6_567jobs0




def t6_568root : Job := ⟨plan6562,[],none,⟨15,3,0⟩⟩
def t6_568jobs0 : List Job := [⟨plan6562,[],none,⟨15,3,0⟩⟩]

def t6_568jobs : List Job := t6_568jobs0




def t6_569root : Job := ⟨plan6563,[],none,⟨15,3,0⟩⟩
def t6_569jobs0 : List Job := [⟨plan5465,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5465,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5465,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_569jobs1 : List Job := [⟨plan5465,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_569jobs2 : List Job := [⟨plan5465,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5465,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_569jobs : List Job := t6_569jobs0++t6_569jobs1++t6_569jobs2




def t6_570root : Job := ⟨plan6564,[],none,⟨15,3,0⟩⟩
def t6_570jobs0 : List Job := [⟨plan6564,[],none,⟨15,3,0⟩⟩]

def t6_570jobs : List Job := t6_570jobs0




def t6_571root : Job := ⟨plan6565,[],none,⟨15,3,0⟩⟩
def t6_571jobs0 : List Job := [⟨plan5467,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5467,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_571jobs1 : List Job := [⟨plan5467,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_571jobs2 : List Job := [⟨plan5467,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_571jobs3 : List Job := [⟨plan5467,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5467,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_571jobs : List Job := t6_571jobs0++t6_571jobs1++t6_571jobs2++t6_571jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


