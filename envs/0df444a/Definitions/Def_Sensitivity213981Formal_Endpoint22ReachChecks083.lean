-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks083
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks083
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:51.303738+00:00
-- url     : https://prove2.me/theorems/60c4cef8-f7a5-446b-b8d4-871d28f61bf3
-- title:
--   Endpoint22 Reach Checks083 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks083 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_677jobs1`, `ThreeBoundEndpoint22Reachable.t6_677jobs2`, `ThreeBoundEndpoint22Reachable.t6_677jobs3`, `ThreeBoundEndpoint22Reachable.t6_677jobs4`, `ThreeBoundEndpoint22Reachable.t6_677jobs5`, `ThreeBoundEndpoint22Reachable.t6_677jobs`, `ThreeBoundEndpoint22Reachable.t6_678root`, `ThreeBoundEndpoint22Reachable.t6_678jobs0`, `ThreeBoundEndpoint22Reachable.t6_677root`, `ThreeBoundEndpoint22Reachable.t6_678jobs1`, `ThreeBoundEndpoint22Reachable.t6_678jobs`, `ThreeBoundEndpoint22Reachable.t6_677jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks083.lean, lines 1–76.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

def t6_677root : Job := ⟨plan6930,[],none,⟨15,6,0⟩⟩
def t6_677jobs0 : List Job := [⟨plan3361,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3361,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3361,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3361,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3361,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3361,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3361,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3361,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3361,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3361,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3361,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3361,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3361,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3361,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3361,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3361,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_677jobs1 : List Job := [⟨plan3361,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3361,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3361,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3361,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3361,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_677jobs2 : List Job := [⟨plan3361,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩,⟨plan3361,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_677jobs3 : List Job := [⟨plan3361,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3361,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3361,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3361,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_677jobs4 : List Job := [⟨plan3361,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩,⟨plan3361,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_677jobs5 : List Job := [⟨plan3361,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_677jobs : List Job := t6_677jobs0++t6_677jobs1++t6_677jobs2++t6_677jobs3++t6_677jobs4++t6_677jobs5




def t6_678root : Job := ⟨plan6931,[],none,⟨15,6,0⟩⟩
def t6_678jobs0 : List Job := [⟨plan5670,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5670,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5670,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩,⟨plan5670,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_678jobs1 : List Job := [⟨plan5670,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_678jobs : List Job := t6_678jobs0++t6_678jobs1




def t6_679root : Job := ⟨plan6932,[],none,⟨15,6,0⟩⟩
def t6_679jobs0 : List Job := [⟨plan3363,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3363,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_679jobs1 : List Job := [⟨plan3363,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3363,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_679jobs2 : List Job := [⟨plan3363,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3363,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩]

def t6_679jobs3 : List Job := [⟨plan3363,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_679jobs4 : List Job := [⟨plan3363,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩]

def t6_679jobs5 : List Job := [⟨plan3363,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_679jobs6 : List Job := [⟨plan3363,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3363,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩]

def t6_679jobs7 : List Job := [⟨plan3363,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_679jobs8 : List Job := [⟨plan3363,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩]

def t6_679jobs9 : List Job := [⟨plan3363,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_679jobs10 : List Job := [⟨plan3363,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_679jobs : List Job := t6_679jobs0++t6_679jobs1++t6_679jobs2++t6_679jobs3++t6_679jobs4++t6_679jobs5++t6_679jobs6++t6_679jobs7++t6_679jobs8++t6_679jobs9++t6_679jobs10



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


