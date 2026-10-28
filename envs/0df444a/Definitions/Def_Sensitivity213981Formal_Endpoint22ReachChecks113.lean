-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks113
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks113
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:10.326013+00:00
-- url     : https://prove2.me/theorems/e1bd3e17-a19f-480d-826a-da72893dc4a2
-- title:
--   Endpoint22 Reach Checks113 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks113 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_878jobs1`, `ThreeBoundEndpoint22Reachable.t6_878jobs2`, `ThreeBoundEndpoint22Reachable.t6_878jobs3`, `ThreeBoundEndpoint22Reachable.t6_878jobs4`, `ThreeBoundEndpoint22Reachable.t6_878jobs5`, `ThreeBoundEndpoint22Reachable.t6_878jobs`, `ThreeBoundEndpoint22Reachable.t6_879root`, `ThreeBoundEndpoint22Reachable.t6_879jobs0`, `ThreeBoundEndpoint22Reachable.t6_878root`, `ThreeBoundEndpoint22Reachable.t6_878jobs0`, `ThreeBoundEndpoint22Reachable.t6_879jobs1`, `ThreeBoundEndpoint22Reachable.t6_879jobs2`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks113.lean, lines 1–63.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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

def t6_878root : Job := ⟨plan7423,[],none,⟨15,10,0⟩⟩
def t6_878jobs0 : List Job := [⟨plan3485,[⟨3,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3485,[⟨3,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3485,[⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_878jobs1 : List Job := [⟨plan3485,[⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_878jobs2 : List Job := [⟨plan3485,[⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3485,[⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,6,(-6)⟩⟩]

def t6_878jobs3 : List Job := [⟨plan3485,[⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,6,(-5)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,8,(-2)⟩⟩]

def t6_878jobs4 : List Job := [⟨plan3485,[⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,7,(-3)⟩⟩,⟨plan3485,[⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,9,0⟩⟩]

def t6_878jobs5 : List Job := [⟨plan3485,[⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_878jobs : List Job := t6_878jobs0++t6_878jobs1++t6_878jobs2++t6_878jobs3++t6_878jobs4++t6_878jobs5




def t6_879root : Job := ⟨plan7424,[],none,⟨15,10,0⟩⟩
def t6_879jobs0 : List Job := [⟨plan3507,[⟨3,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3507,[⟨3,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩]

def t6_879jobs1 : List Job := [⟨plan3507,[⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩]

def t6_879jobs2 : List Job := [⟨plan3507,[⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_879jobs3 : List Job := [⟨plan3507,[⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3507,[⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩]

def t6_879jobs4 : List Job := [⟨plan3507,[⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_879jobs5 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,7,(-4)⟩⟩]

def t6_879jobs6 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,6,(-5)⟩⟩]

def t6_879jobs7 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,8,(-2)⟩⟩]

def t6_879jobs8 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,7,(-3)⟩⟩]

def t6_879jobs9 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,9,0⟩⟩]

def t6_879jobs10 : List Job := [⟨plan3507,[⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_879jobs : List Job := t6_879jobs0++t6_879jobs1++t6_879jobs2++t6_879jobs3++t6_879jobs4++t6_879jobs5++t6_879jobs6++t6_879jobs7++t6_879jobs8++t6_879jobs9++t6_879jobs10



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


