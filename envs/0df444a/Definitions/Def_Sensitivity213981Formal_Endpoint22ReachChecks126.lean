-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks126
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks126
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:29.506221+00:00
-- url     : https://prove2.me/theorems/00e14c8c-48d4-475b-b6e1-12e78f525f86
-- title:
--   Endpoint22 Reach Checks126 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks126 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1200jobs1`, `ThreeBoundEndpoint22Reachable.t6_1200jobs2`, `ThreeBoundEndpoint22Reachable.t6_1200jobs3`, `ThreeBoundEndpoint22Reachable.t6_1200jobs4`, `ThreeBoundEndpoint22Reachable.t6_1200jobs5`, `ThreeBoundEndpoint22Reachable.t6_1200jobs6`, `ThreeBoundEndpoint22Reachable.t6_1200jobs7`, `ThreeBoundEndpoint22Reachable.t6_1200jobs8`, `ThreeBoundEndpoint22Reachable.t6_1200root`, `ThreeBoundEndpoint22Reachable.t6_1200jobs9`, `ThreeBoundEndpoint22Reachable.t6_1200jobs`, `ThreeBoundEndpoint22Reachable.t6_1200jobs0`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks126.lean, lines 1–40.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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

def t6_1200root : Job := ⟨plan7046,[],none,⟨15,6,0⟩⟩
def t6_1200jobs0 : List Job := [⟨plan3363,[⟨5,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨5,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨5,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨5,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨5,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨5,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨5,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨5,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨5,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨5,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩]

def t6_1200jobs1 : List Job := [⟨plan3363,[⟨5,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨5,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨5,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3363,[⟨5,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3363,[⟨5,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨5,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_1200jobs2 : List Job := [⟨plan3363,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨5,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨5,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3363,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_1200jobs3 : List Job := [⟨plan3363,[⟨5,2,1⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨13,5,(-3)⟩⟩,⟨plan3363,[⟨5,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,5,(-2)⟩⟩,⟨plan3363,[⟨5,2,1⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,5,(-3)⟩⟩,⟨plan3363,[⟨5,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,5,(-1)⟩⟩]

def t6_1200jobs4 : List Job := [⟨plan3363,[⟨5,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,5,(-2)⟩⟩,⟨plan3363,[⟨5,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,5,0⟩⟩,⟨plan3363,[⟨5,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,5,(-1)⟩⟩,⟨plan3363,[⟨5,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨13,4,(-4)⟩⟩]

def t6_1200jobs5 : List Job := [⟨plan3363,[⟨5,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,4,(-4)⟩⟩]

def t6_1200jobs6 : List Job := [⟨plan3363,[⟨5,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,4,(-2)⟩⟩,⟨plan3363,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,4,(-3)⟩⟩]

def t6_1200jobs7 : List Job := [⟨plan3363,[⟨5,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,4,(-1)⟩⟩,⟨plan3363,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,4,(-2)⟩⟩,⟨plan3363,[⟨5,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨5,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_1200jobs8 : List Job := [⟨plan3363,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨5,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,(-3)⟩⟩]

def t6_1200jobs9 : List Job := [⟨plan3363,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-4)⟩⟩,⟨plan3363,[⟨5,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-2)⟩⟩,⟨plan3363,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-3)⟩⟩]

def t6_1200jobs : List Job := t6_1200jobs0++t6_1200jobs1++t6_1200jobs2++t6_1200jobs3++t6_1200jobs4++t6_1200jobs5++t6_1200jobs6++t6_1200jobs7++t6_1200jobs8++t6_1200jobs9



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


