-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks102
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks102
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:07.830988+00:00
-- url     : https://prove2.me/theorems/dc67f612-209c-4408-8a95-017491fb2ff0
-- title:
--   Endpoint22 Reach Checks102 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks102 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_849jobs3`, `ThreeBoundEndpoint22Reachable.t6_849jobs4`, `ThreeBoundEndpoint22Reachable.t6_849jobs`, `ThreeBoundEndpoint22Reachable.t6_850root`, `ThreeBoundEndpoint22Reachable.t6_850jobs0`, `ThreeBoundEndpoint22Reachable.t6_850jobs1`, `ThreeBoundEndpoint22Reachable.t6_850jobs2`, `ThreeBoundEndpoint22Reachable.t6_849root`, `ThreeBoundEndpoint22Reachable.t6_850jobs3`, `ThreeBoundEndpoint22Reachable.t6_850jobs4`, `ThreeBoundEndpoint22Reachable.t6_849jobs0`, `ThreeBoundEndpoint22Reachable.t6_850jobs5`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks102.lean, lines 1–57.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_849root : Job := ⟨plan6614,[],none,⟨15,3,0⟩⟩
def t6_849jobs0 : List Job := [⟨plan5492,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5492,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_849jobs1 : List Job := [⟨plan5492,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_849jobs2 : List Job := [⟨plan5492,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_849jobs3 : List Job := [⟨plan5492,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_849jobs4 : List Job := [⟨plan5492,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-3)⟩⟩,⟨plan5492,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,0⟩⟩,⟨plan5492,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-1)⟩⟩,⟨plan5492,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-2)⟩⟩]

def t6_849jobs : List Job := t6_849jobs0++t6_849jobs1++t6_849jobs2++t6_849jobs3++t6_849jobs4




def t6_850root : Job := ⟨plan6615,[],none,⟨15,3,0⟩⟩
def t6_850jobs0 : List Job := [⟨plan3319,[⟨3,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3319,[⟨3,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_850jobs1 : List Job := [⟨plan3319,[⟨3,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3319,[⟨3,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3319,[⟨3,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨3,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩]

def t6_850jobs2 : List Job := [⟨plan3319,[⟨3,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨3,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩,⟨plan3319,[⟨3,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩]

def t6_850jobs3 : List Job := [⟨plan3319,[⟨3,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3319,[⟨3,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩,⟨plan3319,[⟨3,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,3,(-2)⟩⟩,⟨plan3319,[⟨3,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,(-3)⟩⟩]

def t6_850jobs4 : List Job := [⟨plan3319,[⟨3,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-4)⟩⟩,⟨plan3319,[⟨3,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,(-1)⟩⟩,⟨plan3319,[⟨3,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-2)⟩⟩,⟨plan3319,[⟨3,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-3)⟩⟩]

def t6_850jobs5 : List Job := [⟨plan3319,[⟨3,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3319,[⟨3,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-5)⟩⟩]

def t6_850jobs6 : List Job := [⟨plan3319,[⟨3,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,(-2)⟩⟩,⟨plan3319,[⟨3,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-3)⟩⟩,⟨plan3319,[⟨3,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-4)⟩⟩,⟨plan3319,[⟨3,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-6)⟩⟩]

def t6_850jobs7 : List Job := [⟨plan3319,[⟨3,2,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,(-3)⟩⟩,⟨plan3319,[⟨3,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-4)⟩⟩,⟨plan3319,[⟨3,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-5)⟩⟩,⟨plan3319,[⟨3,3,0⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨9,3,0⟩⟩,⟨plan3319,[⟨3,3,0⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨9,3,(-1)⟩⟩,⟨plan3319,[⟨3,3,0⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,3,(-2)⟩⟩]

def t6_850jobs8 : List Job := [⟨plan3319,[⟨3,3,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨9,3,(-2)⟩⟩,⟨plan3319,[⟨3,3,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,3,(-3)⟩⟩,⟨plan3319,[⟨3,3,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,3,(-4)⟩⟩]

def t6_850jobs : List Job := t6_850jobs0++t6_850jobs1++t6_850jobs2++t6_850jobs3++t6_850jobs4++t6_850jobs5++t6_850jobs6++t6_850jobs7++t6_850jobs8



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


