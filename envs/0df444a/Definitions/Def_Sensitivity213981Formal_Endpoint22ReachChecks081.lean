-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks081
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks081
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:55.507334+00:00
-- url     : https://prove2.me/theorems/fad644e6-a12c-43c5-be6f-49d463287244
-- title:
--   Endpoint22 Reach Checks081 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks081 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_668jobs2`, `ThreeBoundEndpoint22Reachable.t6_668jobs3`, `ThreeBoundEndpoint22Reachable.t6_668jobs`, `ThreeBoundEndpoint22Reachable.t6_669root`, `ThreeBoundEndpoint22Reachable.t6_669jobs0`, `ThreeBoundEndpoint22Reachable.t6_669jobs`, `ThreeBoundEndpoint22Reachable.t6_670root`, `ThreeBoundEndpoint22Reachable.t6_670jobs0`, `ThreeBoundEndpoint22Reachable.t6_670jobs1`, `ThreeBoundEndpoint22Reachable.t6_670jobs`, `ThreeBoundEndpoint22Reachable.t6_671root`, `ThreeBoundEndpoint22Reachable.t6_671jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks081.lean, lines 1–91.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_668root : Job := ⟨plan6393,[],none,⟨15,1,0⟩⟩
def t6_668jobs0 : List Job := [⟨plan5405,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5405,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩,⟨plan5405,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_668jobs1 : List Job := [⟨plan5405,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩]

def t6_668jobs2 : List Job := [⟨plan5405,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩]

def t6_668jobs3 : List Job := [⟨plan5405,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_668jobs : List Job := t6_668jobs0++t6_668jobs1++t6_668jobs2++t6_668jobs3




def t6_669root : Job := ⟨plan6394,[],none,⟨15,1,0⟩⟩
def t6_669jobs0 : List Job := [⟨plan6394,[],none,⟨15,1,0⟩⟩]

def t6_669jobs : List Job := t6_669jobs0




def t6_670root : Job := ⟨plan6587,[],none,⟨15,3,0⟩⟩
def t6_670jobs0 : List Job := [⟨plan5504,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5504,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5504,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5504,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩,⟨plan5504,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_670jobs1 : List Job := [⟨plan5504,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_670jobs : List Job := t6_670jobs0++t6_670jobs1




def t6_671root : Job := ⟨plan6588,[],none,⟨15,3,0⟩⟩
def t6_671jobs0 : List Job := [⟨plan3307,[⟨2,0,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-5)⟩⟩,⟨plan3307,[⟨2,0,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,(-3)⟩⟩,⟨plan3307,[⟨2,0,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3307,[⟨2,0,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,(-1)⟩⟩,⟨plan3307,[⟨2,0,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3307,[⟨2,0,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3307,[⟨2,1,2⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3307,[⟨2,1,2⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3307,[⟨2,1,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3307,[⟨2,1,2⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨12,3,0⟩⟩,⟨plan3307,[⟨2,1,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3307,[⟨2,1,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3307,[⟨2,1,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨14,1,(-5)⟩⟩,⟨plan3307,[⟨2,1,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨13,2,(-3)⟩⟩,⟨plan3307,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3307,[⟨2,1,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨12,3,(-1)⟩⟩]

def t6_671jobs1 : List Job := [⟨plan3307,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3307,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3307,[⟨2,2,1⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3307,[⟨2,2,1⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3307,[⟨2,2,1⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_671jobs2 : List Job := [⟨plan3307,[⟨2,2,1⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,1⟩⟩,⟨plan3307,[⟨2,2,1⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,0⟩⟩,⟨plan3307,[⟨2,2,1⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3307,[⟨2,2,2⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-4)⟩⟩]

def t6_671jobs3 : List Job := [⟨plan3307,[⟨2,2,2⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3307,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3307,[⟨2,2,2⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,0⟩⟩]

def t6_671jobs4 : List Job := [⟨plan3307,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,(-1)⟩⟩]

def t6_671jobs5 : List Job := [⟨plan3307,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3307,[⟨2,2,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-5)⟩⟩,⟨plan3307,[⟨2,2,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-3)⟩⟩,⟨plan3307,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-4)⟩⟩]

def t6_671jobs6 : List Job := [⟨plan3307,[⟨2,2,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,(-1)⟩⟩,⟨plan3307,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,(-2)⟩⟩,⟨plan3307,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-3)⟩⟩]

def t6_671jobs : List Job := t6_671jobs0++t6_671jobs1++t6_671jobs2++t6_671jobs3++t6_671jobs4++t6_671jobs5++t6_671jobs6




def t6_672root : Job := ⟨plan6589,[],none,⟨15,3,0⟩⟩
def t6_672jobs0 : List Job := [⟨plan5506,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5506,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5506,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5506,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_672jobs1 : List Job := [⟨plan5506,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_672jobs2 : List Job := [⟨plan5506,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_672jobs : List Job := t6_672jobs0++t6_672jobs1++t6_672jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


