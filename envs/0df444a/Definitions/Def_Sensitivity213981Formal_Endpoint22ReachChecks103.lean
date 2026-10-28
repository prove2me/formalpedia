-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks103
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks103
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:53.175423+00:00
-- url     : https://prove2.me/theorems/9146db25-aa82-4431-8284-6735390a5824
-- title:
--   Endpoint22 Reach Checks103 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks103 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_854jobs`, `ThreeBoundEndpoint22Reachable.t6_855root`, `ThreeBoundEndpoint22Reachable.t6_855jobs0`, `ThreeBoundEndpoint22Reachable.t6_855jobs1`, `ThreeBoundEndpoint22Reachable.t6_855jobs2`, `ThreeBoundEndpoint22Reachable.t6_855jobs3`, `ThreeBoundEndpoint22Reachable.t6_855jobs`, `ThreeBoundEndpoint22Reachable.t6_851jobs1`, `ThreeBoundEndpoint22Reachable.t6_851jobs2`, `ThreeBoundEndpoint22Reachable.t6_851jobs3`, `ThreeBoundEndpoint22Reachable.t6_851jobs4`, `ThreeBoundEndpoint22Reachable.t6_851jobs5`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks103.lean, lines 1–93.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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

def t6_851root : Job := ⟨plan6616,[],none,⟨15,3,0⟩⟩
def t6_851jobs0 : List Job := [⟨plan3320,[⟨3,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3320,[⟨3,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3320,[⟨3,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3320,[⟨3,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_851jobs1 : List Job := [⟨plan3320,[⟨3,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3320,[⟨3,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3320,[⟨3,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩,⟨plan3320,[⟨3,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩,⟨plan3320,[⟨3,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3320,[⟨3,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩,⟨plan3320,[⟨3,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,3,(-2)⟩⟩]

def t6_851jobs2 : List Job := [⟨plan3320,[⟨3,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,(-3)⟩⟩,⟨plan3320,[⟨3,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-4)⟩⟩,⟨plan3320,[⟨3,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,(-1)⟩⟩,⟨plan3320,[⟨3,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-2)⟩⟩,⟨plan3320,[⟨3,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-3)⟩⟩]

def t6_851jobs3 : List Job := [⟨plan3320,[⟨3,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3320,[⟨3,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-5)⟩⟩,⟨plan3320,[⟨3,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,(-2)⟩⟩]

def t6_851jobs4 : List Job := [⟨plan3320,[⟨3,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-3)⟩⟩,⟨plan3320,[⟨3,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-4)⟩⟩,⟨plan3320,[⟨3,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-6)⟩⟩,⟨plan3320,[⟨3,2,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,(-3)⟩⟩,⟨plan3320,[⟨3,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-4)⟩⟩,⟨plan3320,[⟨3,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-5)⟩⟩,⟨plan3320,[⟨3,3,0⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨9,3,0⟩⟩]

def t6_851jobs5 : List Job := [⟨plan3320,[⟨3,3,0⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨9,3,(-1)⟩⟩,⟨plan3320,[⟨3,3,0⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,3,(-2)⟩⟩,⟨plan3320,[⟨3,3,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨9,3,(-2)⟩⟩,⟨plan3320,[⟨3,3,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,3,(-3)⟩⟩,⟨plan3320,[⟨3,3,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,3,(-4)⟩⟩]

def t6_851jobs : List Job := t6_851jobs0++t6_851jobs1++t6_851jobs2++t6_851jobs3++t6_851jobs4++t6_851jobs5




def t6_852root : Job := ⟨plan6617,[],none,⟨15,3,0⟩⟩
def t6_852jobs0 : List Job := [⟨plan5495,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5495,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5495,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5495,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-1)⟩⟩,⟨plan5495,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_852jobs1 : List Job := [⟨plan5495,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-3)⟩⟩,⟨plan5495,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,0⟩⟩,⟨plan5495,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-1)⟩⟩,⟨plan5495,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-2)⟩⟩]

def t6_852jobs : List Job := t6_852jobs0++t6_852jobs1




def t6_853root : Job := ⟨plan6971,[],none,⟨15,6,0⟩⟩
def t6_853jobs0 : List Job := [⟨plan6971,[],none,⟨15,6,0⟩⟩]

def t6_853jobs : List Job := t6_853jobs0




def t6_854root : Job := ⟨plan6972,[],none,⟨15,6,0⟩⟩
def t6_854jobs0 : List Job := [⟨plan3399,[⟨3,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,6,(-8)⟩⟩,⟨plan3399,[⟨3,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,6,(-7)⟩⟩,⟨plan3399,[⟨3,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3399,[⟨3,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,6,(-6)⟩⟩,⟨plan3399,[⟨3,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3399,[⟨3,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,6,(-5)⟩⟩,⟨plan3399,[⟨3,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3399,[⟨3,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-6)⟩⟩,⟨plan3399,[⟨3,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3399,[⟨3,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-5)⟩⟩,⟨plan3399,[⟨3,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3399,[⟨3,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-4)⟩⟩,⟨plan3399,[⟨3,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3399,[⟨3,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-8)⟩⟩,⟨plan3399,[⟨3,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3399,[⟨3,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-7)⟩⟩]

def t6_854jobs1 : List Job := [⟨plan3399,[⟨3,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-5)⟩⟩,⟨plan3399,[⟨3,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-6)⟩⟩,⟨plan3399,[⟨3,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,6,(-4)⟩⟩,⟨plan3399,[⟨3,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,6,(-5)⟩⟩,⟨plan3399,[⟨3,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,6,(-3)⟩⟩]

def t6_854jobs2 : List Job := [⟨plan3399,[⟨3,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,6,(-4)⟩⟩,⟨plan3399,[⟨3,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,6,(-6)⟩⟩]

def t6_854jobs3 : List Job := [⟨plan3399,[⟨3,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,6,(-4)⟩⟩,⟨plan3399,[⟨3,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,6,(-5)⟩⟩,⟨plan3399,[⟨3,3,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨9,6,(-2)⟩⟩]

def t6_854jobs4 : List Job := [⟨plan3399,[⟨3,3,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,6,(-3)⟩⟩,⟨plan3399,[⟨3,3,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨9,6,(-4)⟩⟩]

def t6_854jobs : List Job := t6_854jobs0++t6_854jobs1++t6_854jobs2++t6_854jobs3++t6_854jobs4




def t6_855root : Job := ⟨plan6973,[],none,⟨15,6,0⟩⟩
def t6_855jobs0 : List Job := [⟨plan5634,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5634,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5634,[⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_855jobs1 : List Job := [⟨plan5634,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_855jobs2 : List Job := [⟨plan5634,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_855jobs3 : List Job := [⟨plan5634,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,6,(-1)⟩⟩,⟨plan5634,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-2)⟩⟩]

def t6_855jobs : List Job := t6_855jobs0++t6_855jobs1++t6_855jobs2++t6_855jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


