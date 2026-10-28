-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks170
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks170
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:36.969144+00:00
-- url     : https://prove2.me/theorems/4474843d-e9eb-473c-8dde-1d2c63747f0a
-- title:
--   Endpoint22 Reach Checks170 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks170 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_274jobs3`, `ThreeBoundEndpoint22Reachable.t7_274jobs4`, `ThreeBoundEndpoint22Reachable.t7_274jobs`, `ThreeBoundEndpoint22Reachable.t7_275root`, `ThreeBoundEndpoint22Reachable.t7_275jobs0`, `ThreeBoundEndpoint22Reachable.t7_275jobs1`, `ThreeBoundEndpoint22Reachable.t7_275jobs2`, `ThreeBoundEndpoint22Reachable.t7_275jobs3`, `ThreeBoundEndpoint22Reachable.t7_275jobs4`, `ThreeBoundEndpoint22Reachable.t7_275jobs5`, `ThreeBoundEndpoint22Reachable.t7_275jobs`, `ThreeBoundEndpoint22Reachable.t7_274root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks170.lean, lines 1–110.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
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

def t7_274root : Job := ⟨plan8453,[],none,⟨21,3,0⟩⟩
def t7_274jobs0 : List Job := [⟨plan8097,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8097,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8097,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,3,(-3)⟩⟩]

def t7_274jobs1 : List Job := [⟨plan8097,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_274jobs2 : List Job := [⟨plan8097,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_274jobs3 : List Job := [⟨plan8097,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_274jobs4 : List Job := [⟨plan8097,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨18,3,0⟩⟩,⟨plan8097,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,3,(-1)⟩⟩,⟨plan8097,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,3,(-2)⟩⟩,⟨plan8097,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,3,(-3)⟩⟩]

def t7_274jobs : List Job := t7_274jobs0++t7_274jobs1++t7_274jobs2++t7_274jobs3++t7_274jobs4




def t7_275root : Job := ⟨plan8454,[],none,⟨21,3,0⟩⟩
def t7_275jobs0 : List Job := [⟨plan8098,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8098,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8098,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,3,(-3)⟩⟩]

def t7_275jobs1 : List Job := [⟨plan8098,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_275jobs2 : List Job := [⟨plan8098,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_275jobs3 : List Job := [⟨plan8098,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_275jobs4 : List Job := [⟨plan8098,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨18,3,0⟩⟩]

def t7_275jobs5 : List Job := [⟨plan8098,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,3,(-1)⟩⟩,⟨plan8098,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,3,(-2)⟩⟩,⟨plan8098,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,3,(-3)⟩⟩]

def t7_275jobs : List Job := t7_275jobs0++t7_275jobs1++t7_275jobs2++t7_275jobs3++t7_275jobs4++t7_275jobs5




def t7_276root : Job := ⟨plan8455,[],none,⟨21,3,0⟩⟩
def t7_276jobs0 : List Job := [⟨plan8099,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8099,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8099,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,3,(-3)⟩⟩,⟨plan8099,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨19,3,(-1)⟩⟩,⟨plan8099,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,3,(-2)⟩⟩,⟨plan8099,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_276jobs1 : List Job := [⟨plan8099,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨18,3,0⟩⟩,⟨plan8099,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,3,(-1)⟩⟩,⟨plan8099,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,3,(-2)⟩⟩,⟨plan8099,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,3,(-3)⟩⟩]

def t7_276jobs : List Job := t7_276jobs0++t7_276jobs1




def t7_277root : Job := ⟨plan8456,[],none,⟨21,3,0⟩⟩
def t7_277jobs0 : List Job := [⟨plan8456,[],none,⟨21,3,0⟩⟩]

def t7_277jobs : List Job := t7_277jobs0




def t7_278root : Job := ⟨plan8509,[],none,⟨21,6,0⟩⟩
def t7_278jobs0 : List Job := [⟨plan8509,[],none,⟨21,6,0⟩⟩]

def t7_278jobs : List Job := t7_278jobs0




def t7_279root : Job := ⟨plan8510,[],none,⟨21,6,0⟩⟩
def t7_279jobs0 : List Job := [⟨plan8123,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8123,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8123,[⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8123,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,6,(-2)⟩⟩,⟨plan8123,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-3)⟩⟩,⟨plan8123,[⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_279jobs1 : List Job := [⟨plan8123,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,6,(-1)⟩⟩,⟨plan8123,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-2)⟩⟩,⟨plan8123,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-3)⟩⟩]

def t7_279jobs : List Job := t7_279jobs0++t7_279jobs1




def t7_280root : Job := ⟨plan8511,[],none,⟨21,6,0⟩⟩
def t7_280jobs0 : List Job := [⟨plan8511,[],none,⟨21,6,0⟩⟩]

def t7_280jobs : List Job := t7_280jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


