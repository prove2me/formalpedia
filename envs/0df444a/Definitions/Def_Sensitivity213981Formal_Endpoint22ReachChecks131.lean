-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks131
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks131
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:47.710847+00:00
-- url     : https://prove2.me/theorems/3f3f25e9-c074-4faa-bf2d-e2efc0d51d5a
-- title:
--   Endpoint22 Reach Checks131 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks131 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1219jobs3`, `ThreeBoundEndpoint22Reachable.t6_1219jobs4`, `ThreeBoundEndpoint22Reachable.t6_1219jobs`, `ThreeBoundEndpoint22Reachable.t6_1215jobs1`, `ThreeBoundEndpoint22Reachable.t6_1215jobs2`, `ThreeBoundEndpoint22Reachable.t6_1215jobs3`, `ThreeBoundEndpoint22Reachable.t6_1215jobs`, `ThreeBoundEndpoint22Reachable.t6_1216root`, `ThreeBoundEndpoint22Reachable.t6_1216jobs0`, `ThreeBoundEndpoint22Reachable.t6_1216jobs`, `ThreeBoundEndpoint22Reachable.t6_1217root`, `ThreeBoundEndpoint22Reachable.t6_1217jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks131.lean, lines 1–98.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
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

def t6_1215root : Job := ⟨plan7538,[],none,⟨15,10,0⟩⟩
def t6_1215jobs0 : List Job := [⟨plan3483,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3483,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3483,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3483,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3483,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩]

def t6_1215jobs1 : List Job := [⟨plan3483,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3483,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3483,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,8,(-5)⟩⟩,⟨plan3483,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,8,(-4)⟩⟩,⟨plan3483,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,8,(-3)⟩⟩]

def t6_1215jobs2 : List Job := [⟨plan3483,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3483,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,7,(-5)⟩⟩]

def t6_1215jobs3 : List Job := [⟨plan3483,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3483,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,7,(-3)⟩⟩]

def t6_1215jobs : List Job := t6_1215jobs0++t6_1215jobs1++t6_1215jobs2++t6_1215jobs3




def t6_1216root : Job := ⟨plan7539,[],none,⟨15,10,0⟩⟩
def t6_1216jobs0 : List Job := [⟨plan7539,[],none,⟨15,10,0⟩⟩]

def t6_1216jobs : List Job := t6_1216jobs0




def t6_1217root : Job := ⟨plan7540,[],none,⟨15,10,0⟩⟩
def t6_1217jobs0 : List Job := [⟨plan5780,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5780,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1217jobs1 : List Job := [⟨plan5780,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1217jobs2 : List Job := [⟨plan5780,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1217jobs3 : List Job := [⟨plan5780,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1217jobs : List Job := t6_1217jobs0++t6_1217jobs1++t6_1217jobs2++t6_1217jobs3




def t6_1218root : Job := ⟨plan7541,[],none,⟨15,10,0⟩⟩
def t6_1218jobs0 : List Job := [⟨plan3507,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩]

def t6_1218jobs1 : List Job := [⟨plan3507,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3507,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩]

def t6_1218jobs2 : List Job := [⟨plan3507,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3507,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,8,(-4)⟩⟩]

def t6_1218jobs3 : List Job := [⟨plan3507,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,8,(-3)⟩⟩]

def t6_1218jobs4 : List Job := [⟨plan3507,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3507,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,7,(-5)⟩⟩]

def t6_1218jobs5 : List Job := [⟨plan3507,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_1218jobs6 : List Job := [⟨plan3507,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,7,(-3)⟩⟩]

def t6_1218jobs : List Job := t6_1218jobs0++t6_1218jobs1++t6_1218jobs2++t6_1218jobs3++t6_1218jobs4++t6_1218jobs5++t6_1218jobs6




def t6_1219root : Job := ⟨plan7542,[],none,⟨15,10,0⟩⟩
def t6_1219jobs0 : List Job := [⟨plan3508,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3508,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3508,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3508,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3508,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩]

def t6_1219jobs1 : List Job := [⟨plan3508,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3508,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3508,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,8,(-5)⟩⟩,⟨plan3508,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,8,(-4)⟩⟩]

def t6_1219jobs2 : List Job := [⟨plan3508,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3508,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,7,(-6)⟩⟩]

def t6_1219jobs3 : List Job := [⟨plan3508,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_1219jobs4 : List Job := [⟨plan3508,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,7,(-3)⟩⟩]

def t6_1219jobs : List Job := t6_1219jobs0++t6_1219jobs1++t6_1219jobs2++t6_1219jobs3++t6_1219jobs4



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


