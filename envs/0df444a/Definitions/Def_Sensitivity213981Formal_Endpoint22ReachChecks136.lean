-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks136
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks136
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:50.659081+00:00
-- url     : https://prove2.me/theorems/6ae39812-55c5-485e-a0a8-437116ad7235
-- title:
--   Endpoint22 Reach Checks136 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks136 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1342jobs1`, `ThreeBoundEndpoint22Reachable.t6_1342jobs2`, `ThreeBoundEndpoint22Reachable.t6_1342jobs3`, `ThreeBoundEndpoint22Reachable.t6_1342jobs`, `ThreeBoundEndpoint22Reachable.t6_1336jobs`, `ThreeBoundEndpoint22Reachable.t6_1337root`, `ThreeBoundEndpoint22Reachable.t6_1337jobs0`, `ThreeBoundEndpoint22Reachable.t6_1337jobs`, `ThreeBoundEndpoint22Reachable.t6_1338root`, `ThreeBoundEndpoint22Reachable.t6_1338jobs0`, `ThreeBoundEndpoint22Reachable.t6_1338jobs1`, `ThreeBoundEndpoint22Reachable.t6_1338jobs2`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks136.lean, lines 1–114.

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

def t6_1336root : Job := ⟨plan7571,[],none,⟨15,10,0⟩⟩
def t6_1336jobs0 : List Job := [⟨plan5928,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5928,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5928,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1336jobs1 : List Job := [⟨plan5928,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1336jobs2 : List Job := [⟨plan5928,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1336jobs : List Job := t6_1336jobs0++t6_1336jobs1++t6_1336jobs2




def t6_1337root : Job := ⟨plan7572,[],none,⟨15,10,0⟩⟩
def t6_1337jobs0 : List Job := [⟨plan7572,[],none,⟨15,10,0⟩⟩]

def t6_1337jobs : List Job := t6_1337jobs0




def t6_1338root : Job := ⟨plan7573,[],none,⟨15,10,0⟩⟩
def t6_1338jobs0 : List Job := [⟨plan3443,[⟨5,0,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,2,(-8)⟩⟩,⟨plan3443,[⟨5,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3443,[⟨5,0,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,2,(-7)⟩⟩,⟨plan3443,[⟨5,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3443,[⟨5,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3443,[⟨5,1,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3443,[⟨5,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3443,[⟨5,1,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,3,(-5)⟩⟩,⟨plan3443,[⟨5,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,5,(-2)⟩⟩,⟨plan3443,[⟨5,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,4,(-3)⟩⟩,⟨plan3443,[⟨5,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,2,(-7)⟩⟩,⟨plan3443,[⟨5,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_1338jobs1 : List Job := [⟨plan3443,[⟨5,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,2,(-6)⟩⟩,⟨plan3443,[⟨5,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3443,[⟨5,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3443,[⟨5,2,2⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,4,(-4)⟩⟩,⟨plan3443,[⟨5,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,5,(-2)⟩⟩,⟨plan3443,[⟨5,2,2⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,4,(-3)⟩⟩]

def t6_1338jobs2 : List Job := [⟨plan3443,[⟨5,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,6,0⟩⟩,⟨plan3443,[⟨5,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,5,(-1)⟩⟩,⟨plan3443,[⟨5,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,3,(-5)⟩⟩,⟨plan3443,[⟨5,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,4,(-3)⟩⟩,⟨plan3443,[⟨5,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,3,(-4)⟩⟩]

def t6_1338jobs3 : List Job := [⟨plan3443,[⟨5,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,5,(-1)⟩⟩,⟨plan3443,[⟨5,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,4,(-2)⟩⟩]

def t6_1338jobs : List Job := t6_1338jobs0++t6_1338jobs1++t6_1338jobs2++t6_1338jobs3




def t6_1339root : Job := ⟨plan7574,[],none,⟨15,10,0⟩⟩
def t6_1339jobs0 : List Job := [⟨plan5931,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5931,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5931,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1339jobs1 : List Job := [⟨plan5931,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1339jobs2 : List Job := [⟨plan5931,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1339jobs : List Job := t6_1339jobs0++t6_1339jobs1++t6_1339jobs2




def t6_1340root : Job := ⟨plan7575,[],none,⟨15,10,0⟩⟩
def t6_1340jobs0 : List Job := [⟨plan7575,[],none,⟨15,10,0⟩⟩]

def t6_1340jobs : List Job := t6_1340jobs0




def t6_1341root : Job := ⟨plan7576,[],none,⟨15,10,0⟩⟩
def t6_1341jobs0 : List Job := [⟨plan5933,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5933,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1341jobs1 : List Job := [⟨plan5933,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1341jobs2 : List Job := [⟨plan5933,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1341jobs3 : List Job := [⟨plan5933,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1341jobs : List Job := t6_1341jobs0++t6_1341jobs1++t6_1341jobs2++t6_1341jobs3




def t6_1342root : Job := ⟨plan7577,[],none,⟨15,10,0⟩⟩
def t6_1342jobs0 : List Job := [⟨plan3447,[⟨5,0,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,2,(-8)⟩⟩,⟨plan3447,[⟨5,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3447,[⟨5,0,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,2,(-7)⟩⟩,⟨plan3447,[⟨5,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3447,[⟨5,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3447,[⟨5,1,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3447,[⟨5,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3447,[⟨5,1,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,3,(-5)⟩⟩,⟨plan3447,[⟨5,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,5,(-2)⟩⟩,⟨plan3447,[⟨5,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,4,(-3)⟩⟩,⟨plan3447,[⟨5,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,2,(-7)⟩⟩,⟨plan3447,[⟨5,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_1342jobs1 : List Job := [⟨plan3447,[⟨5,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,2,(-6)⟩⟩,⟨plan3447,[⟨5,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3447,[⟨5,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3447,[⟨5,2,2⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,4,(-4)⟩⟩,⟨plan3447,[⟨5,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,5,(-2)⟩⟩,⟨plan3447,[⟨5,2,2⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,4,(-3)⟩⟩]

def t6_1342jobs2 : List Job := [⟨plan3447,[⟨5,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,6,0⟩⟩,⟨plan3447,[⟨5,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,5,(-1)⟩⟩,⟨plan3447,[⟨5,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,3,(-5)⟩⟩,⟨plan3447,[⟨5,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,4,(-3)⟩⟩,⟨plan3447,[⟨5,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,3,(-4)⟩⟩]

def t6_1342jobs3 : List Job := [⟨plan3447,[⟨5,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,5,(-1)⟩⟩,⟨plan3447,[⟨5,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,4,(-2)⟩⟩]

def t6_1342jobs : List Job := t6_1342jobs0++t6_1342jobs1++t6_1342jobs2++t6_1342jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


