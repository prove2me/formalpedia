-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks090
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks090
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:29.984016+00:00
-- url     : https://prove2.me/theorems/a8dadbb4-c3a9-4505-a9b5-c24626de3cfb
-- title:
--   Endpoint22 Reach Checks090 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks090 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_765jobs1`, `ThreeBoundEndpoint22Reachable.t6_765jobs2`, `ThreeBoundEndpoint22Reachable.t6_765jobs3`, `ThreeBoundEndpoint22Reachable.t6_765jobs`, `ThreeBoundEndpoint22Reachable.t6_766root`, `ThreeBoundEndpoint22Reachable.t6_766jobs0`, `ThreeBoundEndpoint22Reachable.t6_766jobs1`, `ThreeBoundEndpoint22Reachable.t6_766jobs`, `ThreeBoundEndpoint22Reachable.t6_767root`, `ThreeBoundEndpoint22Reachable.t6_767jobs0`, `ThreeBoundEndpoint22Reachable.t6_767jobs`, `ThreeBoundEndpoint22Reachable.t6_768root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks090.lean, lines 1–147.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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

def t6_761root : Job := ⟨plan7372,[],none,⟨15,10,0⟩⟩
def t6_761jobs0 : List Job := [⟨plan3483,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_761jobs1 : List Job := [⟨plan3483,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_761jobs : List Job := t6_761jobs0++t6_761jobs1




def t6_762root : Job := ⟨plan7373,[],none,⟨15,10,0⟩⟩
def t6_762jobs0 : List Job := [⟨plan7373,[],none,⟨15,10,0⟩⟩]

def t6_762jobs : List Job := t6_762jobs0




def t6_763root : Job := ⟨plan7374,[],none,⟨15,10,0⟩⟩
def t6_763jobs0 : List Job := [⟨plan3485,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_763jobs1 : List Job := [⟨plan3485,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_763jobs2 : List Job := [⟨plan3485,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_763jobs : List Job := t6_763jobs0++t6_763jobs1++t6_763jobs2




def t6_764root : Job := ⟨plan7375,[],none,⟨15,10,0⟩⟩
def t6_764jobs0 : List Job := [⟨plan3507,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩]

def t6_764jobs1 : List Job := [⟨plan3507,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩]

def t6_764jobs2 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_764jobs3 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩]

def t6_764jobs4 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_764jobs : List Job := t6_764jobs0++t6_764jobs1++t6_764jobs2++t6_764jobs3++t6_764jobs4




def t6_765root : Job := ⟨plan7376,[],none,⟨15,10,0⟩⟩
def t6_765jobs0 : List Job := [⟨plan3508,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_765jobs1 : List Job := [⟨plan3508,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_765jobs2 : List Job := [⟨plan3508,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩]

def t6_765jobs3 : List Job := [⟨plan3508,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_765jobs : List Job := t6_765jobs0++t6_765jobs1++t6_765jobs2++t6_765jobs3




def t6_766root : Job := ⟨plan7377,[],none,⟨15,10,0⟩⟩
def t6_766jobs0 : List Job := [⟨plan3509,[⟨2,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3509,[⟨2,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3509,[⟨2,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3509,[⟨2,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3509,[⟨2,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3509,[⟨2,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3509,[⟨2,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3509,[⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3509,[⟨2,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3509,[⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3509,[⟨2,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3509,[⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3509,[⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_766jobs1 : List Job := [⟨plan3509,[⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3509,[⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_766jobs : List Job := t6_766jobs0++t6_766jobs1




def t6_767root : Job := ⟨plan7378,[],none,⟨15,10,0⟩⟩
def t6_767jobs0 : List Job := [⟨plan7378,[],none,⟨15,10,0⟩⟩]

def t6_767jobs : List Job := t6_767jobs0




def t6_768root : Job := ⟨plan7379,[],none,⟨15,10,0⟩⟩
def t6_768jobs0 : List Job := [⟨plan5898,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5898,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_768jobs1 : List Job := [⟨plan5898,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_768jobs : List Job := t6_768jobs0++t6_768jobs1




def t6_769root : Job := ⟨plan6310,[],none,⟨15,0,0⟩⟩
def t6_769jobs0 : List Job := [⟨plan6310,[],none,⟨15,0,0⟩⟩]

def t6_769jobs : List Job := t6_769jobs0




def t6_770root : Job := ⟨plan6397,[],none,⟨15,1,0⟩⟩
def t6_770jobs0 : List Job := [⟨plan6397,[],none,⟨15,1,0⟩⟩]

def t6_770jobs : List Job := t6_770jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


