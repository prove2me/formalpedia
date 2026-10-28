-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks176
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks176
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:47.656084+00:00
-- url     : https://prove2.me/theorems/0f9e3c1b-6e6f-40d6-9eb7-949296030655
-- title:
--   Endpoint22 Reach Checks176 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks176 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_300jobs1`, `ThreeBoundEndpoint22Reachable.t7_300jobs2`, `ThreeBoundEndpoint22Reachable.t7_300jobs3`, `ThreeBoundEndpoint22Reachable.t7_300jobs4`, `ThreeBoundEndpoint22Reachable.t7_300jobs5`, `ThreeBoundEndpoint22Reachable.t7_300jobs6`, `ThreeBoundEndpoint22Reachable.t7_300jobs`, `ThreeBoundEndpoint22Reachable.t7_301root`, `ThreeBoundEndpoint22Reachable.t7_301jobs0`, `ThreeBoundEndpoint22Reachable.t7_301jobs1`, `ThreeBoundEndpoint22Reachable.t7_301jobs2`, `ThreeBoundEndpoint22Reachable.t7_301jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks176.lean, lines 1–84.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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

def t7_299root : Job := ⟨plan8640,[],none,⟨21,10,0⟩⟩
def t7_299jobs0 : List Job := [⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨15,9,(-6)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3612,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨15,9,(-6)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3612,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨15,9,(-6)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3612,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩]

def t7_299jobs1 : List Job := [⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩]

def t7_299jobs2 : List Job := [⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3612,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩]

def t7_299jobs3 : List Job := [⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3612,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩]

def t7_299jobs4 : List Job := [⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩]

def t7_299jobs5 : List Job := [⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨13,6,(-7)⟩⟩]

def t7_299jobs6 : List Job := [⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3612,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨12,7,(-5)⟩⟩]

def t7_299jobs : List Job := t7_299jobs0++t7_299jobs1++t7_299jobs2++t7_299jobs3++t7_299jobs4++t7_299jobs5++t7_299jobs6




def t7_300root : Job := ⟨plan8641,[],none,⟨21,10,0⟩⟩
def t7_300jobs0 : List Job := [⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3613,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3613,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩]

def t7_300jobs1 : List Job := [⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3613,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩]

def t7_300jobs2 : List Job := [⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩]

def t7_300jobs3 : List Job := [⟨plan3613,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩]

def t7_300jobs4 : List Job := [⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨13,6,(-7)⟩⟩]

def t7_300jobs5 : List Job := [⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩]

def t7_300jobs6 : List Job := [⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3613,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨12,7,(-5)⟩⟩]

def t7_300jobs : List Job := t7_300jobs0++t7_300jobs1++t7_300jobs2++t7_300jobs3++t7_300jobs4++t7_300jobs5++t7_300jobs6




def t7_301root : Job := ⟨plan8642,[],none,⟨21,10,0⟩⟩
def t7_301jobs0 : List Job := [⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3614,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3614,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩]

def t7_301jobs1 : List Job := [⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩]

def t7_301jobs2 : List Job := [⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3614,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨12,7,(-5)⟩⟩]

def t7_301jobs : List Job := t7_301jobs0++t7_301jobs1++t7_301jobs2




def t7_302root : Job := ⟨plan8643,[],none,⟨21,10,0⟩⟩
def t7_302jobs0 : List Job := [⟨plan8643,[],none,⟨21,10,0⟩⟩]

def t7_302jobs : List Job := t7_302jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


