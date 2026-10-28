-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks177
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks177
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:39.164902+00:00
-- url     : https://prove2.me/theorems/d6943153-e97e-4a3c-8626-b15dcf2a832d
-- title:
--   Endpoint22 Reach Checks177 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks177 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_303jobs9`, `ThreeBoundEndpoint22Reachable.t7_303jobs`, `ThreeBoundEndpoint22Reachable.t7_303root`, `ThreeBoundEndpoint22Reachable.t7_303jobs1`, `ThreeBoundEndpoint22Reachable.t7_303jobs0`, `ThreeBoundEndpoint22Reachable.t7_303jobs2`, `ThreeBoundEndpoint22Reachable.t7_303jobs3`, `ThreeBoundEndpoint22Reachable.t7_303jobs4`, `ThreeBoundEndpoint22Reachable.t7_303jobs5`, `ThreeBoundEndpoint22Reachable.t7_303jobs6`, `ThreeBoundEndpoint22Reachable.t7_303jobs7`, `ThreeBoundEndpoint22Reachable.t7_303jobs8`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks177.lean, lines 1–40.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t7_303root : Job := ⟨plan8644,[],none,⟨21,10,0⟩⟩
def t7_303jobs0 : List Job := [⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨19,6,(-13)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨18,7,(-11)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨17,8,(-9)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨16,9,(-7)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨15,9,(-6)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3616,[⟨3,0,5⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨19,6,(-13)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨18,7,(-11)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨17,8,(-9)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨16,9,(-7)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨15,9,(-6)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩]

def t7_303jobs1 : List Job := [⟨plan3616,[⟨3,1,4⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨18,6,(-12)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨17,7,(-10)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨16,8,(-8)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨15,9,(-6)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,2,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3616,[⟨3,1,5⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨16,6,(-10)⟩⟩]

def t7_303jobs2 : List Job := [⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩]

def t7_303jobs3 : List Job := [⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩]

def t7_303jobs4 : List Job := [⟨plan3616,[⟨3,2,3⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨14,7,(-7)⟩⟩]

def t7_303jobs5 : List Job := [⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨13,8,(-5)⟩⟩]

def t7_303jobs6 : List Job := [⟨plan3616,[⟨3,2,4⟩,⟨3,3,2⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩]

def t7_303jobs7 : List Job := [⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨13,6,(-7)⟩⟩]

def t7_303jobs8 : List Job := [⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩]

def t7_303jobs9 : List Job := [⟨plan3616,[⟨3,3,2⟩,⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨12,7,(-5)⟩⟩]

def t7_303jobs : List Job := t7_303jobs0++t7_303jobs1++t7_303jobs2++t7_303jobs3++t7_303jobs4++t7_303jobs5++t7_303jobs6++t7_303jobs7++t7_303jobs8++t7_303jobs9



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


