-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks077
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks077
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:41.011325+00:00
-- url     : https://prove2.me/theorems/d9167e83-89b5-4195-9aec-ad8018b70993
-- title:
--   Endpoint22 Reach Checks077 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks077 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_658jobs7`, `ThreeBoundEndpoint22Reachable.t6_658jobs8`, `ThreeBoundEndpoint22Reachable.t6_658jobs9`, `ThreeBoundEndpoint22Reachable.t6_658jobs10`, `ThreeBoundEndpoint22Reachable.t6_658jobs11`, `ThreeBoundEndpoint22Reachable.t6_658jobs12`, `ThreeBoundEndpoint22Reachable.t6_658jobs13`, `ThreeBoundEndpoint22Reachable.t6_658jobs14`, `ThreeBoundEndpoint22Reachable.t6_658jobs15`, `ThreeBoundEndpoint22Reachable.t6_658jobs16`, `ThreeBoundEndpoint22Reachable.t6_658jobs`, `ThreeBoundEndpoint22Reachable.t6_658jobs1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks077.lean, lines 1–54.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_658root : Job := ⟨plan6921,[],none,⟨15,6,0⟩⟩
def t6_658jobs0 : List Job := [⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨14,3,(-11)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨13,4,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨12,5,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨11,6,(-5)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩]

def t6_658jobs1 : List Job := [⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩]

def t6_658jobs2 : List Job := [⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩]

def t6_658jobs3 : List Job := [⟨plan1580,[⟨2,1,3⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨14,3,(-11)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨13,4,(-9)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨12,5,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨11,6,(-5)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,0,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,1,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩]

def t6_658jobs4 : List Job := [⟨plan1580,[⟨2,1,4⟩,⟨3,2,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩]

def t6_658jobs5 : List Job := [⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨3,3,1⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩]

def t6_658jobs6 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩]

def t6_658jobs7 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩]

def t6_658jobs8 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨8,5,(-3)⟩⟩]

def t6_658jobs9 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨7,6,(-1)⟩⟩]

def t6_658jobs10 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩]

def t6_658jobs11 : List Job := [⟨plan1580,[⟨2,2,3⟩,⟨3,0,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,1,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩]

def t6_658jobs12 : List Job := [⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩]

def t6_658jobs13 : List Job := [⟨plan1580,[⟨2,2,3⟩,⟨3,2,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,3,(-6)⟩⟩]

def t6_658jobs14 : List Job := [⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨8,3,(-5)⟩⟩]

def t6_658jobs15 : List Job := [⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨7,6,(-1)⟩⟩,⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,5,(-2)⟩⟩]

def t6_658jobs16 : List Job := [⟨plan1580,[⟨2,2,3⟩,⟨3,3,1⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨7,4,(-3)⟩⟩]

def t6_658jobs : List Job := t6_658jobs0++t6_658jobs1++t6_658jobs2++t6_658jobs3++t6_658jobs4++t6_658jobs5++t6_658jobs6++t6_658jobs7++t6_658jobs8++t6_658jobs9++t6_658jobs10++t6_658jobs11++t6_658jobs12++t6_658jobs13++t6_658jobs14++t6_658jobs15++t6_658jobs16



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


