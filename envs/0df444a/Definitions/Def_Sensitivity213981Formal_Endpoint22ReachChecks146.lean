-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks146
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks146
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:21.048543+00:00
-- url     : https://prove2.me/theorems/e4fdc7ff-35dc-43f1-9d50-93b806d3eab2
-- title:
--   Endpoint22 Reach Checks146 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks146 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1681jobs2`, `ThreeBoundEndpoint22Reachable.t6_1683jobs3`, `ThreeBoundEndpoint22Reachable.t6_1683jobs4`, `ThreeBoundEndpoint22Reachable.t6_1683jobs5`, `ThreeBoundEndpoint22Reachable.t6_1681jobs3`, `ThreeBoundEndpoint22Reachable.t6_1683jobs`, `ThreeBoundEndpoint22Reachable.t6_1684root`, `ThreeBoundEndpoint22Reachable.t6_1684jobs0`, `ThreeBoundEndpoint22Reachable.t6_1684jobs1`, `ThreeBoundEndpoint22Reachable.t6_1684jobs`, `ThreeBoundEndpoint22Reachable.t6_1681jobs`, `ThreeBoundEndpoint22Reachable.t6_1685root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks146.lean, lines 1–95.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
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

def t6_1681root : Job := ⟨plan6686,[],none,⟨15,3,0⟩⟩
def t6_1681jobs0 : List Job := [⟨plan5482,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5482,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨14,2,0⟩⟩,⟨plan5482,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1681jobs1 : List Job := [⟨plan5482,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨13,3,2⟩⟩]

def t6_1681jobs2 : List Job := [⟨plan5482,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,1⟩⟩]

def t6_1681jobs3 : List Job := [⟨plan5482,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,0⟩⟩]

def t6_1681jobs : List Job := t6_1681jobs0++t6_1681jobs1++t6_1681jobs2++t6_1681jobs3




def t6_1682root : Job := ⟨plan6687,[],none,⟨15,3,0⟩⟩
def t6_1682jobs0 : List Job := [⟨plan3309,[⟨9,0,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,1,(-5)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,1,(-5)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,1,(-5)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨9,0,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-4)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,2,(-3)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,2,(-3)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,2,(-2)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,2,(-3)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,2,0⟩⟩]

def t6_1682jobs1 : List Job := [⟨plan3309,[⟨9,1,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,2,(-1)⟩⟩,⟨plan3309,[⟨9,1,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,2,(-2)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,1,(-4)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,1,(-4)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,1,(-1)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,1,(-2)⟩⟩,⟨plan3309,[⟨9,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,1,(-3)⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,3,(-1)⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,3,0⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,3,(-1)⟩⟩]

def t6_1682jobs2 : List Job := [⟨plan3309,[⟨9,2,0⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,3,1⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,0⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-1)⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,2⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,1⟩⟩,⟨plan3309,[⟨9,2,0⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,0⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,2,(-2)⟩⟩]

def t6_1682jobs3 : List Job := [⟨plan3309,[⟨9,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,2,0⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,2,(-1)⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,2,(-2)⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,2,1⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,2,0⟩⟩,⟨plan3309,[⟨9,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,2,(-1)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_1682jobs4 : List Job := [⟨plan3309,[⟨9,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,1,(-1)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,1,(-3)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,1,0⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,1,(-1)⟩⟩,⟨plan3309,[⟨9,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,1,(-2)⟩⟩]

def t6_1682jobs : List Job := t6_1682jobs0++t6_1682jobs1++t6_1682jobs2++t6_1682jobs3++t6_1682jobs4




def t6_1683root : Job := ⟨plan6688,[],none,⟨15,3,0⟩⟩
def t6_1683jobs0 : List Job := [⟨plan3310,[⟨9,0,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,1,(-5)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,1,(-5)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,1,(-5)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,(-2)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨9,0,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-4)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,2,(-3)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,2,(-3)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,2,(-2)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,2,(-3)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,2,0⟩⟩]

def t6_1683jobs1 : List Job := [⟨plan3310,[⟨9,1,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,2,(-1)⟩⟩,⟨plan3310,[⟨9,1,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,2,(-2)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,1,(-4)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,1,(-2)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,1,(-4)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,1,(-1)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,1,(-2)⟩⟩,⟨plan3310,[⟨9,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,1,(-3)⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,3,(-1)⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,3,0⟩⟩]

def t6_1683jobs2 : List Job := [⟨plan3310,[⟨9,2,0⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,3,(-1)⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,3,1⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,0⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-1)⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,2⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,1⟩⟩,⟨plan3310,[⟨9,2,0⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,0⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,2,(-2)⟩⟩]

def t6_1683jobs3 : List Job := [⟨plan3310,[⟨9,2,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,2,(-2)⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,2,0⟩⟩]

def t6_1683jobs4 : List Job := [⟨plan3310,[⟨9,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,2,(-1)⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,2,(-2)⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,2,1⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,2,0⟩⟩,⟨plan3310,[⟨9,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,2,(-1)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_1683jobs5 : List Job := [⟨plan3310,[⟨9,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,1,(-1)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,1,(-3)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,1,0⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,1,(-1)⟩⟩,⟨plan3310,[⟨9,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,1,(-2)⟩⟩]

def t6_1683jobs : List Job := t6_1683jobs0++t6_1683jobs1++t6_1683jobs2++t6_1683jobs3++t6_1683jobs4++t6_1683jobs5




def t6_1684root : Job := ⟨plan6689,[],none,⟨15,3,0⟩⟩
def t6_1684jobs0 : List Job := [⟨plan5485,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5485,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨14,2,0⟩⟩,⟨plan5485,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-1)⟩⟩,⟨plan5485,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨13,3,2⟩⟩]

def t6_1684jobs1 : List Job := [⟨plan5485,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,1⟩⟩,⟨plan5485,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,0⟩⟩]

def t6_1684jobs : List Job := t6_1684jobs0++t6_1684jobs1




def t6_1685root : Job := ⟨plan7127,[],none,⟨15,6,0⟩⟩
def t6_1685jobs0 : List Job := [⟨plan5622,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5622,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5622,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-2)⟩⟩,⟨plan5622,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,1⟩⟩,⟨plan5622,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,0⟩⟩]

def t6_1685jobs1 : List Job := [⟨plan5622,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1685jobs : List Job := t6_1685jobs0++t6_1685jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


