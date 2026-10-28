-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks130
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks130
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:51.520215+00:00
-- url     : https://prove2.me/theorems/1f613a1e-9dcb-4b0d-bd1b-06f006fdb4a4
-- title:
--   Endpoint22 Reach Checks130 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks130 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1214jobs1`, `ThreeBoundEndpoint22Reachable.t6_1214jobs2`, `ThreeBoundEndpoint22Reachable.t6_1211jobs1`, `ThreeBoundEndpoint22Reachable.t6_1214jobs3`, `ThreeBoundEndpoint22Reachable.t6_1214jobs4`, `ThreeBoundEndpoint22Reachable.t6_1214jobs5`, `ThreeBoundEndpoint22Reachable.t6_1214jobs6`, `ThreeBoundEndpoint22Reachable.t6_1214jobs`, `ThreeBoundEndpoint22Reachable.t6_1211jobs2`, `ThreeBoundEndpoint22Reachable.t6_1211jobs3`, `ThreeBoundEndpoint22Reachable.t6_1211jobs`, `ThreeBoundEndpoint22Reachable.t6_1212root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks130.lean, lines 1–85.

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

def t6_1211root : Job := ⟨plan7534,[],none,⟨15,10,0⟩⟩
def t6_1211jobs0 : List Job := [⟨plan3479,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3479,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3479,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3479,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3479,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩]

def t6_1211jobs1 : List Job := [⟨plan3479,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3479,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3479,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,8,(-5)⟩⟩,⟨plan3479,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,8,(-4)⟩⟩,⟨plan3479,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,8,(-3)⟩⟩]

def t6_1211jobs2 : List Job := [⟨plan3479,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3479,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,7,(-5)⟩⟩]

def t6_1211jobs3 : List Job := [⟨plan3479,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3479,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,7,(-3)⟩⟩]

def t6_1211jobs : List Job := t6_1211jobs0++t6_1211jobs1++t6_1211jobs2++t6_1211jobs3




def t6_1212root : Job := ⟨plan7535,[],none,⟨15,10,0⟩⟩
def t6_1212jobs0 : List Job := [⟨plan7535,[],none,⟨15,10,0⟩⟩]

def t6_1212jobs : List Job := t6_1212jobs0




def t6_1213root : Job := ⟨plan7536,[],none,⟨15,10,0⟩⟩
def t6_1213jobs0 : List Job := [⟨plan3481,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3481,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3481,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3481,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3481,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩]

def t6_1213jobs1 : List Job := [⟨plan3481,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3481,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩]

def t6_1213jobs2 : List Job := [⟨plan3481,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3481,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3481,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,8,(-5)⟩⟩,⟨plan3481,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,8,(-4)⟩⟩]

def t6_1213jobs3 : List Job := [⟨plan3481,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,8,(-3)⟩⟩]

def t6_1213jobs4 : List Job := [⟨plan3481,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3481,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,7,(-5)⟩⟩]

def t6_1213jobs5 : List Job := [⟨plan3481,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_1213jobs6 : List Job := [⟨plan3481,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,7,(-3)⟩⟩]

def t6_1213jobs : List Job := t6_1213jobs0++t6_1213jobs1++t6_1213jobs2++t6_1213jobs3++t6_1213jobs4++t6_1213jobs5++t6_1213jobs6




def t6_1214root : Job := ⟨plan7537,[],none,⟨15,10,0⟩⟩
def t6_1214jobs0 : List Job := [⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,2,(-12)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,2,(-11)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,2,(-11)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,2,(-10)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,2,(-10)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,2,(-9)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,0,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,3,(-10)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,4,(-8)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,5,(-6)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,6,(-4)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,6,(-3)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨11,3,(-8)⟩⟩]

def t6_1214jobs1 : List Job := [⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨10,3,(-7)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,6,(-2)⟩⟩,⟨plan1604,[⟨5,1,3⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,5,(-3)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,2,(-12)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,2,(-11)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,2,(-11)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,2,(-10)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,2,(-10)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,2,(-9)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩]

def t6_1214jobs2 : List Job := [⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨11,2,(-9)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨10,2,(-8)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1604,[⟨5,1,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,4,(-8)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,5,(-6)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,6,(-4)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,7,(-2)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,6,(-3)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨11,4,(-7)⟩⟩]

def t6_1214jobs3 : List Job := [⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,6,(-3)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,7,(-1)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,6,(-2)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,6,(-2)⟩⟩]

def t6_1214jobs4 : List Job := [⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨8,5,(-3)⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,7,0⟩⟩,⟨plan1604,[⟨5,2,2⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨7,6,(-1)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,3,(-10)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,4,(-8)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,5,(-6)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,6,(-4)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,3,(-9)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,4,(-7)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,5,(-5)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,6,(-3)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,5,(-4)⟩⟩]

def t6_1214jobs5 : List Job := [⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨11,3,(-8)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,4,(-6)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨10,3,(-7)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,5,(-4)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,6,(-2)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,5,(-3)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨10,3,(-7)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,4,(-5)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨9,3,(-6)⟩⟩]

def t6_1214jobs6 : List Job := [⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,5,(-3)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨8,4,(-4)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,6,(-1)⟩⟩,⟨plan1604,[⟨5,2,3⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨7,5,(-2)⟩⟩]

def t6_1214jobs : List Job := t6_1214jobs0++t6_1214jobs1++t6_1214jobs2++t6_1214jobs3++t6_1214jobs4++t6_1214jobs5++t6_1214jobs6



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


