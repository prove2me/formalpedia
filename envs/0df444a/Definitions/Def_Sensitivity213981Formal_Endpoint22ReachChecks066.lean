-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks066
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks066
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:34.514256+00:00
-- url     : https://prove2.me/theorems/35f8e72a-a122-461a-84f5-8526fd243697
-- title:
--   Endpoint22 Reach Checks066 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks066 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_599jobs1`, `ThreeBoundEndpoint22Reachable.t6_599jobs2`, `ThreeBoundEndpoint22Reachable.t6_599jobs3`, `ThreeBoundEndpoint22Reachable.t6_599jobs`, `ThreeBoundEndpoint22Reachable.t6_600root`, `ThreeBoundEndpoint22Reachable.t6_600jobs0`, `ThreeBoundEndpoint22Reachable.t6_600jobs1`, `ThreeBoundEndpoint22Reachable.t6_600jobs`, `ThreeBoundEndpoint22Reachable.t6_601root`, `ThreeBoundEndpoint22Reachable.t6_601jobs0`, `ThreeBoundEndpoint22Reachable.t6_601jobs`, `ThreeBoundEndpoint22Reachable.t6_602root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks066.lean, lines 1–190.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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

def t6_596root : Job := ⟨plan6890,[],none,⟨15,6,0⟩⟩
def t6_596jobs0 : List Job := [⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩]

def t6_596jobs1 : List Job := [⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1573,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩]

def t6_596jobs : List Job := t6_596jobs0++t6_596jobs1




def t6_597root : Job := ⟨plan6891,[],none,⟨15,6,0⟩⟩
def t6_597jobs0 : List Job := [⟨plan6891,[],none,⟨15,6,0⟩⟩]

def t6_597jobs : List Job := t6_597jobs0




def t6_598root : Job := ⟨plan6892,[],none,⟨15,6,0⟩⟩
def t6_598jobs0 : List Job := [⟨plan5597,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5597,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_598jobs1 : List Job := [⟨plan5597,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_598jobs2 : List Job := [⟨plan5597,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5597,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_598jobs : List Job := t6_598jobs0++t6_598jobs1++t6_598jobs2




def t6_599root : Job := ⟨plan6893,[],none,⟨15,6,0⟩⟩
def t6_599jobs0 : List Job := [⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨14,3,(-11)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨13,4,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨12,5,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨11,6,(-5)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩]

def t6_599jobs1 : List Job := [⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1580,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩]

def t6_599jobs2 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩]

def t6_599jobs3 : List Job := [⟨plan1580,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩]

def t6_599jobs : List Job := t6_599jobs0++t6_599jobs1++t6_599jobs2++t6_599jobs3




def t6_600root : Job := ⟨plan6894,[],none,⟨15,6,0⟩⟩
def t6_600jobs0 : List Job := [⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1581,[⟨2,0,4⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1581,[⟨2,1,3⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1581,[⟨2,1,4⟩,⟨2,2,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩]

def t6_600jobs1 : List Job := [⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1581,[⟨2,2,2⟩,⟨2,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩]

def t6_600jobs : List Job := t6_600jobs0++t6_600jobs1




def t6_601root : Job := ⟨plan6895,[],none,⟨15,6,0⟩⟩
def t6_601jobs0 : List Job := [⟨plan6895,[],none,⟨15,6,0⟩⟩]

def t6_601jobs : List Job := t6_601jobs0




def t6_602root : Job := ⟨plan6896,[],none,⟨15,6,0⟩⟩
def t6_602jobs0 : List Job := [⟨plan5601,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5601,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5601,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_602jobs1 : List Job := [⟨plan5601,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5601,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_602jobs : List Job := t6_602jobs0++t6_602jobs1




def t6_603root : Job := ⟨plan6305,[],none,⟨15,0,0⟩⟩
def t6_603jobs0 : List Job := [⟨plan6305,[],none,⟨15,0,0⟩⟩]

def t6_603jobs : List Job := t6_603jobs0




def t6_604root : Job := ⟨plan6383,[],none,⟨15,1,0⟩⟩
def t6_604jobs0 : List Job := [⟨plan6383,[],none,⟨15,1,0⟩⟩]

def t6_604jobs : List Job := t6_604jobs0




def t6_605root : Job := ⟨plan6384,[],none,⟨15,1,0⟩⟩
def t6_605jobs0 : List Job := [⟨plan5391,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5391,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩,⟨plan5391,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩,⟨plan5391,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩]

def t6_605jobs1 : List Job := [⟨plan5391,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5391,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_605jobs : List Job := t6_605jobs0++t6_605jobs1




def t6_606root : Job := ⟨plan6385,[],none,⟨15,1,0⟩⟩
def t6_606jobs0 : List Job := [⟨plan6385,[],none,⟨15,1,0⟩⟩]

def t6_606jobs : List Job := t6_606jobs0




def t6_607root : Job := ⟨plan6570,[],none,⟨15,3,0⟩⟩
def t6_607jobs0 : List Job := [⟨plan6570,[],none,⟨15,3,0⟩⟩]

def t6_607jobs : List Job := t6_607jobs0




def t6_608root : Job := ⟨plan6571,[],none,⟨15,3,0⟩⟩
def t6_608jobs0 : List Job := [⟨plan5474,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5474,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5474,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_608jobs1 : List Job := [⟨plan5474,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_608jobs2 : List Job := [⟨plan5474,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5474,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_608jobs : List Job := t6_608jobs0++t6_608jobs1++t6_608jobs2




def t6_609root : Job := ⟨plan6572,[],none,⟨15,3,0⟩⟩
def t6_609jobs0 : List Job := [⟨plan6572,[],none,⟨15,3,0⟩⟩]

def t6_609jobs : List Job := t6_609jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


