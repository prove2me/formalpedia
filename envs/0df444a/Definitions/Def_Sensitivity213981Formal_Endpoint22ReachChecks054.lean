-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks054
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks054
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:38.998773+00:00
-- url     : https://prove2.me/theorems/2a6105e4-2747-4f39-90bf-7a5104f49ea8
-- title:
--   Endpoint22 Reach Checks054 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks054 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_310root`, `ThreeBoundEndpoint22Reachable.t6_310jobs0`, `ThreeBoundEndpoint22Reachable.t6_310jobs`, `ThreeBoundEndpoint22Reachable.t6_311root`, `ThreeBoundEndpoint22Reachable.t6_311jobs0`, `ThreeBoundEndpoint22Reachable.t6_311jobs1`, `ThreeBoundEndpoint22Reachable.t6_311jobs2`, `ThreeBoundEndpoint22Reachable.t6_311jobs3`, `ThreeBoundEndpoint22Reachable.t6_311jobs4`, `ThreeBoundEndpoint22Reachable.t6_311jobs`, `ThreeBoundEndpoint22Reachable.t6_308jobs1`, `ThreeBoundEndpoint22Reachable.t6_308jobs2`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks054.lean, lines 1–75.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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

def t6_308root : Job := ⟨plan6807,[],none,⟨15,6,0⟩⟩
def t6_308jobs0 : List Job := [⟨plan3401,[⟨1,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,6,(-8)⟩⟩,⟨plan3401,[⟨1,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,6,(-7)⟩⟩,⟨plan3401,[⟨1,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3401,[⟨1,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,6,(-6)⟩⟩,⟨plan3401,[⟨1,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3401,[⟨1,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,6,(-5)⟩⟩,⟨plan3401,[⟨1,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3401,[⟨1,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,6,(-7)⟩⟩,⟨plan3401,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-6)⟩⟩,⟨plan3401,[⟨1,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3401,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-5)⟩⟩,⟨plan3401,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3401,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-4)⟩⟩]

def t6_308jobs1 : List Job := [⟨plan3401,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3401,[⟨1,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3401,[⟨1,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3401,[⟨1,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-8)⟩⟩]

def t6_308jobs2 : List Job := [⟨plan3401,[⟨1,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3401,[⟨1,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-7)⟩⟩]

def t6_308jobs3 : List Job := [⟨plan3401,[⟨1,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-5)⟩⟩,⟨plan3401,[⟨1,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-6)⟩⟩]

def t6_308jobs : List Job := t6_308jobs0++t6_308jobs1++t6_308jobs2++t6_308jobs3




def t6_309root : Job := ⟨plan6808,[],none,⟨15,6,0⟩⟩
def t6_309jobs0 : List Job := [⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨1,0,4⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩]

def t6_309jobs1 : List Job := [⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1573,[⟨1,1,3⟩,⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨13,3,(-10)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨12,4,(-8)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨11,5,(-6)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨10,6,(-4)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,5,(-5)⟩⟩]

def t6_309jobs2 : List Job := [⟨plan1573,[⟨1,1,4⟩,⟨3,1,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨12,3,(-9)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨11,4,(-7)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨10,5,(-5)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨9,6,(-3)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,2,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨11,3,(-8)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨10,4,(-6)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨9,5,(-4)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨9,4,(-5)⟩⟩]

def t6_309jobs3 : List Job := [⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨8,6,(-2)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1573,[⟨1,1,4⟩,⟨3,3,1⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨8,4,(-4)⟩⟩]

def t6_309jobs : List Job := t6_309jobs0++t6_309jobs1++t6_309jobs2++t6_309jobs3




def t6_310root : Job := ⟨plan6809,[],none,⟨15,6,0⟩⟩
def t6_310jobs0 : List Job := [⟨plan6809,[],none,⟨15,6,0⟩⟩]

def t6_310jobs : List Job := t6_310jobs0




def t6_311root : Job := ⟨plan6810,[],none,⟨15,6,0⟩⟩
def t6_311jobs0 : List Job := [⟨plan3404,[⟨1,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,6,(-8)⟩⟩,⟨plan3404,[⟨1,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,6,(-7)⟩⟩,⟨plan3404,[⟨1,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3404,[⟨1,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,6,(-6)⟩⟩,⟨plan3404,[⟨1,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3404,[⟨1,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,6,(-5)⟩⟩,⟨plan3404,[⟨1,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3404,[⟨1,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,6,(-7)⟩⟩,⟨plan3404,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-6)⟩⟩,⟨plan3404,[⟨1,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3404,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-5)⟩⟩]

def t6_311jobs1 : List Job := [⟨plan3404,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3404,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-4)⟩⟩]

def t6_311jobs2 : List Job := [⟨plan3404,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3404,[⟨1,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,6,(-8)⟩⟩]

def t6_311jobs3 : List Job := [⟨plan3404,[⟨1,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3404,[⟨1,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-8)⟩⟩,⟨plan3404,[⟨1,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3404,[⟨1,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-7)⟩⟩]

def t6_311jobs4 : List Job := [⟨plan3404,[⟨1,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,6,(-5)⟩⟩,⟨plan3404,[⟨1,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-6)⟩⟩]

def t6_311jobs : List Job := t6_311jobs0++t6_311jobs1++t6_311jobs2++t6_311jobs3++t6_311jobs4



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


