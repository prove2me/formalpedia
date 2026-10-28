-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks053
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks053
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:54.435388+00:00
-- url     : https://prove2.me/theorems/7be753e8-aafb-4133-bd57-da92f38bbb72
-- title:
--   Endpoint22 Reach Checks053 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks053 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_303root`, `ThreeBoundEndpoint22Reachable.t6_303jobs0`, `ThreeBoundEndpoint22Reachable.t6_303jobs1`, `ThreeBoundEndpoint22Reachable.t6_303jobs`, `ThreeBoundEndpoint22Reachable.t6_304root`, `ThreeBoundEndpoint22Reachable.t6_304jobs0`, `ThreeBoundEndpoint22Reachable.t6_304jobs`, `ThreeBoundEndpoint22Reachable.t6_305root`, `ThreeBoundEndpoint22Reachable.t6_305jobs0`, `ThreeBoundEndpoint22Reachable.t6_305jobs`, `ThreeBoundEndpoint22Reachable.t6_306root`, `ThreeBoundEndpoint22Reachable.t6_306jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks053.lean, lines 1–131.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
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

def t6_299root : Job := ⟨plan6507,[],none,⟨15,3,0⟩⟩
def t6_299jobs0 : List Job := [⟨plan3316,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3316,[⟨1,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_299jobs1 : List Job := [⟨plan3316,[⟨1,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3316,[⟨1,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_299jobs2 : List Job := [⟨plan3316,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩]

def t6_299jobs3 : List Job := [⟨plan3316,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3316,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩]

def t6_299jobs : List Job := t6_299jobs0++t6_299jobs1++t6_299jobs2++t6_299jobs3




def t6_300root : Job := ⟨plan6508,[],none,⟨15,3,0⟩⟩
def t6_300jobs0 : List Job := [⟨plan6508,[],none,⟨15,3,0⟩⟩]

def t6_300jobs : List Job := t6_300jobs0




def t6_301root : Job := ⟨plan6509,[],none,⟨15,3,0⟩⟩
def t6_301jobs0 : List Job := [⟨plan3318,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3318,[⟨1,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3318,[⟨1,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-6)⟩⟩]

def t6_301jobs1 : List Job := [⟨plan3318,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩]

def t6_301jobs2 : List Job := [⟨plan3318,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3318,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩]

def t6_301jobs : List Job := t6_301jobs0++t6_301jobs1++t6_301jobs2




def t6_302root : Job := ⟨plan6510,[],none,⟨15,3,0⟩⟩
def t6_302jobs0 : List Job := [⟨plan3319,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3319,[⟨1,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_302jobs1 : List Job := [⟨plan3319,[⟨1,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3319,[⟨1,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_302jobs2 : List Job := [⟨plan3319,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩]

def t6_302jobs3 : List Job := [⟨plan3319,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3319,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩]

def t6_302jobs : List Job := t6_302jobs0++t6_302jobs1++t6_302jobs2++t6_302jobs3




def t6_303root : Job := ⟨plan6511,[],none,⟨15,3,0⟩⟩
def t6_303jobs0 : List Job := [⟨plan3320,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3320,[⟨1,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3320,[⟨1,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_303jobs1 : List Job := [⟨plan3320,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3320,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩]

def t6_303jobs : List Job := t6_303jobs0++t6_303jobs1




def t6_304root : Job := ⟨plan6512,[],none,⟨15,3,0⟩⟩
def t6_304jobs0 : List Job := [⟨plan6512,[],none,⟨15,3,0⟩⟩]

def t6_304jobs : List Job := t6_304jobs0




def t6_305root : Job := ⟨plan6804,[],none,⟨15,6,0⟩⟩
def t6_305jobs0 : List Job := [⟨plan6804,[],none,⟨15,6,0⟩⟩]

def t6_305jobs : List Job := t6_305jobs0




def t6_306root : Job := ⟨plan6805,[],none,⟨15,6,0⟩⟩
def t6_306jobs0 : List Job := [⟨plan5633,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5633,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_306jobs1 : List Job := [⟨plan5633,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_306jobs : List Job := t6_306jobs0++t6_306jobs1




def t6_307root : Job := ⟨plan6806,[],none,⟨15,6,0⟩⟩
def t6_307jobs0 : List Job := [⟨plan6806,[],none,⟨15,6,0⟩⟩]

def t6_307jobs : List Job := t6_307jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


