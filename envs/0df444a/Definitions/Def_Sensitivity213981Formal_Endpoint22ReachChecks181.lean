-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks181
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks181
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:40.865344+00:00
-- url     : https://prove2.me/theorems/7b825280-7493-4382-a8b1-0d1ac29096e1
-- title:
--   Endpoint22 Reach Checks181 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks181 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_317root`, `ThreeBoundEndpoint22Reachable.t7_317jobs0`, `ThreeBoundEndpoint22Reachable.t7_317jobs`, `ThreeBoundEndpoint22Reachable.t7_318root`, `ThreeBoundEndpoint22Reachable.t7_318jobs0`, `ThreeBoundEndpoint22Reachable.t7_318jobs`, `ThreeBoundEndpoint22Reachable.t7_319root`, `ThreeBoundEndpoint22Reachable.t7_319jobs0`, `ThreeBoundEndpoint22Reachable.t7_319jobs`, `ThreeBoundEndpoint22Reachable.t7_320root`, `ThreeBoundEndpoint22Reachable.t7_320jobs0`, `ThreeBoundEndpoint22Reachable.t7_320jobs1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks181.lean, lines 1–210.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
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

def t7_311root : Job := ⟨plan8652,[],none,⟨21,10,0⟩⟩
def t7_311jobs0 : List Job := [⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3618,[⟨3,1,4⟩,⟨3,3,3⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3618,[⟨3,1,5⟩,⟨3,3,2⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨17,6,(-11)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨16,7,(-9)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨15,8,(-7)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨14,9,(-5)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,2,4⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3618,[⟨3,2,3⟩,⟨3,3,3⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨16,6,(-10)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨15,7,(-8)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨14,8,(-6)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨14,7,(-7)⟩⟩]

def t7_311jobs1 : List Job := [⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨13,9,(-4)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3618,[⟨3,2,4⟩,⟨3,3,2⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨13,8,(-5)⟩⟩]

def t7_311jobs2 : List Job := [⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,2,4⟩],(some ⟨10,2,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3618,[⟨3,3,2⟩,⟨3,3,3⟩,⟨10,3,3⟩],(some ⟨10,3,3⟩),⟨12,7,(-5)⟩⟩]

def t7_311jobs : List Job := t7_311jobs0++t7_311jobs1++t7_311jobs2




def t7_312root : Job := ⟨plan8653,[],none,⟨21,10,0⟩⟩
def t7_312jobs0 : List Job := [⟨plan8653,[],none,⟨21,10,0⟩⟩]

def t7_312jobs : List Job := t7_312jobs0




def t7_313root : Job := ⟨plan8654,[],none,⟨21,10,0⟩⟩
def t7_313jobs0 : List Job := [⟨plan8654,[],none,⟨21,10,0⟩⟩]

def t7_313jobs : List Job := t7_313jobs0




def t7_314root : Job := ⟨plan8812,[],none,⟨21,15,0⟩⟩
def t7_314jobs0 : List Job := [⟨plan8812,[],none,⟨21,15,0⟩⟩]

def t7_314jobs : List Job := t7_314jobs0




def t7_315root : Job := ⟨plan8813,[],none,⟨21,15,0⟩⟩
def t7_315jobs0 : List Job := [⟨plan8813,[],none,⟨21,15,0⟩⟩]

def t7_315jobs : List Job := t7_315jobs0




def t7_316root : Job := ⟨plan8814,[],none,⟨21,15,0⟩⟩
def t7_316jobs0 : List Job := [⟨plan8814,[],none,⟨21,15,0⟩⟩]

def t7_316jobs : List Job := t7_316jobs0




def t7_317root : Job := ⟨plan8815,[],none,⟨21,15,0⟩⟩
def t7_317jobs0 : List Job := [⟨plan8815,[],none,⟨21,15,0⟩⟩]

def t7_317jobs : List Job := t7_317jobs0




def t7_318root : Job := ⟨plan8816,[],none,⟨21,15,0⟩⟩
def t7_318jobs0 : List Job := [⟨plan8816,[],none,⟨21,15,0⟩⟩]

def t7_318jobs : List Job := t7_318jobs0




def t7_319root : Job := ⟨plan8817,[],none,⟨21,15,0⟩⟩
def t7_319jobs0 : List Job := [⟨plan8817,[],none,⟨21,15,0⟩⟩]

def t7_319jobs : List Job := t7_319jobs0




def t7_320root : Job := ⟨plan8818,[],none,⟨21,15,0⟩⟩
def t7_320jobs0 : List Job := [⟨plan6216,[⟨3,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6216,[⟨3,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6216,[⟨3,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6216,[⟨3,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6216,[⟨3,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6216,[⟨3,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6216,[⟨3,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6216,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6216,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6216,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6216,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6216,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_320jobs1 : List Job := [⟨plan6216,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6216,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩,⟨plan6216,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩,⟨plan6216,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_320jobs : List Job := t7_320jobs0++t7_320jobs1




def t7_321root : Job := ⟨plan8819,[],none,⟨21,15,0⟩⟩
def t7_321jobs0 : List Job := [⟨plan8280,[⟨3,0,6⟩],(some ⟨3,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8280,[⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨20,15,(-5)⟩⟩,⟨plan8280,[⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_321jobs1 : List Job := [⟨plan8280,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,15,(-3)⟩⟩]

def t7_321jobs : List Job := t7_321jobs0++t7_321jobs1




def t7_322root : Job := ⟨plan8820,[],none,⟨21,15,0⟩⟩
def t7_322jobs0 : List Job := [⟨plan8820,[],none,⟨21,15,0⟩⟩]

def t7_322jobs : List Job := t7_322jobs0




def t7_323root : Job := ⟨plan8821,[],none,⟨21,15,0⟩⟩
def t7_323jobs0 : List Job := [⟨plan8821,[],none,⟨21,15,0⟩⟩]

def t7_323jobs : List Job := t7_323jobs0




def t7_324root : Job := ⟨plan8822,[],none,⟨21,15,0⟩⟩
def t7_324jobs0 : List Job := [⟨plan6220,[⟨3,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6220,[⟨3,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6220,[⟨3,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6220,[⟨3,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6220,[⟨3,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6220,[⟨3,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6220,[⟨3,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6220,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6220,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6220,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6220,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6220,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6220,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6220,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩]

def t7_324jobs1 : List Job := [⟨plan6220,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6220,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6220,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6220,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_324jobs2 : List Job := [⟨plan6220,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6220,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩]

def t7_324jobs3 : List Job := [⟨plan6220,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩,⟨plan6220,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_324jobs : List Job := t7_324jobs0++t7_324jobs1++t7_324jobs2++t7_324jobs3




def t7_325root : Job := ⟨plan8823,[],none,⟨21,15,0⟩⟩
def t7_325jobs0 : List Job := [⟨plan6221,[⟨3,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6221,[⟨3,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6221,[⟨3,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6221,[⟨3,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6221,[⟨3,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6221,[⟨3,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6221,[⟨3,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6221,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6221,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6221,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6221,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6221,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6221,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6221,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩]

def t7_325jobs1 : List Job := [⟨plan6221,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6221,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6221,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6221,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_325jobs2 : List Job := [⟨plan6221,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6221,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩]

def t7_325jobs3 : List Job := [⟨plan6221,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩,⟨plan6221,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_325jobs : List Job := t7_325jobs0++t7_325jobs1++t7_325jobs2++t7_325jobs3




def t7_326root : Job := ⟨plan8824,[],none,⟨21,15,0⟩⟩
def t7_326jobs0 : List Job := [⟨plan6222,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6222,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6222,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6222,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6222,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6222,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6222,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6222,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6222,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6222,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6222,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩,⟨plan6222,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩]

def t7_326jobs1 : List Job := [⟨plan6222,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩,⟨plan6222,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩,⟨plan6222,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_326jobs : List Job := t7_326jobs0++t7_326jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


