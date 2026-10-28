-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks124
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks124
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:37.89189+00:00
-- url     : https://prove2.me/theorems/e1574756-16f9-4789-9fb9-c78e9886e8c7
-- title:
--   Endpoint22 Reach Checks124 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks124 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1194jobs2`, `ThreeBoundEndpoint22Reachable.t6_1194jobs3`, `ThreeBoundEndpoint22Reachable.t6_1194jobs4`, `ThreeBoundEndpoint22Reachable.t6_1194jobs`, `ThreeBoundEndpoint22Reachable.t6_1192jobs1`, `ThreeBoundEndpoint22Reachable.t6_1192jobs2`, `ThreeBoundEndpoint22Reachable.t6_1192jobs3`, `ThreeBoundEndpoint22Reachable.t6_1192jobs4`, `ThreeBoundEndpoint22Reachable.t6_1192root`, `ThreeBoundEndpoint22Reachable.t6_1192jobs5`, `ThreeBoundEndpoint22Reachable.t6_1192jobs0`, `ThreeBoundEndpoint22Reachable.t6_1192jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks124.lean, lines 1–68.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
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

def t6_1192root : Job := ⟨plan6645,[],none,⟨15,3,0⟩⟩
def t6_1192jobs0 : List Job := [⟨plan3307,[⟨5,0,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,1,(-5)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,1,(-5)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-3)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,1,(-5)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,(-2)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-3)⟩⟩,⟨plan3307,[⟨5,0,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-4)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,2,(-3)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,2,(-3)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,2,(-2)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,2,(-3)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,2,0⟩⟩]

def t6_1192jobs1 : List Job := [⟨plan3307,[⟨5,1,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,2,(-1)⟩⟩,⟨plan3307,[⟨5,1,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,2,(-2)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,1,(-4)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,1,(-2)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,1,(-4)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,1,(-1)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,1,(-2)⟩⟩,⟨plan3307,[⟨5,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,1,(-3)⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,3,(-1)⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,3,0⟩⟩]

def t6_1192jobs2 : List Job := [⟨plan3307,[⟨5,2,0⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,3,(-1)⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,3,1⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,0⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-1)⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,2⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,1⟩⟩,⟨plan3307,[⟨5,2,0⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,0⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,2,(-2)⟩⟩]

def t6_1192jobs3 : List Job := [⟨plan3307,[⟨5,2,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,2,(-2)⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,2,0⟩⟩]

def t6_1192jobs4 : List Job := [⟨plan3307,[⟨5,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,2,(-1)⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,2,(-2)⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,2,1⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,2,0⟩⟩,⟨plan3307,[⟨5,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,2,(-1)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_1192jobs5 : List Job := [⟨plan3307,[⟨5,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,1,(-3)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,1,(-1)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,1,(-3)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,1,0⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,1,(-1)⟩⟩,⟨plan3307,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,1,(-2)⟩⟩]

def t6_1192jobs : List Job := t6_1192jobs0++t6_1192jobs1++t6_1192jobs2++t6_1192jobs3++t6_1192jobs4++t6_1192jobs5




def t6_1193root : Job := ⟨plan6646,[],none,⟨15,3,0⟩⟩
def t6_1193jobs0 : List Job := [⟨plan5482,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5482,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,0⟩⟩,⟨plan5482,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1193jobs1 : List Job := [⟨plan5482,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,2⟩⟩]

def t6_1193jobs2 : List Job := [⟨plan5482,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,1⟩⟩]

def t6_1193jobs3 : List Job := [⟨plan5482,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,0⟩⟩]

def t6_1193jobs : List Job := t6_1193jobs0++t6_1193jobs1++t6_1193jobs2++t6_1193jobs3




def t6_1194root : Job := ⟨plan6647,[],none,⟨15,3,0⟩⟩
def t6_1194jobs0 : List Job := [⟨plan3309,[⟨5,0,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,1,(-5)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,1,(-5)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,1,(-5)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨5,0,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,1,(-4)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,2,(-3)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,2,(-3)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,2,(-2)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,2,(-3)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,2,0⟩⟩]

def t6_1194jobs1 : List Job := [⟨plan3309,[⟨5,1,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,2,(-1)⟩⟩,⟨plan3309,[⟨5,1,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,2,(-2)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,1,(-4)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,1,(-4)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,1,(-1)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,1,(-2)⟩⟩,⟨plan3309,[⟨5,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,1,(-3)⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,3,(-1)⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,3,0⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,3,(-1)⟩⟩]

def t6_1194jobs2 : List Job := [⟨plan3309,[⟨5,2,0⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,3,1⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,0⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-1)⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,3,2⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,1⟩⟩,⟨plan3309,[⟨5,2,0⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,0⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,2,(-2)⟩⟩]

def t6_1194jobs3 : List Job := [⟨plan3309,[⟨5,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,2,0⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,2,(-1)⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,2,(-2)⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,2,1⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,2,0⟩⟩,⟨plan3309,[⟨5,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,2,(-1)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_1194jobs4 : List Job := [⟨plan3309,[⟨5,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨11,1,(-1)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,1,(-3)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨10,1,0⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,1,(-1)⟩⟩,⟨plan3309,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,1,(-2)⟩⟩]

def t6_1194jobs : List Job := t6_1194jobs0++t6_1194jobs1++t6_1194jobs2++t6_1194jobs3++t6_1194jobs4



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


