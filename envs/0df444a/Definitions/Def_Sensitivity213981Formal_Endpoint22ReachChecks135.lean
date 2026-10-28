-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks135
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks135
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:05.662969+00:00
-- url     : https://prove2.me/theorems/370a3873-418e-4cc6-9741-ade791193fdd
-- title:
--   Endpoint22 Reach Checks135 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks135 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1333jobs1`, `ThreeBoundEndpoint22Reachable.t6_1333jobs2`, `ThreeBoundEndpoint22Reachable.t6_1333jobs3`, `ThreeBoundEndpoint22Reachable.t6_1333jobs4`, `ThreeBoundEndpoint22Reachable.t6_1333jobs`, `ThreeBoundEndpoint22Reachable.t6_1334root`, `ThreeBoundEndpoint22Reachable.t6_1334jobs0`, `ThreeBoundEndpoint22Reachable.t6_1334jobs`, `ThreeBoundEndpoint22Reachable.t6_1335root`, `ThreeBoundEndpoint22Reachable.t6_1335jobs0`, `ThreeBoundEndpoint22Reachable.t6_1335jobs`, `ThreeBoundEndpoint22Reachable.t6_1330jobs1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks135.lean, lines 1–104.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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

def t6_1330root : Job := ⟨plan7066,[],none,⟨15,6,0⟩⟩
def t6_1330jobs0 : List Job := [⟨plan3355,[⟨5,0,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,0,(-6)⟩⟩,⟨plan3355,[⟨5,0,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3355,[⟨5,0,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,0,(-5)⟩⟩,⟨plan3355,[⟨5,0,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3355,[⟨5,0,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3355,[⟨5,0,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3355,[⟨5,1,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3355,[⟨5,1,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3355,[⟨5,1,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3355,[⟨5,1,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,3,0⟩⟩,⟨plan3355,[⟨5,1,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3355,[⟨5,1,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,1,(-2)⟩⟩,⟨plan3355,[⟨5,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,0,(-5)⟩⟩,⟨plan3355,[⟨5,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3355,[⟨5,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3355,[⟨5,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3355,[⟨5,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3355,[⟨5,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,0,(-3)⟩⟩]

def t6_1330jobs1 : List Job := [⟨plan3355,[⟨5,2,1⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,2,(-2)⟩⟩,⟨plan3355,[⟨5,2,1⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,3,0⟩⟩,⟨plan3355,[⟨5,2,1⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,2,(-1)⟩⟩,⟨plan3355,[⟨5,2,1⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,4,2⟩⟩,⟨plan3355,[⟨5,2,1⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,3,1⟩⟩]

def t6_1330jobs2 : List Job := [⟨plan3355,[⟨5,2,1⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,2,0⟩⟩,⟨plan3355,[⟨5,2,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3355,[⟨5,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3355,[⟨5,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,1,(-2)⟩⟩,⟨plan3355,[⟨5,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,3,1⟩⟩]

def t6_1330jobs3 : List Job := [⟨plan3355,[⟨5,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,2,0⟩⟩,⟨plan3355,[⟨5,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,1,(-1)⟩⟩,⟨plan3355,[⟨5,2,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3355,[⟨5,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3355,[⟨5,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,0,(-3)⟩⟩]

def t6_1330jobs4 : List Job := [⟨plan3355,[⟨5,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,0⟩⟩,⟨plan3355,[⟨5,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3355,[⟨5,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,0,(-2)⟩⟩]

def t6_1330jobs : List Job := t6_1330jobs0++t6_1330jobs1++t6_1330jobs2++t6_1330jobs3++t6_1330jobs4




def t6_1331root : Job := ⟨plan7067,[],none,⟨15,6,0⟩⟩
def t6_1331jobs0 : List Job := [⟨plan5716,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5716,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5716,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-2)⟩⟩,⟨plan5716,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,1⟩⟩]

def t6_1331jobs1 : List Job := [⟨plan5716,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,0⟩⟩,⟨plan5716,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1331jobs : List Job := t6_1331jobs0++t6_1331jobs1




def t6_1332root : Job := ⟨plan7068,[],none,⟨15,6,0⟩⟩
def t6_1332jobs0 : List Job := [⟨plan3357,[⟨5,0,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,0,(-6)⟩⟩,⟨plan3357,[⟨5,0,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3357,[⟨5,0,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,0,(-5)⟩⟩,⟨plan3357,[⟨5,0,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3357,[⟨5,0,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3357,[⟨5,0,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3357,[⟨5,1,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3357,[⟨5,1,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3357,[⟨5,1,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3357,[⟨5,1,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,3,0⟩⟩,⟨plan3357,[⟨5,1,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3357,[⟨5,1,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,1,(-2)⟩⟩,⟨plan3357,[⟨5,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,0,(-5)⟩⟩,⟨plan3357,[⟨5,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3357,[⟨5,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,0,(-4)⟩⟩]

def t6_1332jobs1 : List Job := [⟨plan3357,[⟨5,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3357,[⟨5,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3357,[⟨5,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,0,(-3)⟩⟩,⟨plan3357,[⟨5,2,1⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,2,(-2)⟩⟩,⟨plan3357,[⟨5,2,1⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,3,0⟩⟩,⟨plan3357,[⟨5,2,1⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,2,(-1)⟩⟩,⟨plan3357,[⟨5,2,1⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,4,2⟩⟩]

def t6_1332jobs2 : List Job := [⟨plan3357,[⟨5,2,1⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,3,1⟩⟩,⟨plan3357,[⟨5,2,1⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,2,0⟩⟩,⟨plan3357,[⟨5,2,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3357,[⟨5,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3357,[⟨5,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,1,(-2)⟩⟩]

def t6_1332jobs3 : List Job := [⟨plan3357,[⟨5,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,3,1⟩⟩,⟨plan3357,[⟨5,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,2,0⟩⟩,⟨plan3357,[⟨5,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,1,(-1)⟩⟩,⟨plan3357,[⟨5,2,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3357,[⟨5,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_1332jobs4 : List Job := [⟨plan3357,[⟨5,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,0,(-3)⟩⟩,⟨plan3357,[⟨5,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,0⟩⟩,⟨plan3357,[⟨5,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3357,[⟨5,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,0,(-2)⟩⟩]

def t6_1332jobs : List Job := t6_1332jobs0++t6_1332jobs1++t6_1332jobs2++t6_1332jobs3++t6_1332jobs4




def t6_1333root : Job := ⟨plan7069,[],none,⟨15,6,0⟩⟩
def t6_1333jobs0 : List Job := [⟨plan3358,[⟨5,0,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,0,(-6)⟩⟩,⟨plan3358,[⟨5,0,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3358,[⟨5,0,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,0,(-5)⟩⟩,⟨plan3358,[⟨5,0,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3358,[⟨5,0,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3358,[⟨5,0,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3358,[⟨5,1,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,1,(-4)⟩⟩,⟨plan3358,[⟨5,1,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,2,(-2)⟩⟩,⟨plan3358,[⟨5,1,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3358,[⟨5,1,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,3,0⟩⟩,⟨plan3358,[⟨5,1,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3358,[⟨5,1,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,1,(-2)⟩⟩,⟨plan3358,[⟨5,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,0,(-5)⟩⟩,⟨plan3358,[⟨5,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3358,[⟨5,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3358,[⟨5,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3358,[⟨5,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3358,[⟨5,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,0,(-3)⟩⟩]

def t6_1333jobs1 : List Job := [⟨plan3358,[⟨5,2,1⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,2,(-2)⟩⟩,⟨plan3358,[⟨5,2,1⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,3,0⟩⟩,⟨plan3358,[⟨5,2,1⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,2,(-1)⟩⟩,⟨plan3358,[⟨5,2,1⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,4,2⟩⟩,⟨plan3358,[⟨5,2,1⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,3,1⟩⟩]

def t6_1333jobs2 : List Job := [⟨plan3358,[⟨5,2,1⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,2,0⟩⟩,⟨plan3358,[⟨5,2,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,1,(-3)⟩⟩,⟨plan3358,[⟨5,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,2,(-1)⟩⟩,⟨plan3358,[⟨5,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,1,(-2)⟩⟩,⟨plan3358,[⟨5,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,3,1⟩⟩]

def t6_1333jobs3 : List Job := [⟨plan3358,[⟨5,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,2,0⟩⟩,⟨plan3358,[⟨5,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,1,(-1)⟩⟩,⟨plan3358,[⟨5,2,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,0,(-4)⟩⟩,⟨plan3358,[⟨5,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3358,[⟨5,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,0,(-3)⟩⟩]

def t6_1333jobs4 : List Job := [⟨plan3358,[⟨5,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,0⟩⟩,⟨plan3358,[⟨5,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3358,[⟨5,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,0,(-2)⟩⟩]

def t6_1333jobs : List Job := t6_1333jobs0++t6_1333jobs1++t6_1333jobs2++t6_1333jobs3++t6_1333jobs4




def t6_1334root : Job := ⟨plan7070,[],none,⟨15,6,0⟩⟩
def t6_1334jobs0 : List Job := [⟨plan7070,[],none,⟨15,6,0⟩⟩]

def t6_1334jobs : List Job := t6_1334jobs0




def t6_1335root : Job := ⟨plan7570,[],none,⟨15,10,0⟩⟩
def t6_1335jobs0 : List Job := [⟨plan7570,[],none,⟨15,10,0⟩⟩]

def t6_1335jobs : List Job := t6_1335jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


