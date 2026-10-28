-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks161
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks161
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:17.972299+00:00
-- url     : https://prove2.me/theorems/6beab309-da9a-4bb4-a78c-dde64893968d
-- title:
--   Endpoint22 Reach Checks161 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks161 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_166jobs3`, `ThreeBoundEndpoint22Reachable.t7_166jobs4`, `ThreeBoundEndpoint22Reachable.t7_166jobs5`, `ThreeBoundEndpoint22Reachable.t7_166jobs6`, `ThreeBoundEndpoint22Reachable.t7_166jobs`, `ThreeBoundEndpoint22Reachable.t7_164jobs1`, `ThreeBoundEndpoint22Reachable.t7_164jobs2`, `ThreeBoundEndpoint22Reachable.t7_164jobs3`, `ThreeBoundEndpoint22Reachable.t7_164jobs4`, `ThreeBoundEndpoint22Reachable.t7_164jobs5`, `ThreeBoundEndpoint22Reachable.t7_164jobs6`, `ThreeBoundEndpoint22Reachable.t7_164root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks161.lean, lines 1–74.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
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

def t7_164root : Job := ⟨plan8497,[],none,⟨21,6,0⟩⟩
def t7_164jobs0 : List Job := [⟨plan6147,[⟨2,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-7)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-6)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-5)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-4)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6147,[⟨2,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-8)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-5)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6147,[⟨2,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-5)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-4)⟩⟩]

def t7_164jobs1 : List Job := [⟨plan6147,[⟨2,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-3)⟩⟩]

def t7_164jobs2 : List Job := [⟨plan6147,[⟨2,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6147,[⟨2,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩,⟨plan6147,[⟨2,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6147,[⟨2,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-7)⟩⟩]

def t7_164jobs3 : List Job := [⟨plan6147,[⟨2,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6147,[⟨2,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-7)⟩⟩]

def t7_164jobs4 : List Job := [⟨plan6147,[⟨2,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-4)⟩⟩]

def t7_164jobs5 : List Job := [⟨plan6147,[⟨2,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-5)⟩⟩,⟨plan6147,[⟨2,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-8)⟩⟩]

def t7_164jobs6 : List Job := [⟨plan6147,[⟨2,2,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-8)⟩⟩]

def t7_164jobs7 : List Job := [⟨plan6147,[⟨2,2,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-5)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-6)⟩⟩,⟨plan6147,[⟨2,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-7)⟩⟩]

def t7_164jobs : List Job := t7_164jobs0++t7_164jobs1++t7_164jobs2++t7_164jobs3++t7_164jobs4++t7_164jobs5++t7_164jobs6++t7_164jobs7




def t7_165root : Job := ⟨plan8498,[],none,⟨21,6,0⟩⟩
def t7_165jobs0 : List Job := [⟨plan8130,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8130,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8130,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8130,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_165jobs1 : List Job := [⟨plan8130,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_165jobs2 : List Job := [⟨plan8130,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_165jobs : List Job := t7_165jobs0++t7_165jobs1++t7_165jobs2




def t7_166root : Job := ⟨plan8499,[],none,⟨21,6,0⟩⟩
def t7_166jobs0 : List Job := [⟨plan6150,[⟨2,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨21,6,(-8)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,6,(-7)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,6,(-6)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,6,(-5)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6150,[⟨2,0,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-7)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-6)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-5)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-4)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6150,[⟨2,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-7)⟩⟩]

def t7_166jobs1 : List Job := [⟨plan6150,[⟨2,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-8)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-5)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6150,[⟨2,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-5)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-4)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩]

def t7_166jobs2 : List Job := [⟨plan6150,[⟨2,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-3)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6150,[⟨2,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-7)⟩⟩]

def t7_166jobs3 : List Job := [⟨plan6150,[⟨2,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-7)⟩⟩]

def t7_166jobs4 : List Job := [⟨plan6150,[⟨2,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-4)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-5)⟩⟩,⟨plan6150,[⟨2,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-8)⟩⟩]

def t7_166jobs5 : List Job := [⟨plan6150,[⟨2,2,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-8)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-8)⟩⟩]

def t7_166jobs6 : List Job := [⟨plan6150,[⟨2,2,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-5)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-6)⟩⟩,⟨plan6150,[⟨2,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-7)⟩⟩]

def t7_166jobs : List Job := t7_166jobs0++t7_166jobs1++t7_166jobs2++t7_166jobs3++t7_166jobs4++t7_166jobs5++t7_166jobs6



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


