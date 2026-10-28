-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks162
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks162
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:54.844582+00:00
-- url     : https://prove2.me/theorems/51d31b73-8a3d-4175-97e7-242f9fd42194
-- title:
--   Endpoint22 Reach Checks162 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks162 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_168jobs`, `ThreeBoundEndpoint22Reachable.t7_169root`, `ThreeBoundEndpoint22Reachable.t7_169jobs0`, `ThreeBoundEndpoint22Reachable.t7_169jobs`, `ThreeBoundEndpoint22Reachable.t7_170root`, `ThreeBoundEndpoint22Reachable.t7_170jobs0`, `ThreeBoundEndpoint22Reachable.t7_170jobs`, `ThreeBoundEndpoint22Reachable.t7_171root`, `ThreeBoundEndpoint22Reachable.t7_171jobs0`, `ThreeBoundEndpoint22Reachable.t7_171jobs1`, `ThreeBoundEndpoint22Reachable.t7_171jobs`, `ThreeBoundEndpoint22Reachable.t7_172root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks162.lean, lines 1–104.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

def t7_167root : Job := ⟨plan8500,[],none,⟨21,6,0⟩⟩
def t7_167jobs0 : List Job := [⟨plan6151,[⟨2,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨21,6,(-8)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,6,(-7)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,6,(-6)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,6,(-5)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6151,[⟨2,0,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-7)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-6)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-5)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-4)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6151,[⟨2,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-8)⟩⟩]

def t7_167jobs1 : List Job := [⟨plan6151,[⟨2,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-5)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6151,[⟨2,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-5)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-4)⟩⟩]

def t7_167jobs2 : List Job := [⟨plan6151,[⟨2,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-3)⟩⟩]

def t7_167jobs3 : List Job := [⟨plan6151,[⟨2,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6151,[⟨2,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩,⟨plan6151,[⟨2,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6151,[⟨2,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-7)⟩⟩]

def t7_167jobs4 : List Job := [⟨plan6151,[⟨2,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6151,[⟨2,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-6)⟩⟩]

def t7_167jobs5 : List Job := [⟨plan6151,[⟨2,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-7)⟩⟩]

def t7_167jobs6 : List Job := [⟨plan6151,[⟨2,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-4)⟩⟩]

def t7_167jobs7 : List Job := [⟨plan6151,[⟨2,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-5)⟩⟩,⟨plan6151,[⟨2,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-8)⟩⟩]

def t7_167jobs8 : List Job := [⟨plan6151,[⟨2,2,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-8)⟩⟩]

def t7_167jobs9 : List Job := [⟨plan6151,[⟨2,2,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-5)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-6)⟩⟩,⟨plan6151,[⟨2,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-7)⟩⟩]

def t7_167jobs : List Job := t7_167jobs0++t7_167jobs1++t7_167jobs2++t7_167jobs3++t7_167jobs4++t7_167jobs5++t7_167jobs6++t7_167jobs7++t7_167jobs8++t7_167jobs9




def t7_168root : Job := ⟨plan8501,[],none,⟨21,6,0⟩⟩
def t7_168jobs0 : List Job := [⟨plan6152,[⟨2,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-7)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-6)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-5)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-4)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6152,[⟨2,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-8)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-5)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6152,[⟨2,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-5)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-4)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-3)⟩⟩]

def t7_168jobs1 : List Job := [⟨plan6152,[⟨2,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6152,[⟨2,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-7)⟩⟩]

def t7_168jobs2 : List Job := [⟨plan6152,[⟨2,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-4)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-5)⟩⟩,⟨plan6152,[⟨2,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-8)⟩⟩]

def t7_168jobs3 : List Job := [⟨plan6152,[⟨2,2,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-8)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-5)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-6)⟩⟩,⟨plan6152,[⟨2,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-7)⟩⟩]

def t7_168jobs : List Job := t7_168jobs0++t7_168jobs1++t7_168jobs2++t7_168jobs3




def t7_169root : Job := ⟨plan8502,[],none,⟨21,6,0⟩⟩
def t7_169jobs0 : List Job := [⟨plan8502,[],none,⟨21,6,0⟩⟩]

def t7_169jobs : List Job := t7_169jobs0




def t7_170root : Job := ⟨plan8604,[],none,⟨21,10,0⟩⟩
def t7_170jobs0 : List Job := [⟨plan8604,[],none,⟨21,10,0⟩⟩]

def t7_170jobs : List Job := t7_170jobs0




def t7_171root : Job := ⟨plan8605,[],none,⟨21,10,0⟩⟩
def t7_171jobs0 : List Job := [⟨plan8181,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8181,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8181,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩,⟨plan8181,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_171jobs1 : List Job := [⟨plan8181,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_171jobs : List Job := t7_171jobs0++t7_171jobs1




def t7_172root : Job := ⟨plan8606,[],none,⟨21,10,0⟩⟩
def t7_172jobs0 : List Job := [⟨plan8606,[],none,⟨21,10,0⟩⟩]

def t7_172jobs : List Job := t7_172jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


