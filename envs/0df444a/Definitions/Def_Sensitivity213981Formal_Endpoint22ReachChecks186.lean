-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks186
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks186
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:34:59.126632+00:00
-- url     : https://prove2.me/theorems/d0a2f3c5-751b-4155-913a-c71c669d6bbf
-- title:
--   Endpoint22 Reach Checks186 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks186 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_435jobs2`, `ThreeBoundEndpoint22Reachable.t7_438jobs4`, `ThreeBoundEndpoint22Reachable.t7_438jobs5`, `ThreeBoundEndpoint22Reachable.t7_438jobs`, `ThreeBoundEndpoint22Reachable.t7_439root`, `ThreeBoundEndpoint22Reachable.t7_439jobs0`, `ThreeBoundEndpoint22Reachable.t7_435jobs3`, `ThreeBoundEndpoint22Reachable.t7_439jobs1`, `ThreeBoundEndpoint22Reachable.t7_439jobs2`, `ThreeBoundEndpoint22Reachable.t7_439jobs`, `ThreeBoundEndpoint22Reachable.t7_440root`, `ThreeBoundEndpoint22Reachable.t7_440jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks186.lean, lines 1–150.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
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

def t7_435root : Job := ⟨plan8671,[],none,⟨21,10,0⟩⟩
def t7_435jobs0 : List Job := [⟨plan8172,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8172,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨20,7,(-2)⟩⟩,⟨plan8172,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,6,(-3)⟩⟩]

def t7_435jobs1 : List Job := [⟨plan8172,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨19,8,0⟩⟩]

def t7_435jobs2 : List Job := [⟨plan8172,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,7,(-1)⟩⟩]

def t7_435jobs3 : List Job := [⟨plan8172,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,6,(-2)⟩⟩]

def t7_435jobs : List Job := t7_435jobs0++t7_435jobs1++t7_435jobs2++t7_435jobs3




def t7_436root : Job := ⟨plan8672,[],none,⟨21,10,0⟩⟩
def t7_436jobs0 : List Job := [⟨plan8672,[],none,⟨21,10,0⟩⟩]

def t7_436jobs : List Job := t7_436jobs0




def t7_437root : Job := ⟨plan8673,[],none,⟨21,10,0⟩⟩
def t7_437jobs0 : List Job := [⟨plan6167,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨21,6,(-9)⟩⟩,⟨plan6167,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6167,[⟨5,0,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨20,6,(-9)⟩⟩,⟨plan6167,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6167,[⟨5,0,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6167,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6167,[⟨5,0,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨20,7,(-7)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,7,(-6)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨19,7,(-7)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,7,(-5)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,7,(-6)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,7,(-4)⟩⟩,⟨plan6167,[⟨5,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,7,(-5)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨20,6,(-8)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨19,6,(-8)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6167,[⟨5,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6167,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,8,(-5)⟩⟩]

def t7_437jobs1 : List Job := [⟨plan6167,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,8,(-4)⟩⟩,⟨plan6167,[⟨5,2,2⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,8,(-5)⟩⟩,⟨plan6167,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,8,(-3)⟩⟩,⟨plan6167,[⟨5,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,8,(-4)⟩⟩,⟨plan6167,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,8,(-2)⟩⟩,⟨plan6167,[⟨5,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,8,(-3)⟩⟩,⟨plan6167,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,7,(-6)⟩⟩,⟨plan6167,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,7,(-5)⟩⟩,⟨plan6167,[⟨5,2,3⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,7,(-6)⟩⟩]

def t7_437jobs2 : List Job := [⟨plan6167,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,7,(-4)⟩⟩,⟨plan6167,[⟨5,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,7,(-5)⟩⟩,⟨plan6167,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,7,(-3)⟩⟩,⟨plan6167,[⟨5,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,7,(-4)⟩⟩,⟨plan6167,[⟨5,2,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,6,(-7)⟩⟩,⟨plan6167,[⟨5,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩]

def t7_437jobs3 : List Job := [⟨plan6167,[⟨5,2,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,6,(-7)⟩⟩,⟨plan6167,[⟨5,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6167,[⟨5,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6167,[⟨5,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6167,[⟨5,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩]

def t7_437jobs : List Job := t7_437jobs0++t7_437jobs1++t7_437jobs2++t7_437jobs3




def t7_438root : Job := ⟨plan8674,[],none,⟨21,10,0⟩⟩
def t7_438jobs0 : List Job := [⟨plan6168,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨21,6,(-9)⟩⟩,⟨plan6168,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6168,[⟨5,0,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨20,6,(-9)⟩⟩,⟨plan6168,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6168,[⟨5,0,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6168,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6168,[⟨5,0,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨20,7,(-7)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,7,(-6)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨19,7,(-7)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,7,(-5)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,7,(-6)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,7,(-4)⟩⟩,⟨plan6168,[⟨5,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,7,(-5)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨20,6,(-8)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨19,6,(-8)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6168,[⟨5,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6168,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,8,(-5)⟩⟩,⟨plan6168,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,8,(-4)⟩⟩,⟨plan6168,[⟨5,2,2⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,8,(-5)⟩⟩]

def t7_438jobs1 : List Job := [⟨plan6168,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,8,(-3)⟩⟩,⟨plan6168,[⟨5,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,8,(-4)⟩⟩,⟨plan6168,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,8,(-2)⟩⟩,⟨plan6168,[⟨5,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,8,(-3)⟩⟩,⟨plan6168,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,7,(-6)⟩⟩,⟨plan6168,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,7,(-5)⟩⟩,⟨plan6168,[⟨5,2,3⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,7,(-6)⟩⟩]

def t7_438jobs2 : List Job := [⟨plan6168,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,7,(-4)⟩⟩,⟨plan6168,[⟨5,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,7,(-5)⟩⟩]

def t7_438jobs3 : List Job := [⟨plan6168,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,7,(-3)⟩⟩,⟨plan6168,[⟨5,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,7,(-4)⟩⟩,⟨plan6168,[⟨5,2,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,6,(-7)⟩⟩,⟨plan6168,[⟨5,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6168,[⟨5,2,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,6,(-7)⟩⟩]

def t7_438jobs4 : List Job := [⟨plan6168,[⟨5,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6168,[⟨5,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩]

def t7_438jobs5 : List Job := [⟨plan6168,[⟨5,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6168,[⟨5,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩]

def t7_438jobs : List Job := t7_438jobs0++t7_438jobs1++t7_438jobs2++t7_438jobs3++t7_438jobs4++t7_438jobs5




def t7_439root : Job := ⟨plan8675,[],none,⟨21,10,0⟩⟩
def t7_439jobs0 : List Job := [⟨plan8176,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8176,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨20,7,(-2)⟩⟩,⟨plan8176,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,6,(-3)⟩⟩,⟨plan8176,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨19,8,0⟩⟩]

def t7_439jobs1 : List Job := [⟨plan8176,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,7,(-1)⟩⟩]

def t7_439jobs2 : List Job := [⟨plan8176,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,6,(-2)⟩⟩]

def t7_439jobs : List Job := t7_439jobs0++t7_439jobs1++t7_439jobs2




def t7_440root : Job := ⟨plan8676,[],none,⟨21,10,0⟩⟩
def t7_440jobs0 : List Job := [⟨plan8676,[],none,⟨21,10,0⟩⟩]

def t7_440jobs : List Job := t7_440jobs0




def t7_441root : Job := ⟨plan8866,[],none,⟨21,15,0⟩⟩
def t7_441jobs0 : List Job := [⟨plan8866,[],none,⟨21,15,0⟩⟩]

def t7_441jobs : List Job := t7_441jobs0




def t7_442root : Job := ⟨plan8867,[],none,⟨21,15,0⟩⟩
def t7_442jobs0 : List Job := [⟨plan8867,[],none,⟨21,15,0⟩⟩]

def t7_442jobs : List Job := t7_442jobs0




def t7_443root : Job := ⟨plan8868,[],none,⟨21,15,0⟩⟩
def t7_443jobs0 : List Job := [⟨plan8868,[],none,⟨21,15,0⟩⟩]

def t7_443jobs : List Job := t7_443jobs0




def t7_444root : Job := ⟨plan8869,[],none,⟨21,15,0⟩⟩
def t7_444jobs0 : List Job := [⟨plan8233,[⟨5,0,5⟩],(some ⟨5,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8233,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8233,[⟨5,1,5⟩],(some ⟨5,1,5⟩),⟨20,10,(-4)⟩⟩,⟨plan8233,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_444jobs1 : List Job := [⟨plan8233,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_444jobs : List Job := t7_444jobs0++t7_444jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


