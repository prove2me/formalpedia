-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks160
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks160
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:41.741794+00:00
-- url     : https://prove2.me/theorems/8b005c5c-20bd-4173-996b-989de2b5ddac
-- title:
--   Endpoint22 Reach Checks160 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks160 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_163jobs5`, `ThreeBoundEndpoint22Reachable.t7_163jobs6`, `ThreeBoundEndpoint22Reachable.t7_163jobs7`, `ThreeBoundEndpoint22Reachable.t7_163jobs8`, `ThreeBoundEndpoint22Reachable.t7_163jobs9`, `ThreeBoundEndpoint22Reachable.t7_163jobs`, `ThreeBoundEndpoint22Reachable.t7_161jobs1`, `ThreeBoundEndpoint22Reachable.t7_161jobs2`, `ThreeBoundEndpoint22Reachable.t7_161jobs3`, `ThreeBoundEndpoint22Reachable.t7_161root`, `ThreeBoundEndpoint22Reachable.t7_161jobs`, `ThreeBoundEndpoint22Reachable.t7_161jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks160.lean, lines 1–72.

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

def t7_161root : Job := ⟨plan8494,[],none,⟨21,6,0⟩⟩
def t7_161jobs0 : List Job := [⟨plan6143,[⟨2,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-7)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-6)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-5)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-4)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6143,[⟨2,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-8)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-5)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6143,[⟨2,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-5)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-4)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-3)⟩⟩]

def t7_161jobs1 : List Job := [⟨plan6143,[⟨2,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6143,[⟨2,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-7)⟩⟩]

def t7_161jobs2 : List Job := [⟨plan6143,[⟨2,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-4)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-5)⟩⟩,⟨plan6143,[⟨2,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-8)⟩⟩]

def t7_161jobs3 : List Job := [⟨plan6143,[⟨2,2,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-8)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-5)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-6)⟩⟩,⟨plan6143,[⟨2,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-7)⟩⟩]

def t7_161jobs : List Job := t7_161jobs0++t7_161jobs1++t7_161jobs2++t7_161jobs3




def t7_162root : Job := ⟨plan8495,[],none,⟨21,6,0⟩⟩
def t7_162jobs0 : List Job := [⟨plan8126,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8126,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8126,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8126,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_162jobs1 : List Job := [⟨plan8126,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_162jobs2 : List Job := [⟨plan8126,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_162jobs : List Job := t7_162jobs0++t7_162jobs1++t7_162jobs2




def t7_163root : Job := ⟨plan8496,[],none,⟨21,6,0⟩⟩
def t7_163jobs0 : List Job := [⟨plan6146,[⟨2,0,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨21,6,(-8)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨20,6,(-7)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨19,6,(-6)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨18,6,(-5)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6146,[⟨2,0,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-7)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-6)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-5)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-4)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6146,[⟨2,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-8)⟩⟩]

def t7_163jobs1 : List Job := [⟨plan6146,[⟨2,1,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨17,6,(-5)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6146,[⟨2,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-5)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-4)⟩⟩]

def t7_163jobs2 : List Job := [⟨plan6146,[⟨2,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-3)⟩⟩]

def t7_163jobs3 : List Job := [⟨plan6146,[⟨2,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6146,[⟨2,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩,⟨plan6146,[⟨2,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6146,[⟨2,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-7)⟩⟩]

def t7_163jobs4 : List Job := [⟨plan6146,[⟨2,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6146,[⟨2,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-6)⟩⟩]

def t7_163jobs5 : List Job := [⟨plan6146,[⟨2,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-7)⟩⟩]

def t7_163jobs6 : List Job := [⟨plan6146,[⟨2,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-4)⟩⟩]

def t7_163jobs7 : List Job := [⟨plan6146,[⟨2,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-5)⟩⟩,⟨plan6146,[⟨2,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-8)⟩⟩]

def t7_163jobs8 : List Job := [⟨plan6146,[⟨2,2,4⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨17,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-7)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-8)⟩⟩]

def t7_163jobs9 : List Job := [⟨plan6146,[⟨2,2,4⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨16,6,(-5)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-6)⟩⟩,⟨plan6146,[⟨2,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-7)⟩⟩]

def t7_163jobs : List Job := t7_163jobs0++t7_163jobs1++t7_163jobs2++t7_163jobs3++t7_163jobs4++t7_163jobs5++t7_163jobs6++t7_163jobs7++t7_163jobs8++t7_163jobs9



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


