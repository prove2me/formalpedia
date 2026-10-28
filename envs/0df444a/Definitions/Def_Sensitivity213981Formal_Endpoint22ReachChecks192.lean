-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks192
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks192
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:39:36.530235+00:00
-- url     : https://prove2.me/theorems/46b553f6-dfea-4d3e-8ca0-e7fba0777ab6
-- title:
--   Endpoint22 Reach Checks192 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks192 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_656jobs`, `ThreeBoundEndpoint22Reachable.t7_657root`, `ThreeBoundEndpoint22Reachable.t7_657jobs0`, `ThreeBoundEndpoint22Reachable.t7_657jobs`, `ThreeBoundEndpoint22Reachable.t7_658root`, `ThreeBoundEndpoint22Reachable.t7_658jobs0`, `ThreeBoundEndpoint22Reachable.t7_658jobs`, `ThreeBoundEndpoint22Reachable.t7_659root`, `ThreeBoundEndpoint22Reachable.t7_659jobs0`, `ThreeBoundEndpoint22Reachable.t7_659jobs1`, `ThreeBoundEndpoint22Reachable.t7_659jobs2`, `ThreeBoundEndpoint22Reachable.t7_659jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks192.lean, lines 1–180.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
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

def t7_650root : Job := ⟨plan8702,[],none,⟨21,10,0⟩⟩
def t7_650jobs0 : List Job := [⟨plan6168,[⟨9,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨21,6,(-9)⟩⟩,⟨plan6168,[⟨9,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨20,6,(-8)⟩⟩,⟨plan6168,[⟨9,0,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨20,6,(-9)⟩⟩,⟨plan6168,[⟨9,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨19,6,(-7)⟩⟩,⟨plan6168,[⟨9,0,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,6,(-8)⟩⟩,⟨plan6168,[⟨9,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨18,6,(-6)⟩⟩,⟨plan6168,[⟨9,0,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,6,(-7)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨20,7,(-7)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,7,(-6)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨19,7,(-7)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,7,(-5)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,7,(-6)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,7,(-4)⟩⟩,⟨plan6168,[⟨9,1,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,7,(-5)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨20,6,(-8)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨19,6,(-7)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨19,6,(-8)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨18,6,(-6)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨18,6,(-7)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨17,6,(-5)⟩⟩,⟨plan6168,[⟨9,1,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨17,6,(-6)⟩⟩,⟨plan6168,[⟨9,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,8,(-5)⟩⟩,⟨plan6168,[⟨9,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,8,(-4)⟩⟩,⟨plan6168,[⟨9,2,2⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,8,(-5)⟩⟩]

def t7_650jobs1 : List Job := [⟨plan6168,[⟨9,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,8,(-3)⟩⟩,⟨plan6168,[⟨9,2,2⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,8,(-4)⟩⟩,⟨plan6168,[⟨9,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,8,(-2)⟩⟩,⟨plan6168,[⟨9,2,2⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,8,(-3)⟩⟩,⟨plan6168,[⟨9,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,7,(-6)⟩⟩,⟨plan6168,[⟨9,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,7,(-5)⟩⟩,⟨plan6168,[⟨9,2,3⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,7,(-6)⟩⟩]

def t7_650jobs2 : List Job := [⟨plan6168,[⟨9,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,7,(-4)⟩⟩,⟨plan6168,[⟨9,2,3⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,7,(-5)⟩⟩]

def t7_650jobs3 : List Job := [⟨plan6168,[⟨9,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,7,(-3)⟩⟩,⟨plan6168,[⟨9,2,3⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,7,(-4)⟩⟩,⟨plan6168,[⟨9,2,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨19,6,(-7)⟩⟩,⟨plan6168,[⟨9,2,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨18,6,(-6)⟩⟩,⟨plan6168,[⟨9,2,4⟩,⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨18,6,(-7)⟩⟩]

def t7_650jobs4 : List Job := [⟨plan6168,[⟨9,2,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨17,6,(-5)⟩⟩,⟨plan6168,[⟨9,2,4⟩,⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨17,6,(-6)⟩⟩]

def t7_650jobs5 : List Job := [⟨plan6168,[⟨9,2,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨16,6,(-4)⟩⟩,⟨plan6168,[⟨9,2,4⟩,⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨16,6,(-5)⟩⟩]

def t7_650jobs : List Job := t7_650jobs0++t7_650jobs1++t7_650jobs2++t7_650jobs3++t7_650jobs4++t7_650jobs5




def t7_651root : Job := ⟨plan8703,[],none,⟨21,10,0⟩⟩
def t7_651jobs0 : List Job := [⟨plan8176,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8176,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨20,7,(-2)⟩⟩,⟨plan8176,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,6,(-3)⟩⟩,⟨plan8176,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,8,0⟩⟩]

def t7_651jobs1 : List Job := [⟨plan8176,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,7,(-1)⟩⟩]

def t7_651jobs2 : List Job := [⟨plan8176,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,6,(-2)⟩⟩]

def t7_651jobs : List Job := t7_651jobs0++t7_651jobs1++t7_651jobs2




def t7_652root : Job := ⟨plan8704,[],none,⟨21,10,0⟩⟩
def t7_652jobs0 : List Job := [⟨plan8704,[],none,⟨21,10,0⟩⟩]

def t7_652jobs : List Job := t7_652jobs0




def t7_653root : Job := ⟨plan8921,[],none,⟨21,15,0⟩⟩
def t7_653jobs0 : List Job := [⟨plan8921,[],none,⟨21,15,0⟩⟩]

def t7_653jobs : List Job := t7_653jobs0




def t7_654root : Job := ⟨plan8922,[],none,⟨21,15,0⟩⟩
def t7_654jobs0 : List Job := [⟨plan8922,[],none,⟨21,15,0⟩⟩]

def t7_654jobs : List Job := t7_654jobs0




def t7_655root : Job := ⟨plan8923,[],none,⟨21,15,0⟩⟩
def t7_655jobs0 : List Job := [⟨plan8923,[],none,⟨21,15,0⟩⟩]

def t7_655jobs : List Job := t7_655jobs0




def t7_656root : Job := ⟨plan8924,[],none,⟨21,15,0⟩⟩
def t7_656jobs0 : List Job := [⟨plan8233,[⟨9,0,5⟩],(some ⟨9,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8233,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8233,[⟨9,1,5⟩],(some ⟨9,1,5⟩),⟨20,10,(-4)⟩⟩,⟨plan8233,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_656jobs1 : List Job := [⟨plan8233,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_656jobs : List Job := t7_656jobs0++t7_656jobs1




def t7_657root : Job := ⟨plan8925,[],none,⟨21,15,0⟩⟩
def t7_657jobs0 : List Job := [⟨plan8925,[],none,⟨21,15,0⟩⟩]

def t7_657jobs : List Job := t7_657jobs0




def t7_658root : Job := ⟨plan8926,[],none,⟨21,15,0⟩⟩
def t7_658jobs0 : List Job := [⟨plan8926,[],none,⟨21,15,0⟩⟩]

def t7_658jobs : List Job := t7_658jobs0




def t7_659root : Job := ⟨plan8927,[],none,⟨21,15,0⟩⟩
def t7_659jobs0 : List Job := [⟨plan8236,[⟨9,0,5⟩],(some ⟨9,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8236,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8236,[⟨9,1,5⟩],(some ⟨9,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_659jobs1 : List Job := [⟨plan8236,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_659jobs2 : List Job := [⟨plan8236,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_659jobs : List Job := t7_659jobs0++t7_659jobs1++t7_659jobs2




def t7_660root : Job := ⟨plan8928,[],none,⟨21,15,0⟩⟩
def t7_660jobs0 : List Job := [⟨plan8237,[⟨9,0,5⟩],(some ⟨9,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8237,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8237,[⟨9,1,5⟩],(some ⟨9,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_660jobs1 : List Job := [⟨plan8237,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_660jobs2 : List Job := [⟨plan8237,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_660jobs : List Job := t7_660jobs0++t7_660jobs1++t7_660jobs2




def t7_661root : Job := ⟨plan8929,[],none,⟨21,15,0⟩⟩
def t7_661jobs0 : List Job := [⟨plan8929,[],none,⟨21,15,0⟩⟩]

def t7_661jobs : List Job := t7_661jobs0




def t7_662root : Job := ⟨plan8930,[],none,⟨21,15,0⟩⟩
def t7_662jobs0 : List Job := [⟨plan8930,[],none,⟨21,15,0⟩⟩]

def t7_662jobs : List Job := t7_662jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


