-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks190
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks190
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:30.854997+00:00
-- url     : https://prove2.me/theorems/c1762503-ee18-459d-b203-efc2bec45f8e
-- title:
--   Endpoint22 Reach Checks190 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks190 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_642root`, `ThreeBoundEndpoint22Reachable.t7_642jobs0`, `ThreeBoundEndpoint22Reachable.t7_642jobs`, `ThreeBoundEndpoint22Reachable.t7_643root`, `ThreeBoundEndpoint22Reachable.t7_643jobs0`, `ThreeBoundEndpoint22Reachable.t7_643jobs`, `ThreeBoundEndpoint22Reachable.t7_644root`, `ThreeBoundEndpoint22Reachable.t7_644jobs0`, `ThreeBoundEndpoint22Reachable.t7_644jobs1`, `ThreeBoundEndpoint22Reachable.t7_644jobs2`, `ThreeBoundEndpoint22Reachable.t7_644jobs`, `ThreeBoundEndpoint22Reachable.t7_634root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks190.lean, lines 1–168.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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

def t7_633root : Job := ⟨plan8429,[],none,⟨21,1,0⟩⟩
def t7_633jobs0 : List Job := [⟨plan8429,[],none,⟨21,1,0⟩⟩]

def t7_633jobs : List Job := t7_633jobs0




def t7_634root : Job := ⟨plan8462,[],none,⟨21,3,0⟩⟩
def t7_634jobs0 : List Job := [⟨plan8462,[],none,⟨21,3,0⟩⟩]

def t7_634jobs : List Job := t7_634jobs0




def t7_635root : Job := ⟨plan8463,[],none,⟨21,3,0⟩⟩
def t7_635jobs0 : List Job := [⟨plan8089,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨21,1,(-2)⟩⟩,⟨plan8089,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨20,2,0⟩⟩,⟨plan8089,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨20,1,(-1)⟩⟩,⟨plan8089,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨19,3,2⟩⟩]

def t7_635jobs1 : List Job := [⟨plan8089,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨19,2,1⟩⟩,⟨plan8089,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,1,0⟩⟩]

def t7_635jobs : List Job := t7_635jobs0++t7_635jobs1




def t7_636root : Job := ⟨plan8464,[],none,⟨21,3,0⟩⟩
def t7_636jobs0 : List Job := [⟨plan8464,[],none,⟨21,3,0⟩⟩]

def t7_636jobs : List Job := t7_636jobs0




def t7_637root : Job := ⟨plan8540,[],none,⟨21,6,0⟩⟩
def t7_637jobs0 : List Job := [⟨plan8540,[],none,⟨21,6,0⟩⟩]

def t7_637jobs : List Job := t7_637jobs0




def t7_638root : Job := ⟨plan8541,[],none,⟨21,6,0⟩⟩
def t7_638jobs0 : List Job := [⟨plan8117,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8117,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨20,4,(-1)⟩⟩,⟨plan8117,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨20,3,(-2)⟩⟩,⟨plan8117,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨19,5,1⟩⟩]

def t7_638jobs1 : List Job := [⟨plan8117,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,4,0⟩⟩]

def t7_638jobs2 : List Job := [⟨plan8117,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,3,(-1)⟩⟩]

def t7_638jobs : List Job := t7_638jobs0++t7_638jobs1++t7_638jobs2




def t7_639root : Job := ⟨plan8542,[],none,⟨21,6,0⟩⟩
def t7_639jobs0 : List Job := [⟨plan8118,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8118,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨20,4,(-1)⟩⟩,⟨plan8118,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨20,3,(-2)⟩⟩,⟨plan8118,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨19,5,1⟩⟩,⟨plan8118,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,4,0⟩⟩]

def t7_639jobs1 : List Job := [⟨plan8118,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,3,(-1)⟩⟩]

def t7_639jobs : List Job := t7_639jobs0++t7_639jobs1




def t7_640root : Job := ⟨plan8543,[],none,⟨21,6,0⟩⟩
def t7_640jobs0 : List Job := [⟨plan8119,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8119,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨20,4,(-1)⟩⟩,⟨plan8119,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨20,3,(-2)⟩⟩]

def t7_640jobs1 : List Job := [⟨plan8119,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨19,5,1⟩⟩]

def t7_640jobs2 : List Job := [⟨plan8119,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,4,0⟩⟩]

def t7_640jobs3 : List Job := [⟨plan8119,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,3,(-1)⟩⟩]

def t7_640jobs : List Job := t7_640jobs0++t7_640jobs1++t7_640jobs2++t7_640jobs3




def t7_641root : Job := ⟨plan8544,[],none,⟨21,6,0⟩⟩
def t7_641jobs0 : List Job := [⟨plan8120,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8120,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨20,4,(-1)⟩⟩,⟨plan8120,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨20,3,(-2)⟩⟩,⟨plan8120,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨19,5,1⟩⟩]

def t7_641jobs1 : List Job := [⟨plan8120,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,4,0⟩⟩]

def t7_641jobs2 : List Job := [⟨plan8120,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,3,(-1)⟩⟩]

def t7_641jobs : List Job := t7_641jobs0++t7_641jobs1++t7_641jobs2




def t7_642root : Job := ⟨plan8545,[],none,⟨21,6,0⟩⟩
def t7_642jobs0 : List Job := [⟨plan8545,[],none,⟨21,6,0⟩⟩]

def t7_642jobs : List Job := t7_642jobs0




def t7_643root : Job := ⟨plan8695,[],none,⟨21,10,0⟩⟩
def t7_643jobs0 : List Job := [⟨plan8695,[],none,⟨21,10,0⟩⟩]

def t7_643jobs : List Job := t7_643jobs0




def t7_644root : Job := ⟨plan8696,[],none,⟨21,10,0⟩⟩
def t7_644jobs0 : List Job := [⟨plan8169,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8169,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨20,7,(-2)⟩⟩,⟨plan8169,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,6,(-3)⟩⟩,⟨plan8169,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨19,8,0⟩⟩]

def t7_644jobs1 : List Job := [⟨plan8169,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,7,(-1)⟩⟩]

def t7_644jobs2 : List Job := [⟨plan8169,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,6,(-2)⟩⟩]

def t7_644jobs : List Job := t7_644jobs0++t7_644jobs1++t7_644jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


