-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks187
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks187
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:35:09.409477+00:00
-- url     : https://prove2.me/theorems/6e576e4b-97e1-4052-a5a3-7bdaf9433e3d
-- title:
--   Endpoint22 Reach Checks187 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks187 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_454jobs`, `ThreeBoundEndpoint22Reachable.t7_455root`, `ThreeBoundEndpoint22Reachable.t7_455jobs0`, `ThreeBoundEndpoint22Reachable.t7_455jobs`, `ThreeBoundEndpoint22Reachable.t7_456root`, `ThreeBoundEndpoint22Reachable.t7_456jobs0`, `ThreeBoundEndpoint22Reachable.t7_456jobs`, `ThreeBoundEndpoint22Reachable.t7_457root`, `ThreeBoundEndpoint22Reachable.t7_457jobs0`, `ThreeBoundEndpoint22Reachable.t7_457jobs`, `ThreeBoundEndpoint22Reachable.t7_446root`, `ThreeBoundEndpoint22Reachable.t7_458root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks187.lean, lines 1–229.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
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

def t7_445root : Job := ⟨plan8870,[],none,⟨21,15,0⟩⟩
def t7_445jobs0 : List Job := [⟨plan8870,[],none,⟨21,15,0⟩⟩]

def t7_445jobs : List Job := t7_445jobs0




def t7_446root : Job := ⟨plan8871,[],none,⟨21,15,0⟩⟩
def t7_446jobs0 : List Job := [⟨plan8871,[],none,⟨21,15,0⟩⟩]

def t7_446jobs : List Job := t7_446jobs0




def t7_447root : Job := ⟨plan8872,[],none,⟨21,15,0⟩⟩
def t7_447jobs0 : List Job := [⟨plan8236,[⟨5,0,5⟩],(some ⟨5,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8236,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8236,[⟨5,1,5⟩],(some ⟨5,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_447jobs1 : List Job := [⟨plan8236,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_447jobs2 : List Job := [⟨plan8236,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_447jobs : List Job := t7_447jobs0++t7_447jobs1++t7_447jobs2




def t7_448root : Job := ⟨plan8873,[],none,⟨21,15,0⟩⟩
def t7_448jobs0 : List Job := [⟨plan8237,[⟨5,0,5⟩],(some ⟨5,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8237,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8237,[⟨5,1,5⟩],(some ⟨5,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_448jobs1 : List Job := [⟨plan8237,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_448jobs2 : List Job := [⟨plan8237,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_448jobs : List Job := t7_448jobs0++t7_448jobs1++t7_448jobs2




def t7_449root : Job := ⟨plan8874,[],none,⟨21,15,0⟩⟩
def t7_449jobs0 : List Job := [⟨plan8874,[],none,⟨21,15,0⟩⟩]

def t7_449jobs : List Job := t7_449jobs0




def t7_450root : Job := ⟨plan8875,[],none,⟨21,15,0⟩⟩
def t7_450jobs0 : List Job := [⟨plan8875,[],none,⟨21,15,0⟩⟩]

def t7_450jobs : List Job := t7_450jobs0




def t7_451root : Job := ⟨plan8876,[],none,⟨21,15,0⟩⟩
def t7_451jobs0 : List Job := [⟨plan8240,[⟨5,0,5⟩],(some ⟨5,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8240,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8240,[⟨5,1,5⟩],(some ⟨5,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_451jobs1 : List Job := [⟨plan8240,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_451jobs2 : List Job := [⟨plan8240,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_451jobs : List Job := t7_451jobs0++t7_451jobs1++t7_451jobs2




def t7_452root : Job := ⟨plan8877,[],none,⟨21,15,0⟩⟩
def t7_452jobs0 : List Job := [⟨plan8241,[⟨5,0,5⟩],(some ⟨5,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8241,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8241,[⟨5,1,5⟩],(some ⟨5,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_452jobs1 : List Job := [⟨plan8241,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_452jobs2 : List Job := [⟨plan8241,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_452jobs : List Job := t7_452jobs0++t7_452jobs1++t7_452jobs2




def t7_453root : Job := ⟨plan8878,[],none,⟨21,15,0⟩⟩
def t7_453jobs0 : List Job := [⟨plan8242,[⟨5,0,5⟩],(some ⟨5,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8242,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8242,[⟨5,1,5⟩],(some ⟨5,1,5⟩),⟨20,10,(-4)⟩⟩,⟨plan8242,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_453jobs1 : List Job := [⟨plan8242,[⟨5,2,4⟩],(some ⟨5,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_453jobs : List Job := t7_453jobs0++t7_453jobs1




def t7_454root : Job := ⟨plan8879,[],none,⟨21,15,0⟩⟩
def t7_454jobs0 : List Job := [⟨plan8879,[],none,⟨21,15,0⟩⟩]

def t7_454jobs : List Job := t7_454jobs0




def t7_455root : Job := ⟨plan8880,[],none,⟨21,15,0⟩⟩
def t7_455jobs0 : List Job := [⟨plan8880,[],none,⟨21,15,0⟩⟩]

def t7_455jobs : List Job := t7_455jobs0




def t7_456root : Job := ⟨plan8534,[],none,⟨21,6,0⟩⟩
def t7_456jobs0 : List Job := [⟨plan8534,[],none,⟨21,6,0⟩⟩]

def t7_456jobs : List Job := t7_456jobs0




def t7_457root : Job := ⟨plan8677,[],none,⟨21,10,0⟩⟩
def t7_457jobs0 : List Job := [⟨plan8677,[],none,⟨21,10,0⟩⟩]

def t7_457jobs : List Job := t7_457jobs0




def t7_458root : Job := ⟨plan8678,[],none,⟨21,10,0⟩⟩
def t7_458jobs0 : List Job := [⟨plan8678,[],none,⟨21,10,0⟩⟩]

def t7_458jobs : List Job := t7_458jobs0




def t7_459root : Job := ⟨plan8679,[],none,⟨21,10,0⟩⟩
def t7_459jobs0 : List Job := [⟨plan8679,[],none,⟨21,10,0⟩⟩]

def t7_459jobs : List Job := t7_459jobs0




def t7_460root : Job := ⟨plan8881,[],none,⟨21,15,0⟩⟩
def t7_460jobs0 : List Job := [⟨plan8881,[],none,⟨21,15,0⟩⟩]

def t7_460jobs : List Job := t7_460jobs0




def t7_461root : Job := ⟨plan8882,[],none,⟨21,15,0⟩⟩
def t7_461jobs0 : List Job := [⟨plan8882,[],none,⟨21,15,0⟩⟩]

def t7_461jobs : List Job := t7_461jobs0




def t7_462root : Job := ⟨plan8883,[],none,⟨21,15,0⟩⟩
def t7_462jobs0 : List Job := [⟨plan8883,[],none,⟨21,15,0⟩⟩]

def t7_462jobs : List Job := t7_462jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


