-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks019
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks019
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:20.100524+00:00
-- url     : https://prove2.me/theorems/c9de720b-6ce4-49b5-baef-d82f0b8efcb2
-- title:
--   Endpoint22 Reach Checks019 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks019 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_747jobs3`, `ThreeBoundEndpoint22Reachable.t5_747jobs`, `ThreeBoundEndpoint22Reachable.t5_748root`, `ThreeBoundEndpoint22Reachable.t5_748jobs0`, `ThreeBoundEndpoint22Reachable.t5_748jobs1`, `ThreeBoundEndpoint22Reachable.t5_748jobs`, `ThreeBoundEndpoint22Reachable.t5_749root`, `ThreeBoundEndpoint22Reachable.t5_749jobs0`, `ThreeBoundEndpoint22Reachable.t5_749jobs1`, `ThreeBoundEndpoint22Reachable.t5_749jobs2`, `ThreeBoundEndpoint22Reachable.t5_749jobs3`, `ThreeBoundEndpoint22Reachable.t5_749jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks019.lean, lines 1–129.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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

def t5_747root : Job := ⟨plan4274,[],none,⟨10,3,0⟩⟩
def t5_747jobs0 : List Job := [⟨plan2773,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2773,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_747jobs1 : List Job := [⟨plan2773,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_747jobs2 : List Job := [⟨plan2773,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_747jobs3 : List Job := [⟨plan2773,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_747jobs : List Job := t5_747jobs0++t5_747jobs1++t5_747jobs2++t5_747jobs3




def t5_748root : Job := ⟨plan4275,[],none,⟨10,3,0⟩⟩
def t5_748jobs0 : List Job := [⟨plan2774,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2774,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2774,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_748jobs1 : List Job := [⟨plan2774,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2774,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_748jobs : List Job := t5_748jobs0++t5_748jobs1




def t5_749root : Job := ⟨plan4276,[],none,⟨10,3,0⟩⟩
def t5_749jobs0 : List Job := [⟨plan2775,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2775,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_749jobs1 : List Job := [⟨plan2775,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_749jobs2 : List Job := [⟨plan2775,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_749jobs3 : List Job := [⟨plan2775,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_749jobs : List Job := t5_749jobs0++t5_749jobs1++t5_749jobs2++t5_749jobs3




def t5_750root : Job := ⟨plan4277,[],none,⟨10,3,0⟩⟩
def t5_750jobs0 : List Job := [⟨plan2776,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2776,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_750jobs1 : List Job := [⟨plan2776,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_750jobs2 : List Job := [⟨plan2776,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_750jobs3 : List Job := [⟨plan2776,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_750jobs : List Job := t5_750jobs0++t5_750jobs1++t5_750jobs2++t5_750jobs3




def t5_751root : Job := ⟨plan4278,[],none,⟨10,3,0⟩⟩
def t5_751jobs0 : List Job := [⟨plan2777,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2777,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2777,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2777,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_751jobs1 : List Job := [⟨plan2777,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_751jobs : List Job := t5_751jobs0++t5_751jobs1




def t5_752root : Job := ⟨plan3744,[],none,⟨10,0,0⟩⟩
def t5_752jobs0 : List Job := [⟨plan3744,[],none,⟨10,0,0⟩⟩]

def t5_752jobs : List Job := t5_752jobs0




def t5_753root : Job := ⟨plan3934,[],none,⟨10,1,0⟩⟩
def t5_753jobs0 : List Job := [⟨plan2648,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2648,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2648,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2648,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_753jobs1 : List Job := [⟨plan2648,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2648,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_753jobs : List Job := t5_753jobs0++t5_753jobs1




def t5_754root : Job := ⟨plan3935,[],none,⟨10,1,0⟩⟩
def t5_754jobs0 : List Job := [⟨plan2649,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2649,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2649,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_754jobs1 : List Job := [⟨plan2649,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2649,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩]

def t5_754jobs2 : List Job := [⟨plan2649,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_754jobs : List Job := t5_754jobs0++t5_754jobs1++t5_754jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


