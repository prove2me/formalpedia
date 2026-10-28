-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks028
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks028
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:23:11.834511+00:00
-- url     : https://prove2.me/theorems/f4d6c1e7-971e-4663-a2f4-c5308a0895d8
-- title:
--   Endpoint22 Reach Checks028 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks028 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_882root`, `ThreeBoundEndpoint22Reachable.t5_882jobs0`, `ThreeBoundEndpoint22Reachable.t5_882jobs1`, `ThreeBoundEndpoint22Reachable.t5_882jobs2`, `ThreeBoundEndpoint22Reachable.t5_882jobs`, `ThreeBoundEndpoint22Reachable.t5_873jobs`, `ThreeBoundEndpoint22Reachable.t5_874root`, `ThreeBoundEndpoint22Reachable.t5_874jobs0`, `ThreeBoundEndpoint22Reachable.t5_874jobs1`, `ThreeBoundEndpoint22Reachable.t5_874jobs`, `ThreeBoundEndpoint22Reachable.t5_875root`, `ThreeBoundEndpoint22Reachable.t5_875jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks028.lean, lines 1–146.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

def t5_873root : Job := ⟨plan4309,[],none,⟨10,3,0⟩⟩
def t5_873jobs0 : List Job := [⟨plan2773,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2773,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2773,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_873jobs1 : List Job := [⟨plan2773,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2773,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩,⟨plan2773,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2773,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_873jobs : List Job := t5_873jobs0++t5_873jobs1




def t5_874root : Job := ⟨plan4310,[],none,⟨10,3,0⟩⟩
def t5_874jobs0 : List Job := [⟨plan2774,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2774,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2774,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_874jobs1 : List Job := [⟨plan2774,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2774,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩,⟨plan2774,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2774,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_874jobs : List Job := t5_874jobs0++t5_874jobs1




def t5_875root : Job := ⟨plan4311,[],none,⟨10,3,0⟩⟩
def t5_875jobs0 : List Job := [⟨plan2775,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2775,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_875jobs1 : List Job := [⟨plan2775,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_875jobs2 : List Job := [⟨plan2775,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2775,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_875jobs3 : List Job := [⟨plan2775,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2775,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_875jobs : List Job := t5_875jobs0++t5_875jobs1++t5_875jobs2++t5_875jobs3




def t5_876root : Job := ⟨plan4312,[],none,⟨10,3,0⟩⟩
def t5_876jobs0 : List Job := [⟨plan2776,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2776,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_876jobs1 : List Job := [⟨plan2776,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2776,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_876jobs2 : List Job := [⟨plan2776,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩,⟨plan2776,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2776,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_876jobs : List Job := t5_876jobs0++t5_876jobs1++t5_876jobs2




def t5_877root : Job := ⟨plan4313,[],none,⟨10,3,0⟩⟩
def t5_877jobs0 : List Job := [⟨plan4313,[],none,⟨10,3,0⟩⟩]

def t5_877jobs : List Job := t5_877jobs0




def t5_878root : Job := ⟨plan4733,[],none,⟨10,6,0⟩⟩
def t5_878jobs0 : List Job := [⟨plan4733,[],none,⟨10,6,0⟩⟩]

def t5_878jobs : List Job := t5_878jobs0




def t5_879root : Job := ⟨plan4734,[],none,⟨10,6,0⟩⟩
def t5_879jobs0 : List Job := [⟨plan3018,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3018,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩,⟨plan3018,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_879jobs1 : List Job := [⟨plan3018,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_879jobs : List Job := t5_879jobs0++t5_879jobs1




def t5_880root : Job := ⟨plan4735,[],none,⟨10,6,0⟩⟩
def t5_880jobs0 : List Job := [⟨plan4735,[],none,⟨10,6,0⟩⟩]

def t5_880jobs : List Job := t5_880jobs0




def t5_881root : Job := ⟨plan4736,[],none,⟨10,6,0⟩⟩
def t5_881jobs0 : List Job := [⟨plan3020,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3020,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_881jobs1 : List Job := [⟨plan3020,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_881jobs2 : List Job := [⟨plan3020,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_881jobs : List Job := t5_881jobs0++t5_881jobs1++t5_881jobs2




def t5_882root : Job := ⟨plan4737,[],none,⟨10,6,0⟩⟩
def t5_882jobs0 : List Job := [⟨plan3021,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3021,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_882jobs1 : List Job := [⟨plan3021,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_882jobs2 : List Job := [⟨plan3021,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_882jobs : List Job := t5_882jobs0++t5_882jobs1++t5_882jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


