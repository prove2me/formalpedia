-- Prove2me | Definitions.Def_Submission_ThreeSum_RawIncidences
-- name    : Submission_ThreeSum_RawIncidences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:15.776196+00:00
-- url     : https://prove2.me/theorems/ec6c43aa-c08e-474d-abf1-a7d4ba12683b
-- title:
--   Raw Incidences
-- statement:
--   Definitions and structural lemmas for Raw Incidences, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
def lift (j : Fin 3) : ℤ := (j.val : ℤ) - 1
abbrev ChoiceTuple (h J : ℕ) := Fin J → RetainedChoice h
instance retainedChoiceDecidableEq (h : ℕ) : DecidableEq (RetainedChoice h) := inferInstance
instance choiceTupleDecidableEq (h J : ℕ) : DecidableEq (ChoiceTuple h J) :=
  Fintype.decidablePiFintype
def tupleLeft {h J : ℕ} (t : ChoiceTuple h J) : ℤ :=
  Radix.positionalHash (localPrime h) rawLeft (List.ofFn t)
def tupleRight {h J : ℕ} (t : ChoiceTuple h J) : ℤ :=
  Radix.positionalHash (localPrime h) rawRight (List.ofFn t)
def tupleOutput {h J : ℕ} (t : ChoiceTuple h J) : GlobalOutput h J :=
  fun i => blockOfChoice (t i)
def tupleKey {h J : ℕ} (t : ChoiceTuple h J) : ℤ := globalKey (tupleOutput t)
def leftSignature {h J : ℕ} (t : ChoiceTuple h J) :=
  fun i : Fin J => (occurrence (t i), LocalGraph.left (edge (t i)))
def rightSignature {h J : ℕ} (t : ChoiceTuple h J) :=
  fun i : Fin J => (occurrence (t i), LocalGraph.right (edge (t i)))
def tupleOfList {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    ChoiceTuple h J := fun i => xs.get (Fin.cast hlen.symm i)
abbrev Witness (h J : ℕ) := ChoiceTuple h J × Fin 3
instance witnessDecidableEq (h J : ℕ) : DecidableEq (Witness h J) := inferInstance
def witnesses (h J : ℕ) (P d a b c : ℤ) : Finset (Witness h J) :=
  Finset.univ.filter fun w : Witness h J =>
    List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
      globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1
section OriginalIndices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
abbrev Original (α β γ : Type*) := α × (β × γ)
def difference (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (t : Original α β γ) : ℤ :=
  c t.2.2 - b t.2.1 - a t.1
abbrev RawItem (h J : ℕ) (α β γ : Type*) := Σ _t : Original α β γ, Witness h J
def rawOn (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : Finset (RawItem h J α β γ) :=
  T.sigma fun t => witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)
def rawMass (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : ℕ := (rawOn h J P d T a b c).card
def leftBucket {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (t : ChoiceTuple h J) : ℕ :=
  ∑ j ∈ B, if globalModulus h J ∣ b j % P - tupleLeft t then 1 else 0
def rightBucket {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (t : ChoiceTuple h J) : ℕ :=
  ∑ j ∈ C, if globalModulus h J ∣ c j % P + d - tupleRight t then 1 else 0
def productMass (h J : ℕ) (P d : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : ℕ :=
  ∑ i ∈ A, ∑ t : ChoiceTuple h J, ∑ j : Fin 3,
    if globalModulus h J ∣ (a i % P + lift j * P + d) - tupleKey t
    then leftBucket P B b t * rightBucket P d C c t else 0
end OriginalIndices
end ThreeSum.RawIncidences


