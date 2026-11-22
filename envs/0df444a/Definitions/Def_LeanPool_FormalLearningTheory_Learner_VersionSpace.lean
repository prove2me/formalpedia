-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_VersionSpace
-- name    : LeanPool_FormalLearningTheory_Learner_VersionSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:12.643831+00:00
-- url     : https://prove2.me/theorems/4bdadf38-8198-40bb-853b-3e0f4526e4b0
-- title:
--   Version Space
-- statement:
--   Definitions and structural lemmas for Version Space, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/VersionSpace.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open MeasureTheory Set
def IsSampleConsistent {X : Type u} (h : Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) : Prop :=
  ∀ i, h (S i).1 = (S i).2
instance isSampleConsistentDecidable
    {X : Type u} (h : Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) :
    Decidable (IsSampleConsistent h S) :=
  Fintype.decidableForallFintype
def IsFirstConsistent {X : Type u} (enum : ℕ → Concept X Bool)
    {m : ℕ} (S : Fin m → X × Bool) (n : ℕ) : Prop :=
  IsSampleConsistent (enum n) S ∧ ∀ k, k < n → ¬ IsSampleConsistent (enum k) S
noncomputable def versionSpaceLearner
    {X : Type u}
    (enum : ℕ → Concept X Bool) : BatchLearner X Bool where
  hypotheses := range enum ∪ {fun _ => false}
  learn S := by
    classical
    exact if h : ∃ n, IsSampleConsistent (enum n) S
      then enum (Nat.find h)
      else fun _ => false
  output_in_H S := by
    classical
    change (if h : ∃ n, IsSampleConsistent (enum n) S then enum (Nat.find h)
          else fun _ => false) ∈ range enum ∪ {fun _ => false}
    by_cases h : ∃ n, IsSampleConsistent (enum n) S
    · rw [dif_pos h]; exact Or.inl ⟨Nat.find h, rfl⟩
    · rw [dif_neg h]; exact Or.inr rfl


