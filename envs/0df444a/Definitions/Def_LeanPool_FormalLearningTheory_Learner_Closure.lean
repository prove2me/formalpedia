-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
-- name    : LeanPool_FormalLearningTheory_Learner_Closure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:34:13.691829+00:00
-- url     : https://prove2.me/theorems/22a433e3-e1e1-4e26-82b0-519ea1ef6f2f
-- title:
--   Closure
-- statement:
--   Definitions and structural lemmas for Closure, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
attribute [local instance] Classical.propDecidable
noncomputable def combineLearner
    {X : Type u}
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (L : Fin k → BatchLearner X Bool) : BatchLearner X Bool where
  hypotheses := {h | ∃ hs : Fin k → Concept X Bool,
    (∀ i, hs i ∈ (L i).hypotheses) ∧
    h = fun x => F x (fun i => hs i x)}
  learn := fun {m} S x => F x (fun i => (L i).learn S x)
  output_in_H := fun {m} S => by
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun i => (L i).learn S, fun i => (L i).output_in_H S, rfl⟩
noncomputable def boostLearner
    {X : Type u}
    (k : ℕ) (L : Fin k → BatchLearner X Bool) : BatchLearner X Bool :=
  combineLearner k (fun _ v => majorityVote k v) L
noncomputable def interpLearner
    {X : Type u}
    (A : Set X) (L₁ L₂ : BatchLearner X Bool) : BatchLearner X Bool :=
  combineLearner 2
    (fun x v => if x ∈ A then v 0 else v 1)
    (fun i => if i = 0 then L₁ else L₂)
class UniformMeasurableBatchFamily {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) : Prop where
  eval_measurable : ∀ (m : ℕ),
    Measurable (fun p : ℕ × (Fin m → X × Bool) × X => (L p.1).learn p.2.1 p.2.2)
noncomputable def concatLearner
    {X : Type u}
    (L : ℕ → BatchLearner X Bool)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ) : BatchLearner X Bool where
  hypotheses := ⋃ n, (L n).hypotheses
  learn := fun S x => (L (sel S)).learn S x
  output_in_H := fun S => Set.mem_iUnion.mpr ⟨sel S, (L (sel S)).output_in_H S⟩


