-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
-- name    : LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:35:07.054133+00:00
-- url     : https://prove2.me/theorems/25b7116d-e530-4b56-b616-2902c72768e3
-- title:
--   Generalization Results
-- statement:
--   Definitions and structural lemmas for Generalization Results, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
attribute [local instance] Classical.propDecidable
section UCNotOnline
noncomputable def thresholdClassX {X : Type u} (φ : ℕ ↪ X) : ConceptClass X Bool :=
  { f | ∃ n : ℕ, f = fun x => decide (∃ k, k ≤ n ∧ φ k = x) }
noncomputable def mistakesFromG {X : Type u}
    (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict s x ≠ c x then 1 else 0) +
      mistakesFromG L (L.update s x (c x)) c xs
end UCNotOnline


