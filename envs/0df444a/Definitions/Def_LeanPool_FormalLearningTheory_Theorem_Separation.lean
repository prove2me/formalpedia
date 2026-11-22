-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Separation
-- name    : LeanPool_FormalLearningTheory_Theorem_Separation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:35:19.503462+00:00
-- url     : https://prove2.me/theorems/db82618c-8140-4b05-b179-40f9541ef2fd
-- title:
--   Separation
-- statement:
--   Definitions and structural lemmas for Separation, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Extended
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
noncomputable def mistakesFromU {X : Type u}
    (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict s x ≠ c x then 1 else 0) +
      mistakesFromU L (L.update s x (c x)) c xs
def boosted_majority (k : ℕ) (votes : Fin k → Bool) : Bool :=
  k < 2 * ((Finset.univ.filter (fun j => votes j)).card)
def LearnEvalMeasurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) : Prop :=
  ∀ m : ℕ,
    Measurable (fun p : (Fin m → X × Bool) × X => L.learn p.1 p.2)
def goodBlockEvent
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) (D : MeasureTheory.Measure X)
    (c : Concept X Bool) (rate : ℕ → ℝ)
    (k n : ℕ) (j : Fin k) : Set (Fin (k * n) → X) :=
  { ω : Fin (k * n) → X |
      D { x : X |
          L.learn (fun i => (blockExtract k n ω j i, c (blockExtract k n ω j i))) x ≠ c x }
        ≤ ENNReal.ofReal (rate n) }
section ClassicalInstances
attribute [local instance] Classical.propDecidable
end ClassicalInstances
def thresholdClass : ConceptClass ℕ Bool :=
  { f | ∃ n : ℕ, f = fun x => decide (x ≤ n) }
noncomputable def thresholdTree (lo : ℕ) : (d : ℕ) → LTree ℕ d
  | 0 => .leaf
  | d + 1 =>
    let mid := lo + 2 ^ d
    .branch mid (thresholdTree mid d) (thresholdTree lo d)


