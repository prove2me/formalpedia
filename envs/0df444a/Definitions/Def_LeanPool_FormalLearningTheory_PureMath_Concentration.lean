-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_Concentration
-- name    : LeanPool_FormalLearningTheory_PureMath_Concentration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:29.603542+00:00
-- url     : https://prove2.me/theorems/99dd85c1-3d2a-416e-a767-cee30c625c4a
-- title:
--   Concentration
-- statement:
--   Definitions and structural lemmas for Concentration, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/Concentration.lean

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
class BoundedRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (a b : ℝ) : Prop where
  ae_mem_Icc : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc a b
  measurable : Measurable f
section ClassicalInstances
attribute [local instance] Classical.propDecidable
end ClassicalInstances


