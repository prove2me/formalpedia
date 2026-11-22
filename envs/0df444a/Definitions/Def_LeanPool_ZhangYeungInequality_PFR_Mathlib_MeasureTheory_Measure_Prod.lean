-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:52.3308+00:00
-- url     : https://prove2.me/theorems/18a0b058-440a-470b-855a-9a910eda3c95
-- title:
--   Prod
-- statement:
--   Definitions and structural lemmas for Prod, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean

module
public import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function
open scoped ENNReal NNReal
namespace MeasureTheory.Measure
variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω
    → β} {Z : Ω → γ}
end MeasureTheory.Measure
open MeasureTheory
instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsZeroOrProbabilityMeasure μ] {ν : Measure β} [IsZeroOrProbabilityMeasure ν] :
    IsZeroOrProbabilityMeasure (μ.prod ν) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · rw [Measure.zero_prod]
    infer_instance
  rcases eq_zero_or_isProbabilityMeasure ν with rfl | hν
  · rw [Measure.prod_zero]
    infer_instance
  infer_instance


