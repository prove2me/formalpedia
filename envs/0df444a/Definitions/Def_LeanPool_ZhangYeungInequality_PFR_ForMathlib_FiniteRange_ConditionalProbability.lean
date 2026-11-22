-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:24.459202+00:00
-- url     : https://prove2.me/theorems/0da9e9e0-036b-4e80-9c45-1b266cf607d8
-- title:
--   Conditional Probability
-- statement:
--   Definitions and structural lemmas for Conditional Probability, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/FiniteRange/ConditionalProbability.lean

module
public import Mathlib.Probability.ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
namespace ProbabilityTheory
variable {Ω α : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
 [MeasurableSpace α] [MeasurableSingletonClass α]
end ProbabilityTheory


