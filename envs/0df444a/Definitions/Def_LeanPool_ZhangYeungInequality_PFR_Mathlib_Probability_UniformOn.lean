-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:37.129813+00:00
-- url     : https://prove2.me/theorems/a73d1410-1f8d-4249-9b5b-67a5705f2e33
-- title:
--   Uniform On
-- statement:
--   Definitions and structural lemmas for Uniform On, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/UniformOn.lean

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function MeasureTheory Measure
namespace ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
instance _root_.ProbabilityTheory.uniformOn.instIsProbabilityMeasure [Nonempty s] [Finite s] :
    IsProbabilityMeasure (uniformOn s) := isProbabilityMeasure_uniformOn ‹_› .of_subtype
end ProbabilityTheory


