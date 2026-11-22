-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:22:04.823972+00:00
-- url     : https://prove2.me/theorems/b439c539-d36e-44b7-b6da-87a23abed4bb
-- title:
--   Real
-- statement:
--   Definitions and structural lemmas for Real, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function Set
open scoped ENNReal NNReal
namespace MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}
variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']
end MeasureTheory


