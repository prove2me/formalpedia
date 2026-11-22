-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:52.176431+00:00
-- url     : https://prove2.me/theorems/6669c510-c685-41fc-87a5-9280e8719d36
-- title:
--   Countable
-- statement:
--   Definitions and structural lemmas for Countable, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open ENNReal
namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]
end MeasureTheory


