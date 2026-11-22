-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:55.242427+00:00
-- url     : https://prove2.me/theorems/ea3fca66-458a-4873-9eb4-2fda37e4894c
-- title:
--   Pi
-- statement:
--   Definitions and structural lemmas for Pi, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean

module
public import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Function Set
namespace MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
instance : IsProbabilityMeasure (.pi μ) :=
  ⟨by simp_rw [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩
end MeasureTheory.Measure


