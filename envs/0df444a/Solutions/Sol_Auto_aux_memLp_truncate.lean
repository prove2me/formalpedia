-- Prove2me | solution 1 for Auto.aux_memLp_truncate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:04.284555+00:00
-- url     : https://prove2.me/submissions/a79bb8e7-0a18-408b-838d-70f1a67e6a31

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_eLpNorm_truncate_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (A : Finset (Fin n → ℕ))
    (F : (Fin n → ℕ) → ℝ) (p : ℝ≥0∞) (hF : MemLp F p Measure.count) :
    MemLp (aux_truncate A F) p Measure.count := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  exact (aux_eLpNorm_truncate_le A F p).trans_lt hF.2
end Auto
