-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_natToInt_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:52:22.301618+00:00
-- url     : https://prove2.me/submissions/d766d446-b3c0-406b-919b-8c088a6ddf6e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_natToInt_enorm_rpow_eq

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ}
    (A : Finset (Fin n → ℕ)) (F : (Fin n → ℕ) → ℝ)
    (hsupport : ∀ k, k ∉ A → F k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_natToInt F) p Measure.count = eLpNorm F p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    lintegral_count_natToInt_enorm_rpow_eq A F hsupport p.toReal
      (ENNReal.toReal_pos hp0 hptop)]
end Auto.aux_CuboidNorm
