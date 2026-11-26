-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_cuboidEmbed_eq_count_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:52:39.905545+00:00
-- url     : https://prove2.me/submissions/1a1507dd-c743-480d-830c-c3decd5ca926

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_cuboidEmbed_enorm_rpow
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_enorm_rpow_eq_finset

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
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_cuboidEmbed ε δ i a) p volume =
      eLpNorm a p Measure.count *
        (∏ j, ENNReal.ofReal (if j = i then δ else ε)) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  rw [lintegral_cuboidEmbed_enorm_rpow hε0 hε hεδ i A a hsupport
    p.toReal (ENNReal.toReal_pos hp0 hptop)]
  rw [← Finset.sum_mul, ← lintegral_count_enorm_rpow_eq_finset A a p.toReal
    (ENNReal.toReal_pos hp0 hptop) hsupport]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
end Auto.aux_CuboidNorm
