-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_eq_count_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:50.034031+00:00
-- url     : https://prove2.me/submissions/f7871175-0f38-474a-9731-6a0156653c3b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_cuboidEmbed_eq_count_mul
public import Theorems.Thm_Auto_aux_CuboidNorm_measurable_cuboidEmbed
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftRaw_eq

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
    eLpNorm (aux_liftRaw (aux_cuboidEmbed ε δ i a)) p volume =
      eLpNorm a p Measure.count *
        (∏ j, ENNReal.ofReal (if j = i then δ else ε)) ^ (1 / p.toReal) := by
  rw [eLpNorm_liftRaw_eq _ p
    (measurable_cuboidEmbed hε0 hε hεδ i A a hsupport),
    eLpNorm_cuboidEmbed_eq_count_mul hε0 hε hεδ i A a hsupport p hp0 hptop]
end Auto.aux_CuboidNorm
