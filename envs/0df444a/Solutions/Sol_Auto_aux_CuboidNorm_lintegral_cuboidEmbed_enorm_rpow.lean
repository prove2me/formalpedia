-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_cuboidEmbed_enorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:16.298728+00:00
-- url     : https://prove2.me/submissions/379dd2d1-8dd5-4619-a3e9-2e21deb9c68c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_volume_axisCuboid
public import Theorems.Thm_Auto_aux_CuboidNorm_cuboidEmbed_eq_finiteLatticeStep_apply
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteLatticeStep_enorm_rpow

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
    (hsupport : ∀ k, k ∉ A → a k = 0) (q : ℝ) (hq : 0 < q) :
    (∫⁻ y, ‖aux_cuboidEmbed ε δ i a y‖ₑ ^ q ∂volume) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q *
        ∏ j, ENNReal.ofReal (if j = i then δ else ε) := by
  have hεle : ε ≤ 1 := hε.le
  have hδle : δ ≤ 1 := by linarith
  calc
    (∫⁻ y, ‖aux_cuboidEmbed ε δ i a y‖ₑ ^ q ∂volume) =
        ∫⁻ y, ‖finiteLatticeStep ε δ i A a y‖ₑ ^ q ∂volume := by
          congr with y
          rw [cuboidEmbed_eq_finiteLatticeStep_apply hε0 hε hεδ i A a hsupport y]
    _ = ∑ k ∈ A, ‖a k‖ₑ ^ q * volume (latticeAxisCuboid ε δ i k) :=
      lintegral_finiteLatticeStep_enorm_rpow hεle hδle i A a q hq
    _ = ∑ k ∈ A, ‖a k‖ₑ ^ q *
        ∏ j, ENNReal.ofReal (if j = i then δ else ε) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [latticeAxisCuboid, volume_axisCuboid]
end Auto.aux_CuboidNorm
