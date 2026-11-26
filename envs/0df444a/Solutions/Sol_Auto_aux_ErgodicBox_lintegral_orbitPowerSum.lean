-- Prove2me | solution 1 for Auto.aux_ErgodicBox.lintegral_orbitPowerSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:59.081655+00:00
-- url     : https://prove2.me/submissions/e58b9ae3-1059-4b83-844d-a2f5600878d6

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_enorm_rpow
public import Theorems.Thm_Auto_aux_ErgodicBox_lintegral_enorm_rpow_comp_measurePreserving
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution
    {X κ : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    ∫⁻ x, orbitPowerSum B T f p x ∂μ =
      B.card * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  unfold orbitPowerSum
  rw [lintegral_finsetSum' B]
  · calc
      ∑ k ∈ B, ∫⁻ x, ‖f (T k x)‖ₑ ^ p ∂μ =
          ∑ k ∈ B, ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact lintegral_enorm_rpow_comp_measurePreserving (T k) (hT k hk) f hf p
      _ = B.card * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
  · intro k hk
    exact aemeasurable_enorm_rpow (f ∘ T k)
      (hf.comp_quasiMeasurePreserving (hT k hk).quasiMeasurePreserving) p
end Auto.aux_ErgodicBox
