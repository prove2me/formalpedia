-- Prove2me | solution 1 for Auto.aux_ErgodicBox.lintegral_finite_orbit_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:01.784253+00:00
-- url     : https://prove2.me/submissions/0b2e2844-f3c5-4515-a9ef-3bc84a1cd22d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_two_sq_nat
public import Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_two_sq_nat
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
    {X κ : Type*} [MeasurableSpace X] (μ : Measure X)
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    {J : ℕ} (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ) :
    ∫⁻ x, ∑ j : Fin J, ∑ k ∈ B, ‖d j (T k x)‖ₑ ^ (2 : ℕ) ∂μ =
      B.card * ∑ j : Fin J, ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
  have hmeas : ∀ j : Fin J, ∀ k ∈ B,
      AEMeasurable (fun x ↦ ‖d j (T k x)‖ₑ ^ (2 : ℕ)) μ := by
    intro j k hk
    exact (((hd j).comp_quasiMeasurePreserving
      (hT k hk).quasiMeasurePreserving).enorm.pow measurable_const.aemeasurable)
  have hterm : ∀ (j : Fin J) (k : κ), k ∈ B →
      ∫⁻ x, ‖d j (T k x)‖ₑ ^ (2 : ℕ) ∂μ =
        ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
    intro j k hk
    rw [← eLpNorm_two_sq_nat]
    change eLpNorm (d j ∘ T k) 2 μ ^ 2 = _
    rw [eLpNorm_comp_measurePreserving (hd j) (hT k hk)]
    exact eLpNorm_two_sq_nat μ (d j)
  rw [lintegral_finsetSum' Finset.univ]
  · calc
      ∑ j, ∫⁻ x, ∑ k ∈ B, ‖d j (T k x)‖ₑ ^ (2 : ℕ) ∂μ =
          ∑ j, ∑ k ∈ B, ∫⁻ x, ‖d j (T k x)‖ₑ ^ (2 : ℕ) ∂μ := by
        apply Finset.sum_congr rfl
        intro j _
        exact lintegral_finsetSum' B (hmeas j)
      _ = ∑ j, ∑ k ∈ B, ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm j k hk
      _ = B.card * ∑ j : Fin J, ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
        calc
          ∑ j, ∑ k ∈ B, ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ =
              ∑ j, B.card • ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_const _
          _ = B.card * ∑ j : Fin J, ∫⁻ x, ‖d j x‖ₑ ^ (2 : ℕ) ∂μ := by
            simp only [nsmul_eq_mul]
            rw [Finset.mul_sum]
  · intro j _
    simpa only [Finset.sum_fn] using Finset.aemeasurable_sum B (hmeas j)
end Auto.aux_ErgodicBox
