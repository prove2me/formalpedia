-- Prove2me | solution 1 for Auto.aux_integral_scaled_Ico_eq_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:12.559636+00:00
-- url     : https://prove2.me/submissions/d97d96f6-23b8-40f3-958b-8c72a644994a

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
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
namespace Auto
theorem _root_.solution {N : ℕ} (P : ℝ → ℝ) :
    ∫ s : ℝ, ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s) *
        P s =
      (N : ℝ)⁻¹ * ∫ s in Ico (0 : ℝ) N, P s := by
  have hkernel : ∀ s : ℝ,
      ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s) * P s =
        (N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator P s := by
    intro s
    by_cases hs : s ∈ Ico (0 : ℝ) N <;> simp [hs]
  calc
    ∫ s : ℝ, ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator
        (fun _ ↦ (1 : ℝ)) s) * P s =
        ∫ s : ℝ, (N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator P s := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      exact hkernel s
    _ = (N : ℝ)⁻¹ * ∫ s : ℝ, (Ico (0 : ℝ) N).indicator P s :=
      MeasureTheory.integral_const_mul _ _
    _ = _ := by
      rw [MeasureTheory.integral_indicator measurableSet_Ico]
end Auto
