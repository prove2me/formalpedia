-- Prove2me | solution 1 for Auto.aux_scaled_unitIntervalKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:11.97795+00:00
-- url     : https://prove2.me/submissions/d7e4ce2e-0d6c-44bc-a709-514386babc72

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
theorem _root_.solution {N : ℕ} (hN : 0 < N) (s : ℝ) :
    (N : ℝ)⁻¹ * ctUnitIntervalKernel ((N : ℝ)⁻¹ * s) =
      (N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s := by
  unfold ctUnitIntervalKernel
  by_cases hs : s ∈ Ico (0 : ℝ) N
  · have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hs' : (N : ℝ)⁻¹ * s ∈ Ico (0 : ℝ) 1 := by
      rw [mem_Ico] at hs ⊢
      rw [inv_mul_eq_div]
      constructor
      · exact (le_div_iff₀ hNreal).2 (by simpa using hs.1)
      · rw [div_lt_iff₀ hNreal]
        simpa using hs.2
    simp [hs, hs']
  · have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hs' : (N : ℝ)⁻¹ * s ∉ Ico (0 : ℝ) 1 := by
      intro hs'
      rw [inv_mul_eq_div] at hs'
      rw [mem_Ico] at hs'
      apply hs
      rw [mem_Ico]
      constructor
      · have h := (le_div_iff₀ hNreal).1 hs'.1
        simpa using h
      · have h := (div_lt_iff₀ hNreal).1 hs'.2
        simpa using h
    simp [hs, hs']
end Auto
