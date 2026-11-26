-- Prove2me | solution 1 for Auto.aux_CuboidNorm.memLp_cuboidEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:33.804413+00:00
-- url     : https://prove2.me/submissions/78b54e06-5d77-4e3e-a367-faf2cf705b38

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_cuboidEmbed_eq
public import Theorems.Thm_Auto_aux_CuboidNorm_measurable_cuboidEmbed
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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    MemLp (aux_cuboidEmbed ε δ i a) p volume := by
  refine ⟨(measurable_cuboidEmbed hε0 hε hεδ i A a hsupport).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_cuboidEmbed_eq hε0 hε hεδ i A a hsupport p hp0 hptop]
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
  apply (ENNReal.sum_lt_top.mpr fun k hk ↦ ?_).ne
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg (by simp)
  · apply ENNReal.prod_lt_top
    intro j hj
    exact ENNReal.ofReal_lt_top
end Auto.aux_CuboidNorm
