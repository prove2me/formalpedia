-- Prove2me | solution 1 for Auto.aux_ErgodicBox.eLpNorm_count_sq_eq_finset_sum_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:34.380854+00:00
-- url     : https://prove2.me/submissions/72e59964-fed1-4915-ad66-fd2d6ba18190

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution
    {κ : Type*} [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
    (B : Finset κ) (F : κ → ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hpreal : 0 < p.toReal)
    (hF : ∀ k, k ∉ B → F k = 0) :
    eLpNorm F p Measure.count ^ 2 =
      (∑ k ∈ B, ‖F k‖ₑ ^ p.toReal) ^ (2 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  have hexp : (1 / p.toReal) * (↑(2 : ℕ) : ℝ) = 2 / p.toReal := by ring
  rw [hexp]
  rw [lintegral_count]
  rw [tsum_eq_sum]
  intro k hk
  rw [hF k hk]
  simp [ENNReal.zero_rpow_of_pos hpreal]
end Auto.aux_ErgodicBox
