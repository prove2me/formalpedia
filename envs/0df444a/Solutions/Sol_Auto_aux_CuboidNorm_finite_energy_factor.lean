-- Prove2me | solution 1 for Auto.aux_CuboidNorm.finite_energy_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:40.21897+00:00
-- url     : https://prove2.me/submissions/5637302c-ec58-4e93-82fb-567a5526a81c

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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ} (A : Finset (ZVector n))
    (ε c : ℝ) (hc : 0 ≤ c) (a : ZVector n → ℝ) :
    (∑ k ∈ A, ‖c * a k‖ₑ ^ (2 : ℝ)) *
        ∏ _ : Fin n, ENNReal.ofReal ε =
      (ENNReal.ofReal c ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ k ∈ A, ‖a k‖ₑ ^ (2 : ℝ) := by
  have hmul (x y : ℝ) :
      ‖x * y‖ₑ ^ (2 : ℝ) = ‖x‖ₑ ^ (2 : ℝ) * ‖y‖ₑ ^ (2 : ℝ) := by
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg]
    norm_num
  have hsum : ∑ k ∈ A, ‖c * a k‖ₑ ^ (2 : ℝ) =
      ‖c‖ₑ ^ (2 : ℝ) * ∑ k ∈ A, ‖a k‖ₑ ^ (2 : ℝ) := by
    simp_rw [hmul]
    rw [Finset.mul_sum]
  rw [hsum, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  simp only [Finset.prod_const]
  rw [Finset.card_fin]
  ac_rfl
end Auto.aux_CuboidNorm
