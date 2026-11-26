-- Prove2me | solution 1 for Auto.aux_ErgodicBox.holder_exponents_of_inverse_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:44:24.819574+00:00
-- url     : https://prove2.me/submissions/e7033f85-2aed-4eda-983d-674f91d8c326

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
theorem _root_.solution {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2) :
    (∀ i, p i ≠ 0) ∧ (∀ i, p i ≠ ∞) ∧
      (∀ i, 0 < (p i).toReal) ∧
      ∑ i, 2 / (p i).toReal = 1 := by
  have hp0 : ∀ i, p i ≠ 0 := by
    intro i hi
    have := (hp i).1
    simp [hi] at this
  have hptop : ∀ i, p i ≠ ∞ := by
    intro i
    exact ne_of_lt (hp i).2
  refine ⟨hp0, hptop, ?_, ?_⟩
  · intro i
    exact ENNReal.toReal_pos (hp0 i) (hptop i)
  · calc
      ∑ i, 2 / (p i).toReal = 2 * ∑ i, ((p i)⁻¹).toReal := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.toReal_inv]
        ring
      _ = 1 := by rw [hsum]; norm_num
end Auto.aux_ErgodicBox
