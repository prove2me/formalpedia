-- Prove2me | solution 1 for Auto.ct_calderon_transference_external
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:11.464807+00:00
-- url     : https://prove2.me/submissions/13e31d8c-e21c-4000-96c6-5b33591bd397

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_realErgodicJumpBound_of_realVariable
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
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n)
    (p : Fin n → ℝ≥0∞) (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2) (C : ℝ) (_hC : 0 < C) :
    0 < calderonTransferenceConstant n ∧ ∀ g : ℕ → ℝ,
      (∀ J, 0 < J → 1 ≤ g J) →
      realVariableJumpBound p C g →
        realErgodicJumpBound.{u} p (calderonTransferenceConstant n * C) g := by
  refine ⟨by dsimp [calderonTransferenceConstant]; positivity, ?_⟩
  intro g _hg hreal
  have h := aux_realErgodicJumpBound_of_realVariable (by omega) p C g hp hsum hreal
  have hconstant : calderonTransferenceConstant n * C =
      (2 : ℝ) ^ n * ((2 : ℝ) ^ (3 * n + 6) * C) := by
    dsimp [calderonTransferenceConstant]
    calc
      (2 : ℝ) ^ (4 * n + 6) * C =
          (2 : ℝ) ^ (n + (3 * n + 6)) * C := by
            congr 1
            ring
      _ = ((2 : ℝ) ^ n * (2 : ℝ) ^ (3 * n + 6)) * C := by
            rw [pow_add]
      _ = (2 : ℝ) ^ n * ((2 : ℝ) ^ (3 * n + 6) * C) := by ring
  rw [hconstant]
  exact h
end Auto
