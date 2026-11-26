-- Prove2me | solution 1 for Auto.aux_realErgodicJumpBound_of_realVariable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:55.486255+00:00
-- url     : https://prove2.me/submissions/fdba0c90-e430-4099-b3c1-87a5ff147eaa

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_finite_forward_jump_bound_of_realVariable
public import Theorems.Thm_Auto_aux_ErgodicBox_holder_exponents_of_inverse_sum
public import Theorems.Thm_Auto_aux_ErgodicBox_realErgodicJumpEnergy_of_finite_sum
public import Theorems.Thm_Auto_aux_ofReal_two_pow_mul
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
theorem _root_.solution {n : ℕ}
    (hn : 0 < n) (p : Fin n → ℝ≥0∞) (C : ℝ) (g : ℕ → ℝ)
    (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2)
    (hreal : realVariableJumpBound p C g) :
    realErgodicJumpBound.{u} p
      ((2 : ℝ) ^ n * ((2 : ℝ) ^ (3 * n + 6) * C)) g := by
  intro X _ μ S J hJ N hN hNpos f hf
  rcases aux_ErgodicBox.holder_exponents_of_inverse_sum p hp hsum with
    ⟨hp0, hptop, _hpreal, _hqsum⟩
  let Cd : ℝ := (2 : ℝ) ^ (3 * n + 6) * C
  have hbox := aux_ErgodicBox.realErgodicJumpEnergy_of_finite_sum
    p hp hsum S N hN hNpos f hf
    (ENNReal.ofReal Cd * ENNReal.ofReal (g J)) (by
      intro x
      exact aux_finite_forward_jump_bound_of_realVariable hn p C g hreal hJ
        N hN hNpos
        (fun i ↦ aux_ErgodicBox.truncOrbit
          (aux_ErgodicBox.box n
            (N (Fin.last J) + N (Fin.last J)))
          (aux_orbit S.transformation) (f i) x)
        (aux_ErgodicBox.box n (N (Fin.last J))) hp0 hptop)
  have hconstant :
      ENNReal.ofReal ((2 : ℝ) ^ n * Cd) =
        ((2 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal Cd :=
    aux_ofReal_two_pow_mul n Cd
  change realErgodicJumpEnergy S N f ≤
    ENNReal.ofReal ((2 : ℝ) ^ n * Cd) * ENNReal.ofReal (g J) *
      ∏ i, eLpNorm (f i) (p i) μ ^ 2
  rw [hconstant]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hbox
end Auto
