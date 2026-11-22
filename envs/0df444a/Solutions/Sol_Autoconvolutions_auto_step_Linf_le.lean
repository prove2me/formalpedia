-- Prove2me | solution 1 for Autoconvolutions.auto_step_Linf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:15.780606+00:00
-- url     : https://prove2.me/submissions/111395ab-23f9-4c86-b793-20a879ed7525

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_auto_step_interpolate
public import Theorems.Thm_Autoconvolutions_auto_step_nonneg


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ k : ℤ, convCoeff d p k ≤ M) :
    (eLpNorm (auto (step d p)) ∞ volume).toReal ≤ M := by
  rw [eLpNorm_exponent_top]
  have bound (x : ℝ) : ‖auto (step d p) x‖ ≤ M := by
    let k : ℤ := ⌊x - 1⌋
    have hl : (k:ℝ) ≤ x-1 := Int.floor_le _
    have hr : x-1 < (k:ℝ)+1 := Int.lt_floor_add_one _
    let u : ℝ := x-((k:ℝ)+1)
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hu' : u ≤ 1 := by dsimp [u]; linarith
    have hx : (k:ℝ)+1+u = x := by dsimp [u]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (auto_step_nonneg hp _), ← hx,
      auto_step_interpolate _ _ _ _ hu hu']
    calc
      _ ≤ (1-u)*M + u*M := add_le_add
        (mul_le_mul_of_nonneg_left (hb k) (by linarith))
        (mul_le_mul_of_nonneg_left (hb (k+1)) hu)
      _ = M := by ring
  simpa [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound (.of_forall bound))
end Autoconvolutions
