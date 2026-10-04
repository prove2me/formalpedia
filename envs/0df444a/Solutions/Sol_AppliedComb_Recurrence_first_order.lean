-- Prove2me | solution 1 for AppliedComb.Recurrence.first_order
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:21:19.96034+00:00
-- url     : https://prove2.me/submissions/bfb6f188-89ad-49f4-9919-f33ba72eaf5b

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

open AppliedComb.Recurrence in
theorem solution (r : ℝ) (hr : r ≠ 0) (f : ℤ → ℝ)
    (hf : (advance - r • (1 : Module.End ℝ (ℤ → ℝ))) f = 0) (c : ℝ) (hc : c = f 0) :
    ∀ n : ℤ, f n = c * r ^ n := by
  have step : ∀ n : ℤ, f (n + 1) = r * f n := by
    intro n
    have h := congrFun hf n
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have h2 : advance f n = f (n + 1) := rfl
    rw [h2] at h
    linarith
  intro n
  induction n using Int.induction_on with
  | zero => simp [hc]
  | succ k ih =>
    rw [step, ih, zpow_add_one₀ hr]
    ring
  | pred k ih =>
    have h1 := step (-(k : ℤ) - 1)
    have e : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
    rw [e, ih] at h1
    rw [zpow_sub_one₀ hr, show f (-(k : ℤ) - 1) = r⁻¹ * (r * f (-(k : ℤ) - 1)) by
      rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul], ← h1]
    ring
