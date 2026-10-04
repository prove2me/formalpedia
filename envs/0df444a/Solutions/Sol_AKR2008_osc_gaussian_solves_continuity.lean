-- Prove2me | solution 1 for AKR2008.osc_gaussian_solves_continuity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:05:37.905996+00:00
-- url     : https://prove2.me/submissions/436fa834-7365-4337-be59-16204e1bf93c

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

set_option autoImplicit false

open AKR2008 in
theorem solution (ω τ w x t : ℝ) (hcos : Real.cos (ω * t) ≠ 0) :
    deriv (fun s => oscP ω τ w x s) t
      + deriv (fun y => oscP ω τ w y t * deriv (fun z => oscS ω z t) y) x = 0 := by
  rcases le_or_gt τ 0 with hτ | hτ
  · have h0 : ∀ y s, oscP ω τ w y s = 0 := by
      intro y s
      unfold oscP
      rw [Real.sqrt_eq_zero'.mpr, zero_mul]
      exact div_nonpos_of_nonpos_of_nonneg hτ (by positivity)
    simp [h0]
  · have hS : ∀ y, deriv (fun z => oscS ω z t) y = -(ω * y) * Real.tan (ω * t) := by
      intro y
      have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      have h2 := ((h1.const_mul ω).div_const 2).neg.mul_const (Real.tan (ω * t))
      have e : deriv (fun z => oscS ω z t) y = _ := h2.deriv
      rw [e]; ring
    have hSf : (fun y => oscP ω τ w y t * deriv (fun z => oscS ω z t) y)
        = fun y => oscP ω τ w y t * (-(ω * y) * Real.tan (ω * t)) := by
      funext y; rw [hS y]
    rw [hSf]
    have hc2 : Real.cos (ω * t) ^ 2 ≠ 0 := pow_ne_zero 2 hcos
    have hc2pos : 0 < Real.cos (ω * t) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hc2)
    have hden : (2 * Real.pi * Real.cos (ω * t) ^ 2) ≠ 0 := by positivity
    have hQpos : 0 < τ / (2 * Real.pi * Real.cos (ω * t) ^ 2) := by positivity
    have hcosd : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * t) * (ω * 1)) t :=
      ((hasDerivAt_id' t).const_mul ω).cos
    have hC2 := hcosd.pow 2
    have hQd := (hasDerivAt_const t τ).div (hC2.const_mul (2 * Real.pi)) hden
    have hsq := hQd.sqrt hQpos.ne'
    have hA := (hasDerivAt_const t τ).div hC2 hc2
    have hB := ((hasDerivAt_const t x).sub (hcosd.const_mul w)).pow 2
    have hEd := (hA.const_mul (-(1 / 2 : ℝ))).mul hB
    have hP := hsq.mul hEd.exp
    have e1 : deriv (fun s => oscP ω τ w x s) t = _ :=
      HasDerivAt.deriv (f := fun s => oscP ω τ w x s) hP
    have hy := ((hasDerivAt_const x (Real.sqrt (τ / (2 * Real.pi * Real.cos (ω * t) ^ 2)))).mul
      (((hasDerivAt_const x (-(1 / 2) * (τ / Real.cos (ω * t) ^ 2))).mul
        (((hasDerivAt_id' x).sub_const (w * Real.cos (ω * t))).pow 2)).exp)).mul
      (((hasDerivAt_id' x).const_mul ω).neg.mul_const (Real.tan (ω * t)))
    have e2 : deriv (fun y => oscP ω τ w y t * (-(ω * y) * Real.tan (ω * t))) x = _ :=
      HasDerivAt.deriv (f := fun y => oscP ω τ w y t * (-(ω * y) * Real.tan (ω * t))) hy
    rw [e1, e2]
    simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, Pi.neg_apply,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    have hK : Real.sqrt (τ / (2 * Real.pi * Real.cos (ω * t) ^ 2)) ^ 2
        = τ / (2 * Real.pi * Real.cos (ω * t) ^ 2) := Real.sq_sqrt hQpos.le
    have hKne : Real.sqrt (τ / (2 * Real.pi * Real.cos (ω * t) ^ 2)) ≠ 0 :=
      (Real.sqrt_pos.mpr hQpos).ne'
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hτK : τ = Real.sqrt (τ / (2 * Real.pi * Real.cos (ω * t) ^ 2)) ^ 2
        * (2 * Real.pi * Real.cos (ω * t) ^ 2) := by
      rw [hK]; field_simp
    rw [Real.tan_eq_sin_div_cos]
    generalize Real.exp (-(1 / 2) * (τ / Real.cos (ω * t) ^ 2) * (x - w * Real.cos (ω * t)) ^ 2) = X
    revert hKne hτK
    generalize Real.sqrt (τ / (2 * Real.pi * Real.cos (ω * t) ^ 2)) = K
    intro hKne hτK
    rw [hτK]
    field_simp
    ring
