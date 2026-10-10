-- Prove2me | solution 1 for ActuarialValuation.cm1ForceTermFactor_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:20:27.143483+00:00
-- url     : https://prove2.me/submissions/5745deb6-fc5c-4916-b76c-2ba1fb9a8137

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ForceTermFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ T t : ℝ) (hk : δ+μ ≠ 0) :
    deriv (cm1ForceTermFactor δ μ T) t =
      -Real.exp (-(δ+μ)*(T-t)) := by
  let k : ℝ := δ + μ
  have hneq : k ≠ 0 := hk
  have hdiff : HasDerivAt (fun x : ℝ => T - x) (-1) t :=
    (hasDerivAt_id t).const_sub T
  have hlinear :
      HasDerivAt (fun x : ℝ => -k * (T - x)) ((-k) * (-1)) t :=
    hdiff.const_mul (-k)
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-k * (T - x)))
        (Real.exp (-k * (T - t)) * ((-k) * (-1))) t := by
    convert (Real.hasDerivAt_exp (-k * (T - t))).comp t hlinear using 1 <;>
      try rfl <;> try { funext x; rfl } <;>
      try { funext x; ring! } <;> try ring! <;>
      try { simp [mul_comm, neg_mul_neg] }
  have hnum :
      HasDerivAt (fun x : ℝ => 1 - Real.exp (-k * (T - x)))
        (-(Real.exp (-k * (T - t)) * ((-k) * (-1)))) t :=
    hexp.const_sub (1 : ℝ)
  have hquot :
      HasDerivAt (fun x : ℝ => (1 - Real.exp (-k * (T - x))) / k)
        (-(Real.exp (-k * (T - t)) * ((-k) * (-1))) / k) t :=
    hnum.div_const k
  change deriv (fun x : ℝ =>
    (1 - Real.exp (-k * (T - x))) / k) t =
    -Real.exp (-k * (T - t))
  calc
    deriv (fun x : ℝ => (1 - Real.exp (-k * (T - x))) / k) t =
      (-(Real.exp (-k * (T - t)) * ((-k) * (-1))) / k) := hquot.deriv
    _ = -Real.exp (-k * (T - t)) := by
      apply (div_eq_iff hneq).2
      ring!
