-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.backward_kolmogorov_gaussian_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:37:47.375457+00:00
-- url     : https://prove2.me/submissions/f4d22ae6-5d4e-42f1-a8e9-fb6abc545464

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_gaussian_constant_drift
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_forward_backward_kernel_symmetry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false
theorem solution
    (b q x t y s : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ → ℝ → ℝ := fun z τ =>
      Real.exp (-((x - z - b * (t - τ)) ^ 2 / (2 * q * (t - τ)))) /
        Real.sqrt (2 * Real.pi * q * (t - τ));
    -(deriv (fun τ => p y τ) s) =
      b * deriv (fun z => p z s) y +
        q / 2 * deriv (fun z => deriv (fun w => p w s) z) y := by
  let B : ℝ -> ℝ -> ℝ := fun z u =>
    Real.exp (-((x - z - b * (t - u)) ^ 2 / (2 * q * (t - u)))) /
      Real.sqrt (2 * Real.pi * q * (t - u))
  let F : ℝ -> ℝ -> ℝ := fun z tau =>
    Real.exp (-((z - x - (-b) * (tau - s)) ^ 2 /
      (2 * q * (tau - s)))) /
      Real.sqrt (2 * Real.pi * q * (tau - s))
  change -deriv (fun u : ℝ => B y u) s =
    b * deriv (fun z : ℝ => B z s) y +
      q / 2 * deriv (fun z : ℝ =>
        deriv (fun w : ℝ => B w s) z) y
  have hsym : (∀ z : ℝ, B z s = F z t) ∧
      (∀ u : ℝ, B y u = F y (s + t - u)) :=
    AppliedSDE.SarkkaSolin.gaussian_forward_backward_kernel_symmetry
      b q y s x t
  have hspace : (fun z : ℝ => B z s) =
      (fun z : ℝ => F z t) := funext hsym.1
  have htimemap : (fun u : ℝ => B y u) =
      (fun u : ℝ => F y (s + t - u)) := funext hsym.2
  have ht : -deriv (fun u : ℝ => B y u) s =
      deriv (fun tau : ℝ => F y tau) t := by
    rw [htimemap, deriv_comp_const_sub]
    have hh : s + t - s = t := by ring
    rw [hh]
    ring
  have hs1 : deriv (fun z : ℝ => B z s) y =
      deriv (fun z : ℝ => F z t) y :=
    congrArg (fun v : ℝ -> ℝ => deriv v y) hspace
  have hs2 : deriv (fun z : ℝ =>
      deriv (fun w : ℝ => B w s) z) y =
      deriv (fun z : ℝ =>
        deriv (fun w : ℝ => F w t) z) y :=
    congrArg (fun v : ℝ -> ℝ => deriv (deriv v) y) hspace
  have hfwd : deriv (fun tau : ℝ => F y tau) t =
      -(-b) * deriv (fun z : ℝ => F z t) y +
        q / 2 * deriv (fun z : ℝ =>
          deriv (fun w : ℝ => F w t) z) y := by
    simpa [F] using
      (AppliedSDE.SarkkaSolin.fpk_gaussian_constant_drift
        (-b) q x s y t hq hst)
  rw [ht, hs1, hs2]
  simpa only [neg_neg] using hfwd
