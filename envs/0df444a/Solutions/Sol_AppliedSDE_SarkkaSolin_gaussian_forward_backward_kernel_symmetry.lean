-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_forward_backward_kernel_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:37:13.033024+00:00
-- url     : https://prove2.me/submissions/93fcdf06-6116-4686-b033-5e2a33a8d6f4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (b q y s x t : ℝ) :
    let B : ℝ -> ℝ -> ℝ := fun z u =>
      Real.exp (-((x - z - b * (t - u)) ^ 2 / (2 * q * (t - u)))) /
        Real.sqrt (2 * Real.pi * q * (t - u))
    let F : ℝ -> ℝ -> ℝ := fun z tau =>
      Real.exp (-((z - x - (-b) * (tau - s)) ^ 2 /
        (2 * q * (tau - s)))) /
        Real.sqrt (2 * Real.pi * q * (tau - s))
    (∀ z : ℝ, B z s = F z t) ∧
      (∀ u : ℝ, B y u = F y (s + t - u)) := by
  intro B F
  constructor
  · intro z
    dsimp [B, F]
    have hpow : (x - z - b * (t - s)) ^ 2 =
      (z - x - (-b) * (t - s)) ^ 2 := by ring
    rw [hpow]
  · intro u
    dsimp [B, F]
    have hd : (s + t - u) - s = t - u := by ring
    rw [hd]
    have hpow : (x - y - b * (t - u)) ^ 2 =
      (y - x - (-b) * (t - u)) ^ 2 := by ring
    rw [hpow]
