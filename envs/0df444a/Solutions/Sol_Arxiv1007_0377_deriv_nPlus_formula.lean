-- Prove2me | solution 1 for Arxiv1007_0377.deriv_nPlus_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:50:49.289594+00:00
-- url     : https://prove2.me/submissions/58f7f430-85f5-4bc0-8609-21be2fb98bc2

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem deriv_nPlus_formula (ε μ : ℝ → ℂ) (ω : ℝ)
    (hε : DifferentiableAt ℝ ε ω) (hμ : DifferentiableAt ℝ μ ω)
    (hR : 0 < branchRadicand (ε ω) (μ ω)) :
    HasDerivAt (fun w => nPlus (ε w) (μ w))
      (1 / Real.sqrt 2 * (1 / 2) *
          (((deriv ε ω).re * (μ ω).re + (ε ω).re * (deriv μ ω).re -
              ((deriv ε ω).im * (μ ω).im + (ε ω).im * (deriv μ ω).im)) /
            Real.sqrt (branchRadicand (ε ω) (μ ω))) +
        1 / Real.sqrt 2 * (1 / 2) *
          ((deriv (fun w => ‖ε w‖) ω * ‖μ ω‖ + ‖ε ω‖ * deriv (fun w => ‖μ w‖) ω) /
            Real.sqrt (branchRadicand (ε ω) (μ ω)))) ω := by
  have hεne : ε ω ≠ 0 := by
    intro h; rw [branchRadicand, h] at hR; simp at hR
  have hμne : μ ω ≠ 0 := by
    intro h; rw [branchRadicand, h] at hR; simp at hR
  have hεr : HasDerivAt (fun w => (ε w).re) (deriv ε ω).re ω := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt ω hε.hasDerivAt
  have hεi : HasDerivAt (fun w => (ε w).im) (deriv ε ω).im ω := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt ω hε.hasDerivAt
  have hμr : HasDerivAt (fun w => (μ w).re) (deriv μ ω).re ω := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt ω hμ.hasDerivAt
  have hμi : HasDerivAt (fun w => (μ w).im) (deriv μ ω).im ω := by
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt ω hμ.hasDerivAt
  have hεn : HasDerivAt (fun w => ‖ε w‖) (deriv (fun w => ‖ε w‖) ω) ω :=
    (hε.norm ℝ hεne).hasDerivAt
  have hμn : HasDerivAt (fun w => ‖μ w‖) (deriv (fun w => ‖μ w‖) ω) ω :=
    (hμ.norm ℝ hμne).hasDerivAt
  have hB : HasDerivAt (fun w => branchRadicand (ε w) (μ w))
      (((deriv ε ω).re * (μ ω).re + (ε ω).re * (deriv μ ω).re -
              ((deriv ε ω).im * (μ ω).im + (ε ω).im * (deriv μ ω).im)) +
        (deriv (fun w => ‖ε w‖) ω * ‖μ ω‖ + ‖ε ω‖ * deriv (fun w => ‖μ w‖) ω)) ω := by
    unfold branchRadicand
    exact ((hεr.mul hμr).sub (hεi.mul hμi)).add (hεn.mul hμn)
  have hS := (hB.sqrt hR.ne').div_const (Real.sqrt 2)
  unfold nPlus
  exact hS.congr_deriv (by ring)

end Arxiv1007_0377
open Arxiv1007_0377 in
theorem solution (ε μ : ℝ → ℂ) (ω : ℝ)
    (hε : DifferentiableAt ℝ ε ω) (hμ : DifferentiableAt ℝ μ ω)
    (hR : 0 < branchRadicand (ε ω) (μ ω)) :
    HasDerivAt (fun w => nPlus (ε w) (μ w))
      (1 / Real.sqrt 2 * (1 / 2) *
          (((deriv ε ω).re * (μ ω).re + (ε ω).re * (deriv μ ω).re -
              ((deriv ε ω).im * (μ ω).im + (ε ω).im * (deriv μ ω).im)) /
            Real.sqrt (branchRadicand (ε ω) (μ ω))) +
        1 / Real.sqrt 2 * (1 / 2) *
          ((deriv (fun w => ‖ε w‖) ω * ‖μ ω‖ + ‖ε ω‖ * deriv (fun w => ‖μ w‖) ω) /
            Real.sqrt (branchRadicand (ε ω) (μ ω)))) ω :=
  deriv_nPlus_formula ε μ ω hε hμ hR
