-- Prove2me | solution 1 for Arxiv2001_06227.stealth_hyperuniform_transparency
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:53:26.866017+00:00
-- url     : https://prove2.me/submissions/e12ff541-aff6-4f0c-b0e7-35c7ae799cab

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

open Arxiv2001_06227 in
theorem solution (rho k0 kr K : ℝ) (hrho : 0 < rho) (hk0 : 0 < k0)
    (hkr : 0 < kr) (deltaEps : ℂ) (thetaHat : Space → ℂ) (sTilde : Space → ℝ)
    (u : Space) (hu : ‖u‖ = 1)
    (hstealth : ∀ q : Space, ‖q‖ < K → sTilde q = 0) (hK : 2 * kr < K) :
    invScatLength rho k0 kr deltaEps thetaHat sTilde u = 0 := by
  have h : ∀ v : Metric.sphere (0 : Space) 1, sTilde (kr • ((v : Space) - u)) = 0 := by
    intro v
    apply hstealth
    have hv : ‖(v : Space)‖ = 1 := by simpa using v.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hkr]
    have := norm_sub_le (v : Space) u
    nlinarith
  unfold invScatLength
  simp [h]
