-- Prove2me | Definitions.Def_GenEmpLik_Coverage_influence
-- name    : GenEmpLik_Coverage_influence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:04:15.109153+00:00
-- url     : https://prove2.me/theorems/60a86143-7720-47e8-98aa-ec62d655e9e4
-- title:
--   Influence function of the optimal value
-- statement:
--   When the population optimizer $x^\star$ is unique, the influence function of the optimal-value functional at $P_0$ is
--
--   $$T^{(1)}(z;P_0)=\ell(x^\star;z)-\mathbb E_{P_0}[\ell(x^\star;\xi)].$$
--
--   It is centered under $P_0$. Its variance determines the nondegenerate Gaussian limit and thus the one degree of freedom chi square calibration.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 39, Appendix C.1, display for the canonical gradient

import Mathlib

namespace GenEmpLik.Coverage

/-- The influence function T^(1)(z;P₀) in Appendix C.1, p. 39. -/
noncomputable def influence {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (xs : EuclideanSpace ℝ (Fin d)) (P₀ : MeasureTheory.Measure Ξ) (z : Ξ) : ℝ :=
  ℓ xs z - ∫ z', ℓ xs z' ∂P₀

end GenEmpLik.Coverage


