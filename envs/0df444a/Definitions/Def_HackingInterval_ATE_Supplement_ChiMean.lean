-- Prove2me | Definitions.Def_HackingInterval_ATE_Supplement_ChiMean
-- name    : HackingInterval_ATE_Supplement_ChiMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:55:17.295015+00:00
-- url     : https://prove2.me/theorems/05f3d6fa-c909-4f1b-8b3e-396165899ce6
-- title:
--   Equation (21): exact chi mean constant
-- statement:
--   For a positive integer $\nu$, define
--
--   $$\mu_\nu=\sqrt2\,\frac{\Gamma((\nu+1)/2)}{\Gamma(\nu/2)}.$$
--
--   This is the exact constant in Equation (21), used in both endpoint variance formulas of Theorem 3. The arguments of the Gamma functions are positive on the theorem's domain, so the denominator is nonzero. No asymptotic replacement or unspecified parameter is introduced.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, p. 12 (PDF 13), eq. (21)

import Mathlib
noncomputable section

namespace HackingInterval.ATE.Supplement

/-- Exact constant in Equation (21), used for ν > 0. -/
def chiMean (ν : ℕ) : ℝ :=
  Real.sqrt 2 * Real.Gamma (((ν : ℝ) + 1) / 2) / Real.Gamma ((ν : ℝ) / 2)

end HackingInterval.ATE.Supplement


