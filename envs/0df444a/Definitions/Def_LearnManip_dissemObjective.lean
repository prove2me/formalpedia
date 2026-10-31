-- Prove2me | Definitions.Def_LearnManip_dissemObjective
-- name    : LearnManip_dissemObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:23.877071+00:00
-- url     : https://prove2.me/theorems/ddcca830-fbbd-445b-800d-8b3ab9e4d753
-- title:
--   Objective of the DP equation (13)
-- statement:
--   For a function $v(\mu,s,c)$, the objective of the DP equation (13) at a quantity $q$:
--   $$-cq+\gamma\log E_{\mu,s}\Bigl[\exp\Bigl(\frac1\gamma\bigl(\mu^q+\alpha v(\mu^q,\tfrac{s}{1+sq},c\eta)\bigr)\Bigr)\Bigr],$$
--   the expectation being under the undistorted law of $\mu^q$.
--
--   **Formalization Note.** The expectation is positive and finite for the functions the mission applies this to.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (13), p.13

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_postVar
import Definitions.Def_LearnManip_baseLaw

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The objective of the DP equation (13), p.13, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), at
the quantity `q`: `−c q + γ log E_{μ,s}[exp((μ^q + α v(μ^q, s/(1+sq), cη))/γ)]`.

**Formalization Note.** The expectation is under the undistorted law. It is positive and finite for
the functions it is applied to here (`InClass`, `vk`): the exponent is within a constant of an affine
function of `y`, so `Real.log` and the Bochner integral are not at a junk value. -/
noncomputable def dissemObjective (P : Params) (v : ℝ → ℝ≥0 → ℝ≥0 → ℝ) (μ : ℝ) (s c q : ℝ≥0) : ℝ :=
  -((c : ℝ) * q) + (P.γ : ℝ) *
    Real.log (∫ y, Real.exp ((y + (P.α : ℝ) * v y (postVar s q) (c * P.η)) / (P.γ : ℝ))
      ∂baseLaw μ s q)

end LearnManip


