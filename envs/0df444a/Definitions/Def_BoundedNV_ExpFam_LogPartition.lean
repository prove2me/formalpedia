-- Prove2me | Definitions.Def_BoundedNV_ExpFam_LogPartition
-- name    : BoundedNV_ExpFam_LogPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:28.732277+00:00
-- url     : https://prove2.me/theorems/2c1a264a-5194-49a1-8a25-4144e14fa24d
-- title:
--   Observation, p. 575 — the log-partition function A(η₁, η₂) of the choice distributions, eq. (12)
-- statement:
--   Let $f$ be a demand density with decision domain $S$ (the smallest interval containing the support of $f$), and write $E\min(D,v)=\int\min(t,v)f(t)\,dt$. For real $\eta_1,\eta_2$ the **log-partition function** of the family of newsvendor choice distributions is (eq. (12))
--   $$A(\eta_1,\eta_2) = \ln\Big(\int_S e^{\eta_1 E\min(D,v) - \eta_2 v}\,dv\Big).$$
--
--   At the natural parameters $\eta_1 = p/\beta$, $\eta_2 = c/\beta$ the integral is the normalizer of the behavioral solution's density (11), and Proposition 2 expresses the expected order and the expected profit of the behavioral solution through the partial derivatives of $A$.
--
--   **Formalization Note** Lean's $\ln$ is $0$ at $0$ and the integral is $0$ when the integrand is not integrable, so $A$ carries a junk value outside the parameter region where the integral is finite and positive; the theorems of this mission establish that it is genuine at $(p/\beta, c/\beta)$ (Observation) and use only derivatives there.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 575 (PDF p. 10), Observation, eq. (12)

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit

namespace BoundedNV.ExpFam

/-- The log-partition function (12) of the family of choice distributions:
`A(η₁, η₂) = ln ∫_S e^{η₁ E min(D, v) − η₂ v} dv`, with `S` the decision domain of `f`. -/
noncomputable def logPartition (f : ℝ → ℝ) (η₁ η₂ : ℝ) : ℝ :=
  Real.log (∫ v in decisionDomain f, Real.exp (η₁ * BoundedNV.Uniform.expMin f v - η₂ * v))

end BoundedNV.ExpFam


