-- Prove2me | Definitions.Def_BoundedNVAudit_Stakes_LogitLaw
-- name    : BoundedNVAudit_Stakes_LogitLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:03.227332+00:00
-- url     : https://prove2.me/theorems/6e70acd8-acdd-4561-b69f-5a0f48f606b0
-- title:
--   Genuine continuous logit normalizer and law
-- statement:
--   Let $S\subseteq\mathbb R$ be a decision domain, $u:\mathbb R\to\mathbb R$ a utility, and $\beta$ a real parameter. Normalizability means that $e^{u/\beta}$ is integrable over $S$ and its real integral $Z$ is positive. For the source model $\beta>0$ is supplied explicitly by the goal. The measure is
--
--   $$\mu(A)=\int_A\mathbf1_S(x)\frac{e^{u(x)/\beta}}{Z}\,dx.$$
--
--   The file reuses the published density and constructs its measure using a nonnegative density with respect to Lebesgue measure. It introduces no payoff moment or nonconstancy condition. On the goal's domain it is proved to be a probability measure. Outside the normalizable domain the total formula is not designated a behavioral decision.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4):566–589, 2008, doi:10.1287/msom.1070.0200, §3, equation (2), printed p. 571 (PDF p. 6); Proposition 5 proof, printed p. 587 (PDF p. 22)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit

namespace BoundedNVAudit.Stakes

open MeasureTheory

/-- Existence of the continuous logit law in Su (2008), (2), printed p. 571.
Integrability and a positive integral mean a genuinely finite, nonzero normalizer.
No payoff moment is imposed. The parameter's positive domain is supplied by the goal. -/
def LogitNormalizable (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) : Prop :=
  IntegrableOn (fun x => Real.exp (u x / β)) S ∧
    0 < ∫ x in S, Real.exp (u x / β)

/-- The measure with the published logit density; probability normalization is a theorem
on the normalizable domain, not a field assuming any source-model conclusion. -/
noncomputable def logitMeasure (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (BoundedNV.Uniform.logitDensity S u β x))

end BoundedNVAudit.Stakes


