-- Prove2me | Definitions.Def_BetaCoskew_ThreeMoment_Supplement_Objective
-- name    : BetaCoskew_ThreeMoment_Supplement_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:37:50.644131+00:00
-- url     : https://prove2.me/theorems/4c344747-2401-4dd2-8f3e-e717089434d0
-- title:
--   §2.1, p. 8 — RDU objective (corrected: Stieltjes weights at atoms and endpoint utility)
-- statement:
--   Let $\mu$ be the probability law of a nonnegative payoff $X$, let $F$ be its CDF, and let $w$ satisfy Assumption 1(iii). The corrected RDU distribution $\nu_w$ has CDF
--
--   $$
--   G(x)=1-w(1-F(x)).
--   $$
--   Define $u_e(x)=u(x)$ for $x>0$ and $u_e(0)=\lim_{t\downarrow0}u(t)\in[-\infty,\infty)$. Its objective is the signed extended expectation $\int u_e\,d\nu_w$. A value is asserted only when the integrand is measurable and the positive and negative integrals are not both infinite. This handles nonintegrable negative utility without assigning it zero.
--
--   At a payoff atom $x$, its weight is $G(x)-G(x-)$, rather than $w'(1-F(x))\mu\{x\}$. This is an explicit correction to the printed derivative-times-CDF formula, not an assertion that those two formulae agree at atoms. The original formula gives a certain payoff $c>0$ the value $u(c)w'(0)$; for $w(p)=p^2$ this is zero. DISPROOF.md gives a complete counterexample to the printed Theorem 1 and explains this distributional correction. The published base objective remains a separate referenced definition.
--
--   **Formalization Note** The Stieltjes measure is constructed from the monotone function $G$ using its right limit. Since $w$ is continuous on $[0,1]$ and $F$ is right-continuous, $G$ is already right-continuous. No quantile representation of the objective is assumed. Extended-real subtraction is used only under an explicit guard excluding two infinite parts. At zero the infimum of utility over positive wealth gives its right limit; an arbitrary real value $u(0)$ is ignored.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), pp. 8–10, §2.1, (2) and Theorem 1; atomic correction documented in DISPROOF.md

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment.Supplement

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The atom-corrected RDU distribution, with CDF 1 - w(1 - F).
Taking the right limit gives a Stieltjes function. Under WeightingAssumption,
the displayed function is already right-continuous, so the limit changes nothing.
This intentionally corrects, rather than redefines, the published real rdu. -/
noncomputable def distortedLaw (w : ℝ → ℝ) (hw : WeightingAssumption w)
    (μ : Measure ℝ) : Measure ℝ :=
  (show Monotone (fun x : ℝ => 1 - w (1 - cdf μ x)) from by
    intro x y hxy
    apply sub_le_sub_left
    apply hw.strictMonoOn.monotoneOn
    · constructor <;> linarith [cdf_nonneg μ y, cdf_le_one μ y]
    · constructor <;> linarith [cdf_nonneg μ x, cdf_le_one μ x]
    · exact sub_le_sub_left ((cdf μ).mono hxy) 1).stieltjesFunction.measure

/-- Utility at zero is its genuine limit from positive wealth, possibly -∞.
An arbitrary total-function value u(0) never enters the optimization. -/
noncomputable def extendedUtility (u : ℝ → ℝ) (x : ℝ) : EReal :=
  if 0 < x then (u x : EReal) else
    sInf ((fun t : ℝ => (u t : EReal)) '' Ioi 0)

/-- Positive and negative parts of the corrected distributional objective. -/
noncomputable def objectivePos (μ : Measure ℝ) (u w : ℝ → ℝ)
    (hw : WeightingAssumption w) : ℝ≥0∞ :=
  ∫⁻ x, (extendedUtility u x).toENNReal ∂(distortedLaw w hw μ)

noncomputable def objectiveNeg (μ : Measure ℝ) (u w : ℝ → ℝ)
    (hw : WeightingAssumption w) : ℝ≥0∞ :=
  ∫⁻ x, (-extendedUtility u x).toENNReal ∂(distortedLaw w hw μ)

/-- A genuine signed extended expectation. Both infinite parts are explicitly
forbidden; measurability is part of the assertion, not an optimizer premise. -/
def HasRduValue (μ : Measure ℝ) (u w : ℝ → ℝ)
    (hw : WeightingAssumption w) (v : EReal) : Prop :=
  AEMeasurable (extendedUtility u) (distortedLaw w hw μ) ∧
    (objectivePos μ u w hw ≠ ⊤ ∨ objectiveNeg μ u w hw ≠ ⊤) ∧
    v = (objectivePos μ u w hw : EReal) - (objectiveNeg μ u w hw : EReal)

end BetaCoskew.ThreeMoment.Supplement


