-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:56:09.217362+00:00
-- url     : https://prove2.me/theorems/9eef9138-14c2-48d1-b1b0-5798f4355474
-- title:
--   Linear–quadratic posterior exponent
-- statement:
--   For a real inner-product space $E$, a vector $c\in E$, a continuous linear map $Q:E\to E$, and $x\in E$, `quadraticExponent c Q x` is the real-valued expression $\langle c,x\rangle-\frac12\langle Qx,x\rangle$. This is the linear–quadratic exponent used to define the posterior tilt; no measure or integrability assertion is included.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E67. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean#L26-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Exponent`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The exponent `⟪c, x⟫ − ½⟪Q x, x⟫` of the BKL posterior (67) with parameters `(c, Q)`. -/
def quadraticExponent (c : E) (Q : E →L[ℝ] E) (x : E) : ℝ :=
  ⟪c, x⟫ - (1 / 2 : ℝ) * ⟪Q x, x⟫
end Posterior
end Probability
end FunctionalInequalities


