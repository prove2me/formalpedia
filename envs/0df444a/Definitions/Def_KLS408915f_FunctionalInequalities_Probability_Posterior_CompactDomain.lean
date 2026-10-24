-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
-- name    : KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:58:09.30561+00:00
-- url     : https://prove2.me/theorems/526bd264-9486-4251-a85d-988b07483a32
-- title:
--   Compactly supported quadratic posterior law
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space with compact support, `compactPosterior μ hc c Q` is the probability measure whose underlying measure is the tilt of $\mu$ by $x\mapsto\langle c,x\rangle-\frac12\langle Qx,x\rangle$. The probability structure is justified by `isProbabilityMeasure_tilted_quadraticExponent_of_compact`, and the definition permits every $c$ and continuous linear map $Q$.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E67. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactDomain.lean#L26-L30 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactDomain`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The BKL posterior `μ.tilted (⟪c,·⟫ − ½⟪Q·,·⟫)` of a compactly supported prior, as a probability law
(every finite `(c, Q)`, including `0` and negative `Q`). -/
def compactPosterior (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (c : E) (Q : E →L[ℝ] E) : ProbabilityMeasure E :=
  ⟨(μ : Measure E).tilted (quadraticExponent c Q), isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q⟩
end Posterior
end Probability
end FunctionalInequalities


