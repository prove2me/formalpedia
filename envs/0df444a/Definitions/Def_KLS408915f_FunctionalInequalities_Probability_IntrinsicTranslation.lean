-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
-- name    : KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:36:15.196009+00:00
-- url     : https://prove2.me/theorems/abe1f613-fd23-4586-b5c3-5a27571ffe82
-- title:
--   Barycenters under translation of probability laws
-- statement:
--   `Probability.integral_id_translateLaw` states that, for an integrable identity function, translating a probability law by c translates its barycenter by c: $\int x\,d(\operatorname{translateLaw}(\nu,c))=c+\int x\,d\nu$. `integral_id_translateLaw_neg_integral` specializes this to translation by the negative barycenter and concludes that the translated law has barycenter zero. The statements do not require finite-dimensionality, although the surrounding module supplies stronger ambient structure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/IntrinsicTranslation.lean#L123-L138 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.IntrinsicTranslation`, definition bundle `KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory Filter Topology
namespace FunctionalInequalities
namespace Probability
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
/-- The barycenter of a translated law is the translated barycenter. -/
theorem integral_id_translateLaw (ν : ProbabilityMeasure V) (hint : Integrable id (ν : Measure V))
    (c : V) : ∫ x, x ∂(translateLaw ν c : Measure V) = c + ∫ x, x ∂(ν : Measure V) := by
  rw [coe_translateLaw, integral_map (measurable_const_add c).aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V ↦ x) (ν : Measure V) := hint
  rw [integral_add (integrable_const c) hint', integral_const, probReal_univ, one_smul]
omit [FiniteDimensional ℝ V] in
/-- Translating by the negative barycenter centers the law. -/
theorem integral_id_translateLaw_neg_integral (ν : ProbabilityMeasure V)
    (hint : Integrable id (ν : Measure V)) :
    ∫ x, x ∂(translateLaw ν (-∫ x, x ∂(ν : Measure V)) : Measure V) = 0 := by
  rw [integral_id_translateLaw ν hint]
  simp
end Probability
end FunctionalInequalities


