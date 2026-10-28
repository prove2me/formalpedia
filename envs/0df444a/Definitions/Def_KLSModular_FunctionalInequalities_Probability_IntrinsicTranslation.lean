-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_IntrinsicTranslation
-- name    : KLSModular_FunctionalInequalities_Probability_IntrinsicTranslation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:23:11.790985+00:00
-- url     : https://prove2.me/theorems/b9ce8338-e7be-450b-86d4-c0e89470d643
-- title:
--   Barycenters under translation of probability laws
-- statement:
--   `Probability.integral_id_translateLaw` states that, for an integrable identity function, translating a probability law by c translates its barycenter by c: $\int x\,d(\operatorname{translateLaw}(\nu,c))=c+\int x\,d\nu$. `integral_id_translateLaw_neg_integral` specializes this to translation by the negative barycenter and concludes that the translated law has barycenter zero. The statements do not require finite-dimensionality, although the surrounding module supplies stronger ambient structure.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Transport
--   import FunctionalInequalities.Probability.AffineSupport
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem integral_id_translateLaw (ν : ProbabilityMeasure V) (hint : Integrable id (ν : Measure V))
--       (c : V) : ∫ x, x ∂(translateLaw ν c : Measure V) = c + ∫ x, x ∂(ν : Measure V) := by
--     rw [coe_translateLaw, integral_map (measurable_const_add c).aemeasurable
--       continuous_id'.aestronglyMeasurable]
--     have hint' : Integrable (fun x : V ↦ x) (ν : Measure V) := hint
--     rw [integral_add (integrable_const c) hint', integral_const, probReal_univ, one_smul]
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Theorems in source order:
--
--   - [`affineSupport_translateLaw`](https://prove2.me/theorems/618c4d8e-695f-405d-a488-6790e221d360)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/IntrinsicTranslation.lean) · `FunctionalInequalities.Probability.IntrinsicTranslation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/IntrinsicTranslation.lean#L123-L138 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.IntrinsicTranslation`, definition bundle `KLSModular_FunctionalInequalities_Probability_IntrinsicTranslation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport

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


