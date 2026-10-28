-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:10:30.44837+00:00
-- url     : https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101
-- title:
--   Compact-support cumulant and Letwin hypotheses
-- statement:
--   `CumulantBoundCompact d b` is the universal statement that every compactly supported isotropic log-concave probability measure in every dimension satisfies the order-$d+1$ coordinate cumulant-square bound with constant $b$. `LetwinCompactBound` is the universal positive-dimensional statement that every compactly supported isotropic log-concave probability measure satisfies `LetwinQuadraticBound`. Both are hypotheses encoded as propositions; this bundle does not prove either bound or the associated compact approximation mentioned in the module documentation.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.LocalThirdCumulant
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation
--   import FunctionalInequalities.KLS.LogConcave.Transport
--   import FunctionalInequalities.KLS.LogConcave.Isotropic
--   import FunctionalInequalities.Analysis.Operator.InverseSqrt
--   import FunctionalInequalities.Probability.Transport
--   import FunctionalInequalities.Probability.Conditioning
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def CumulantBoundCompact (d : ℕ) (b : ℝ) : Prop :=
--     ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
--       KLS.Isotropic ν → _root_.FunctionalInequalities.KLS.LogConcave ν →
--         IsCompact (ν : Measure (EuclideanSpace ℝ (Fin m))).support →
--         ∀ u : EuclideanSpace ℝ (Fin m),
--         ∑ J : Fin d → Fin m, cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
--           (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/LocalThirdCumulant`](https://prove2.me/theorems/5dd0d47b-4529-48fb-b87a-289ddd8332b0), [`Analysis/BakryEmery/Cumulant/Truncation`](https://prove2.me/theorems/1997edb8-3ab3-4dc8-9655-6994bac1ddde), [`KLS/LogConcave/Transport`](https://prove2.me/theorems/e2b06803-5a96-41cf-bc8d-6b89b02cb255), [`KLS/LogConcave/Isotropic`](https://prove2.me/theorems/35471368-b77f-4600-8554-699e6845e252), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`Probability/Conditioning`](https://prove2.me/theorems/b0c5089d-02c8-45e7-8c38-91aba9c55475).
--
--   Theorems in source order:
--
--   - [`cumulantBoundCompact_two_of_letwinCompact`](https://prove2.me/theorems/5e9f20a0-75af-4b56-97f4-5f51be0ce81a)
--   - [`norm_sub_one_le_of_isPositive_mul_self`](https://prove2.me/theorems/eb4c41c1-de2e-4b9b-953d-d2442f523791)
--   - [`opNorm_le_of_inner_eq`](https://prove2.me/theorems/1886b5dc-8b60-448e-812c-d2f3b3c38710)
--   - [`inner_self_pos_of_norm_sub_one_lt`](https://prove2.me/theorems/3500b35b-5a79-4cfe-8a40-9807fb6246e9)
--   - [`exists_standardized`](https://prove2.me/theorems/b86ffa3f-dfc6-43a2-8cd2-8a6a6fc5a590)
--   - [`cumulantBound_of_compact`](https://prove2.me/theorems/642ea310-0dfa-47d8-b6bd-18048856ed8f)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean) · `FunctionalInequalities.KLS.BKL.CompactReduction` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L31-L49 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CompactReduction`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_LocalThirdCumulant
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Conditioning

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace Suspension
/-- `CumulantBound d b` restricted to compactly supported laws: `R^ν_{d+1} ≤ b Id` for every compactly
supported isotropic log-concave probability measure in every dimension (BKL arXiv:2610.05474v1, p. 19:
Theorem 4.1 is proved for compactly supported laws first). This names the hypothesis. -/
def CumulantBoundCompact (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν → _root_.FunctionalInequalities.KLS.LogConcave ν →
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin m))).support →
      ∀ u : EuclideanSpace ℝ (Fin m),
      ∑ J : Fin d → Fin m, cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2
/-- Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for compactly supported isotropic
log-concave laws in positive dimension: the input of BKL Lemma 4.2 used by the localization argument.
This names the hypothesis; it is the interface between the Letwin and the Theorem 4.1 streams. -/
def LetwinCompactBound : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
    _root_.FunctionalInequalities.KLS.LogConcave μ → KLS.Isotropic μ →
      IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support →
      LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))
end Suspension
end LogConcave
end KLS
end FunctionalInequalities


