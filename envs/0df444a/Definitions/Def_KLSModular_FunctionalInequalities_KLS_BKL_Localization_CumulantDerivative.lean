-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:01:54.276462+00:00
-- url     : https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8
-- title:
--   Permutation for cumulant slot reindexing
-- statement:
--   The private definition `snocToCons m` is a permutation of `Fin (m+1)` that moves the final slot to the first position and shifts the preceding slots, with explicit inverse and left/right inverse proofs. It is a technical reindexing device for parameter derivatives of posterior cumulants; the module's public cumulant-derivative statements are not included in this declaration bundle.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Coefficients
--   import FunctionalInequalities.Probability.Posterior.LogPartition
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   private def snocToCons (m : ℕ) : Equiv.Perm (Fin (m + 1))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd), [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Theorems in source order:
--
--   - [`contDiff_cumulant_posterior`](https://prove2.me/theorems/fae38448-b47c-4a2d-b61a-67ba2745ecc0)
--   - [`fderiv_cumulant_posterior_apply`](https://prove2.me/theorems/7e33f35a-71f2-43a6-bb75-a119f0e67849)
--   - [`inner_cov_apply`](https://prove2.me/theorems/9dacc562-afff-4880-8959-c09a4a246ec3)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean) · `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L53-L66 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
 def snocToCons (m : ℕ) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.mk
    (Fin.cases (Fin.last m) (fun i => i.castSucc))
    (Fin.lastCases 0 (fun i => i.succ))
    (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp)
    (by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp)
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
end Localization
end BKL
end KLS
end FunctionalInequalities


