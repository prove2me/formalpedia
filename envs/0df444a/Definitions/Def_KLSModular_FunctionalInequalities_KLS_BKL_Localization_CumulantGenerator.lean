-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:11:37.07766+00:00
-- url     : https://prove2.me/theorems/f937fdfc-a22d-4fdf-a9aa-a094d34ecbc2
-- title:
--   Fixed-direction differential operator for cumulant calculations
-- statement:
--   For normed real vector spaces $U$ and $V$, `fixedOp b s f p` is the scalar expression $D f(p)[b]+\frac12\sum_k D(Df)(p)[s_k][s_k]$, where $b\in U$, $s:\operatorname{Fin}d\to U$, and $f:U\to\mathbb R$. The bundle contains this technical auxiliary definition; no cumulant-generator theorem is declared here.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator
--   import FunctionalInequalities.KLS.BKL.Localization.Coefficients
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.Probability.Posterior.LogPartition
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def fixedOp {d : ℕ} (b : U) (s : Fin d → U)
--       (f : U → ℝ) (p : U) : ℝ :=
--     fderiv ℝ f p b + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ f) p (s k) (s k)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa).
--
--   Theorems in source order:
--
--   - [`generator_cumulant_posterior`](https://prove2.me/theorems/a8578c33-036f-4c18-b2db-a9b7abd9284e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantGenerator.lean) · `FunctionalInequalities.KLS.BKL.Localization.CumulantGenerator` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantGenerator.lean#L150-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CumulantGenerator`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
section Calculus
variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
 def fixedOp {d : ℕ} (b : U) (s : Fin d → U)
    (f : U → ℝ) (p : U) : ℝ :=
  fderiv ℝ f p b + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ f) p (s k) (s k)
end Calculus
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
end Localization
end BKL
end KLS
end FunctionalInequalities


