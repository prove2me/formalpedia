-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:16:51.433601+00:00
-- url     : https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7
-- title:
--   Lyapunov function and trace-coordinate maps for localization
-- statement:
--   For $n\in\mathbb N$, `Vec n` is the Euclidean space $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and `Op n` is its space of continuous linear endomorphisms. The maps `entryMap` and `traceMap` evaluate an operator through inner products with coordinate basis vectors, with `traceMap` summing the diagonal entries. Given a probability measure $\mu$ on `Vec n` whose support is compact, `lyapunov μ hc p` is the real-valued function $1+\|p.1\|^2+\|p.2\|_{HS}^2+\operatorname{tr}(\operatorname{cov}(\mu,p)^{-1})^2$ for a localization parameter $p$.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
--   import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
--   import FunctionalInequalities.KLS.BKL.Localization.NoiseBound
--   import FunctionalInequalities.Analysis.Operator.HilbertSchmidt
--   import FunctionalInequalities.Probability.Diffusion.VectorGenerator
--   import FunctionalInequalities.Probability.Diffusion.InverseCalculus
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.KLS.BKL.Posterior.Regularity
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/CovarianceGenerator`](https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1), [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8), [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72), [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34), [`Probability/Diffusion/VectorGenerator`](https://prove2.me/theorems/a27154a7-c41b-4d48-aa0c-9939263debb7), [`Probability/Diffusion/InverseCalculus`](https://prove2.me/theorems/c78d55be-9c73-46d5-85f1-1fc1bf677188), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`KLS/BKL/Posterior/Regularity`](https://prove2.me/theorems/d3a1b3f7-aa50-410c-a659-85a6897688cc), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`contDiff_lyapunov`](https://prove2.me/theorems/4f60de76-3e6c-470a-94e3-d3d2e0b1126e)
--   - [`generator_norm_sq_fst`](https://prove2.me/theorems/fff7723a-0c09-4862-bd3f-d8025b08ca9d)
--   - [`generator_hsNormSq_snd`](https://prove2.me/theorems/458648f7-5e6d-495f-af0b-3e5a75b3e463)
--   - [`fderiv_stdTrace_ringInverse_cov_noise`](https://prove2.me/theorems/428086ba-248f-46b6-b406-de56d14e5026)
--   - [`generator_stdTrace_ringInverse_cov`](https://prove2.me/theorems/8d08a995-5fda-4412-91ca-edf9a5b73120)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean) · `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L24-L184 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_InverseCalculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
 abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)
 abbrev Op (n : ℕ) := FunctionalInequalities.KLS.BKL.Localization.Vec n →L[ℝ] FunctionalInequalities.KLS.BKL.Localization.Vec n
 def entryMap {n : ℕ} (x y : FunctionalInequalities.KLS.BKL.Localization.Vec n) : FunctionalInequalities.KLS.BKL.Localization.Op n →L[ℝ] ℝ :=
  (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ (FunctionalInequalities.KLS.BKL.Localization.Vec n) y)
 def traceMap {n : ℕ} : FunctionalInequalities.KLS.BKL.Localization.Op n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    FunctionalInequalities.KLS.BKL.Localization.entryMap (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i)
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/-- The Lyapunov function `𝒱(c, Q) = 1 + ‖c‖² + ‖Q‖²_HS + (tr A(p)⁻¹)²` of the localization (67) (non-explosion of
the cutoff Eldan processes, uniformly in the cutoff). -/
def lyapunov (p : Param n) : ℝ :=
  1 + ‖p.1‖ ^ 2 + hsNormSq p.2 + stdTrace (Ring.inverse (cov μ hc p)) ^ 2
end Localization
end BKL
end KLS
end FunctionalInequalities


