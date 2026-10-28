-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:46:07.699279+00:00
-- url     : https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74
-- title:
--   Eldan localization coefficients and admissible cutoffs
-- statement:
--   For $p=(c,Q)$ in `Localization.Param n`, where $c∈EuclideanSpace ℝ (Fin n)$ and $Q$ is an arbitrary continuous linear operator on that space, `cov` is the covariance operator of the compact posterior associated with a probability measure `μ` and compact support hypothesis `hc`. The definitions `drift`, `noise`, and `generator` use $A^{-1}a$, $A^{-1}$, and the inverse square root of $A$ to form the diffusion coefficients, while `cutoffDrift` and `cutoffNoise` multiply them by $γ^2$ and $γ$, respectively. `IsCutoff γ` requires a globally Lipschitz cutoff, compact support, and pointwise values in $[0,1]$.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   import FunctionalInequalities.Analysis.Cutoff.LipschitzBall
--   import FunctionalInequalities.KLS.BKL.Posterior.Regularity
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev Param (n : ℕ) :=
--     EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2), [`Analysis/Cutoff/LipschitzBall`](https://prove2.me/theorems/ff179ecc-cd31-4939-9396-b1ea0665ce64), [`KLS/BKL/Posterior/Regularity`](https://prove2.me/theorems/d3a1b3f7-aa50-410c-a659-85a6897688cc).
--
--   Theorems in source order:
--
--   - [`locallyLipschitz_noise`](https://prove2.me/theorems/aa73acec-6bb4-4a4c-a7ca-0777d3c209ba)
--   - [`cutoffCoefficients_admissible`](https://prove2.me/theorems/b3c27db8-2231-4fb1-9cdc-cc4964163df3)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean) · `FunctionalInequalities.KLS.BKL.Localization.Coefficients` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean#L24-L58 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Coefficients`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity

noncomputable section
open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
/-- Parameter space `p = (c, Q)` of the Eldan localization equations (BKL arXiv:2610.05474v1, (67));
`Q` is not required to be symmetric. -/
abbrev Param (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/-- The posterior covariance `A(p) = Cov μ_{c,Q}`. -/
def cov (p : Param n) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
/-- Drift of (67): `(A⁻¹ a, A⁻¹)`. -/
def drift (p : Param n) : Param n :=
  (Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2), Ring.inverse (cov μ hc p))
/-- Noise columns of (67): `(A^{-1/2} e_k, 0)`. -/
def noise (p : Param n) (k : Fin n) : Param n :=
  (inverseSqrt (cov μ hc p) (EuclideanSpace.single k 1), 0)
/-- The generator `𝓛` of (67): `𝓛F = DF[(A⁻¹a, A⁻¹)] + ½ Σ_k D²F[(A^{-1/2}e_k, 0), (A^{-1/2}e_k, 0)]`. -/
def generator (F : Param n → ℝ) (p : Param n) : ℝ :=
  diffusionGenerator (drift μ hc) (noise μ hc) F p
/-- Cutoff drift `γ² · (A⁻¹ a, A⁻¹)`. -/
def cutoffDrift (γ : Param n → ℝ) (p : Param n) : Param n := (γ p) ^ 2 • drift μ hc p
/-- Cutoff noise `γ · (A^{-1/2} e_k, 0)`. -/
def cutoffNoise (γ : Param n → ℝ) (p : Param n) (k : Fin n) : Param n := γ p • noise μ hc p k
/-- An admissible cutoff: Lipschitz, compactly supported, `[0, 1]`-valued. -/
structure IsCutoff (γ : Param n → ℝ) : Prop where
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K γ
  compactSupport : HasCompactSupport γ
  mem_Icc : ∀ p, γ p ∈ Set.Icc (0 : ℝ) 1
end Localization
end BKL
end KLS
end FunctionalInequalities


