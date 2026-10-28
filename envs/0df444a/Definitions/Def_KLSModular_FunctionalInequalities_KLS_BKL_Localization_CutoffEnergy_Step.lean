-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Step
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Step
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:45:59.103098+00:00
-- url     : https://prove2.me/theorems/6083b927-e2d3-45a6-af55-38d3d9d080a5
-- title:
--   Cutoff-energy induction hypothesis and arithmetic term
-- statement:
--   `Lemma51Bound` is a proposition asserting that, in every dimension, every compactly supported isotropic log-concave probability measure satisfying `CumulantBoundCompact 2 8` obeys the displayed generator inequality for every $r\ge 2$, direction $u$, and parameter with self-adjoint positive-semidefinite matrix component. The inequality uses the cumulant energies, the lower-drift sum, and the exact constants $1/2$ and $17$. `inductionMain K m δ` is the explicit real arithmetic expression involving the envelope, binomial coefficients, and square roots used in the cutoff induction step; the bundle does not prove `Lemma51Bound`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Integral
--   import FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment
--   import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Bound
--   import FunctionalInequalities.KLS.BKL.CumulantEnvelope
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity
--   import FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Integral
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   def Lemma51Bound : Prop
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Energy/Integral`](https://prove2.me/theorems/f4a73439-9c30-4a80-a66d-ff72b684af83), [`KLS/BKL/Localization/Lyapunov/Moment`](https://prove2.me/theorems/efd9f37b-5ca3-4919-b8ed-5afbf25b7a3c), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7), [`KLS/BKL/Localization/Energy/Bound`](https://prove2.me/theorems/4ab05ed1-3d8d-48ff-a6a8-e41faa7f3068), [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/CutoffEnergy/Boundary`](https://prove2.me/theorems/fc1e6296-7365-450f-8b02-bedf52fdeb49), [`KLS/BKL/Localization/Energy/Regularity`](https://prove2.me/theorems/a5950f32-4ea5-4584-9d29-8056c7b809f6), [`KLS/BKL/Localization/Lyapunov/Bound`](https://prove2.me/theorems/aa56646a-429f-4f7a-b76b-db51e21f5aa2), [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa).
--
--   Theorems in source order:
--
--   - [`cutoffEnergyClaim_succ`](https://prove2.me/theorems/8ae5977b-ab49-4d46-8c59-295ce589f83a)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Step.lean) · `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Step` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Step.lean#L32-L66 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Step`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Step`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
/-- **BKL Lemma 5.1 as a hypothesis** (its generator form with `C = 17`, in every dimension): for every compactly
supported isotropic log-concave prior with the third-order bound (79), every `m = r + 1 ≥ 3`, direction `u` and
parameter with symmetric PSD `Q`,
`½ E_{m+1} − 17 m² E_m − 2 ⟨κ_m(u), L_m(u)⟩ ≤ 𝓛 E_m`. Discharged by `generator_cumulantEnergy_ge` once that is canonical. -/
def Lemma51Bound : Prop :=
  ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support),
    KLS.Isotropic μ → KLS.LogConcave μ → LogConcave.Suspension.CumulantBoundCompact 2 8 →
    ∀ (r : ℕ), 2 ≤ r → ∀ (u : EuclideanSpace ℝ (Fin n)) (q : Param n),
      IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      (1 / 2 : ℝ) * cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1) u
        - 17 * ((r : ℝ) + 1) ^ 2 *
          cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u
        - 2 * ∑ K : Fin r → Fin n,
            cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
                (Fin.cons u fun s => inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
              lowerDrift (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
                (Fin.cons u fun s => inverseSqrt (cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ≤
      generator μ hc
        (fun q' : Param n => cumulantEnergy (compactPosterior μ hc q'.1 q'.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) q
 def inductionMain (K : ℝ) (m : ℕ) (δ : ℝ) : ℝ :=
  17 * (m : ℝ) ^ 2 * (2 * (envelope K (m - 1) + δ)) +
    2 * ∑ a ∈ Finset.Icc 2 (m - 2),
      ((m - 1).choose (a - 1) : ℝ) *
        Real.sqrt (envelope K (m - a + 1)) *
        (Real.sqrt (2 * (envelope K (m - 1) + δ)) *
          Real.sqrt (2 * (envelope K a + δ)))
end Localization
end BKL
end KLS
end FunctionalInequalities


