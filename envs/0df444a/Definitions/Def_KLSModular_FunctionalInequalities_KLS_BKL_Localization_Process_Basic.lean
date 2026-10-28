-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:34:12.376618+00:00
-- url     : https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918
-- title:
--   Cutoff Eldan localization process predicate
-- statement:
--   `IsEldanCutoff μ hc W ℱ hW γ p` defines the cutoff Eldan process for a probability measure $\mu$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ with compact support and parameter process $p_t$. It requires that the coordinate representation of $p_t$ under `stateEquiv (Param n)` is an `IsDiffusion` with transported cutoff drift `transportDrift ... (cutoffDrift μ hc γ)`, transported cutoff noise `transportNoise ... (cutoffNoise μ hc γ)`, and initial state corresponding to zero. The predicate is conditional on a Brownian motion, filtration, Brownian-filtration hypotheses, and cutoff function $\gamma$; it does not itself assert existence.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Coefficients
--   import FunctionalInequalities.Probability.Diffusion.Transport
--   import FunctionalInequalities.Probability.Diffusion.Setup
--   import FunctionalInequalities.Probability.Diffusion.Existence
--   import FunctionalInequalities.Probability.Diffusion.Dynkin
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
--   def IsEldanCutoff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
--       (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (γ : Param n → ℝ)
--       (p : ℝ → Ω → Param n) : Prop :=
--     IsDiffusion W ℱ hW (transportDrift (stateEquiv (Param n)) (cutoffDrift μ hc γ))
--       (transportNoise (stateEquiv (Param n)) (cutoffNoise μ hc γ)) (stateEquiv (Param n) 0)
--       (fun t ω => stateEquiv (Param n) (p t ω))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Diffusion/Transport`](https://prove2.me/theorems/d4891633-0f13-4f16-95c2-a8857d3d0e3e), [`Probability/Diffusion/Setup`](https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd), [`Probability/Diffusion/Existence`](https://prove2.me/theorems/523c289a-088b-456f-9966-2cf2f32eb8dc), [`Probability/Diffusion/Dynkin`](https://prove2.me/theorems/ee9571d4-2835-4ab8-aa76-a9be712193b7), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`KLS/BKL/Posterior/Regularity`](https://prove2.me/theorems/d3a1b3f7-aa50-410c-a659-85a6897688cc), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`exists_isEldanCutoff`](https://prove2.me/theorems/c19ca091-9b2b-4723-a463-2678e5d1f088)
--   - [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8)
--   - [`IsEldanCutoff.dynkin`](https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba)
--   - [`IsEldanCutoff.ae_inner_Q_eq_integral`](https://prove2.me/theorems/996b9078-50df-4528-8085-8b31a80e5f6a)
--   - [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean) · `FunctionalInequalities.KLS.BKL.Localization.Process.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L32-L40 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Setup
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Dynkin
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/-- **The cutoff Eldan process** (BKL arXiv:2610.05474v1, (67), with cutoff coefficients `γ² · drift`, `γ · noise`)
in parameter-space form: its coordinates under `stateEquiv (Param n)` form an `IsDiffusion` with the transported cutoff coefficients, started at `p₀ = (0, 0)`. -/
def IsEldanCutoff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (γ : Param n → ℝ)
    (p : ℝ → Ω → Param n) : Prop :=
  IsDiffusion W ℱ hW (transportDrift (stateEquiv (Param n)) (cutoffDrift μ hc γ))
    (transportNoise (stateEquiv (Param n)) (cutoffNoise μ hc γ)) (stateEquiv (Param n) 0)
    (fun t ω => stateEquiv (Param n) (p t ω))
end Localization
end BKL
end KLS
end FunctionalInequalities


