-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:13:59.547833+00:00
-- url     : https://prove2.me/theorems/9ec9f121-cade-4400-bbdd-811b2f170da2
-- title:
--   Smooth directional derivative helper
-- statement:
--   `contDiff_fderiv_apply_infty` states that if $f:V\to\mathbb{R}$ is $C^\infty$, then for every fixed $v\in V$ the function $y\mapsto Df(y)[v]$ is also $C^\infty$. It is a technical regularity lemma supporting the weak Hessian and curvature-form development; the module's larger statements concern the closed heat-model gradient and its domain.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
--   import FunctionalInequalities.KLS.LogConcave.Density.Tilted
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private theorem contDiff_fderiv_apply_infty {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (v : V) :
--       ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
--     ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f), [`Analysis/BakryEmery/Bochner/Temperate`](https://prove2.me/theorems/3d0b9fbe-846b-4821-b768-fdcecccd6374), [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Theorems in source order:
--
--   - [`exists_seq_smooth_tendsto_weakHessian`](https://prove2.me/theorems/710e036c-fb9b-40b7-ba2f-f65dc86dd10f)
--   - [`compLp_innerSL_closedWeightedOperator_comm`](https://prove2.me/theorems/9523c342-5f06-4597-bd28-317e4e2a8f9d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean#L64-L67 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Temperate
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.WeightedGradient
section Partial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- A directional derivative of a smooth function is smooth. -/
 theorem contDiff_fderiv_apply_infty {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (v : V) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
variable [CompleteSpace V] [FiniteDimensional ℝ V]
end Partial
end LogConcave
end KLS
end FunctionalInequalities


