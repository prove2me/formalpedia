-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:27:25.887351+00:00
-- url     : https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970
-- title:
--   Centering in the closed-gradient domain
-- statement:
--   For a full-dimensional log-concave law and the unit-weight closed gradient, `center_mem_closedWeightedOperator_domain` states that if $u$ belongs to the operator domain, then its centered class $u-\int u\,d\nu$ also belongs to that domain. The hypotheses include an explicit tilted representation $\nu=m.\operatorname{tilted}(-U)$ with $U\in C^2$, although the displayed conclusion concerns only domain stability under subtraction of a constant.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare
--   import FunctionalInequalities.Analysis.BakryEmery.Curvature
--   import FunctionalInequalities.Analysis.Semigroup.Generated.Curvature
--   import FunctionalInequalities.Analysis.Semigroup.Generated.Convergence
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel
--   import FunctionalInequalities.KLS.LogConcave.Density.Tilted
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   theorem center_mem_closedWeightedOperator_domain
--       (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
--       L2.center ν (u : Lp ℝ 2 (ν : Measure V)) ∈
--         (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/Decay`](https://prove2.me/theorems/87f7a5e4-b54d-4085-b6b9-cd0350aac65d), [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f), [`KLS/LogConcave/WeightedGradient/Poincare`](https://prove2.me/theorems/80fd6f93-3b94-490a-9376-d2fdf9e800cd), [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461), [`Analysis/Semigroup/Generated/Curvature`](https://prove2.me/theorems/2d0d4681-a28b-4386-bf7f-208cba5fd2c8), [`Analysis/Semigroup/Generated/Convergence`](https://prove2.me/theorems/bf431053-eab1-4154-9189-5a728fdc5db2), [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22), [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Theorems in source order:
--
--   - [`norm_toLp_gradient_sq`](https://prove2.me/theorems/08f6268b-f9f3-4fc1-9889-3665ced688d5)
--   - [`mul_norm_closedWeightedOperator_toLp_sq_le`](https://prove2.me/theorems/1216a9e9-dda9-49e5-b0a6-d2e0cf7acb3e)
--   - [`mul_norm_closedWeightedOperator_sq_le`](https://prove2.me/theorems/df1ab815-889d-4825-b09c-233d7b8156e8)
--   - [`closedWeightedOperator_center`](https://prove2.me/theorems/7038d041-6a2a-40bc-ab8a-0baeb48cd646)
--   - [`norm_center_sq_sub_le`](https://prove2.me/theorems/7596243b-315e-4568-9444-de9ecda59015)
--   - [`literatureConstant_le_of_gap`](https://prove2.me/theorems/b49f19dd-a419-448a-a1a8-ceb4b69486a2)
--   - [`literatureConstant_le_inv_of_tendsto`](https://prove2.me/theorems/ad4697ec-e48c-433b-b18f-ec34a0341e53)
--   - [`closedWeightedOperator_eq_zero_iff`](https://prove2.me/theorems/245eb849-5b26-4814-9a95-03fa2537cb37)
--   - [`inner_center_eq_zero_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/60306a5c-e4a6-42ad-8e3e-e1beb0e3909f)
--   - [`tendsto_norm_center_apply`](https://prove2.me/theorems/d65ce5f8-31f4-4f05-808f-036c8d89bf33)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L207-L230 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Decay
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Poincare
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
/-- Centering stays in the domain of the closed gradient: `center u ∈ D(T̄)` for `u ∈ D(T̄)`. -/
theorem center_mem_closedWeightedOperator_domain
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    L2.center ν (u : Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hconst :
      L2.const ν (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) ∈ T.domain := by
    have hone :
        L2.const ν 1 ∈ T.domain :=
      one_mem_domain_closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hν hi
    have hsmul :
        L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) • L2.const ν 1 ∈ T.domain :=
      T.domain.smul_mem
        (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) hone
    rw [← mul_one (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))),
      L2.const_smul]
    exact hsmul
  have hsub :
      (u : Lp ℝ 2 (ν : Measure V)) -
          L2.const ν (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) ∈ T.domain :=
    T.domain.sub_mem u.2 hconst
  simpa [T, L2.center] using hsub
end LogConcave
end KLS
end FunctionalInequalities


