-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:22:41.356319+00:00
-- url     : https://prove2.me/theorems/49f2d187-0409-49fa-a861-f4dcb4534ed2
-- title:
--   Smooth cutoff functions for operator-core arguments
-- statement:
--   The private definition `profile` is a fixed smooth bump equal to one on the ball of radius $5$ and supported in the ball of radius $8$. For $r\in\mathbb R$, `cutoff` is the rescaled function $\chi_r(y)=\operatorname{profile}(r^{-1}y)$; `contDiff_cutoff` gives smoothness, while `cutoff_eq_zero`, `tsupport_cutoff_subset`, and `hasCompactSupport_cutoff` give its support properties for $r>0$. These are technical cutoff facts used in operator-core estimates.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
--   import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def profile : ContDiffBump (0 : V) := ⟨5, 8, by norm_num, by norm_num⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Theorems in source order:
--
--   - [`norm_toLp_mul_cutoff_le`](https://prove2.me/theorems/70f87b8e-1e63-4a64-b689-a93e9c786f4e)
--   - [`eq_zero_of_localRegularity`](https://prove2.me/theorems/51e4b343-ce48-434b-a25f-137e75ee3400)
--   - [`exists_seq_smooth_tendsto_adjointComp_of_localRegularity`](https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L86-L130 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.WeightedGradient
section Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
/-- One fixed smooth profile, equal to one on the ball of radius five and supported in the ball
of radius eight. -/
 def profile : ContDiffBump (0 : V) := ⟨5, 8, by norm_num, by norm_num⟩
/-- The scaled cutoff `χ_r (y) = profile (r⁻¹ • y)`: one on `closedBall 0 (5 r)`, zero off
`ball 0 (8 r)`, with gradient of size `O(1/r)`. -/
 def cutoff (r : ℝ) (y : V) : ℝ := (FunctionalInequalities.KLS.LogConcave.profile (V := V)) (r⁻¹ • y)
 theorem contDiff_cutoff (r : ℝ) : ContDiff ℝ ∞ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).contDiff.comp (contDiff_id.const_smul _)
 theorem cutoff_eq_zero {r : ℝ} (hr : 0 < r) {y : V} (hy : 8 * r ≤ ‖y‖) :
    FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y = 0 := by
  apply (FunctionalInequalities.KLS.LogConcave.profile (V := V)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← div_eq_inv_mul, le_div_iff₀ hr]
  exact hy
 theorem tsupport_cutoff_subset {r : ℝ} (hr : 0 < r) :
    tsupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) ⊆ closedBall (0 : V) (8 * r) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hy (FunctionalInequalities.KLS.LogConcave.cutoff_eq_zero hr (le_of_lt (not_le.1 h)))
 theorem hasCompactSupport_cutoff {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : V) (8 * r))
    ((subset_tsupport _).trans (FunctionalInequalities.KLS.LogConcave.tsupport_cutoff_subset hr))
end Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
end LogConcave
end KLS
end FunctionalInequalities


