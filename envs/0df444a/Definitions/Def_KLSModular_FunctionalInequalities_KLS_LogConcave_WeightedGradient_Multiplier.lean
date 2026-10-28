-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:14:53.791665+00:00
-- url     : https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901
-- title:
--   Smooth compactly supported multipliers in L²
-- statement:
--   For a smooth compactly supported real function $\phi$ and any $u\in L^2(\nu)$, `memLp_mul_of_contDiff_hasCompactSupport` states that $x\mapsto\phi(x)u(x)$ belongs to $L^2(\nu)$. The result uses only the probability-law measure and the compact support of $\phi$; it is an auxiliary integrability statement for multiplier arguments involving the closed weighted gradient.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.WeightedGradient.Leibniz
--   import FunctionalInequalities.Energy.Relaxation.LinearPMap
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure
--   import FunctionalInequalities.L2.BoundedMultiplier
--   import FunctionalInequalities.Analysis.Semigroup.AdjointClosure
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem memLp_mul_of_contDiff_hasCompactSupport {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
--       (hφc : HasCompactSupport φ) (u : Lp ℝ 2 (ν : Measure V)) :
--       MemLp (fun y => φ y * u y) 2 (ν : Measure V) := by
--     obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
--     have hb : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ M :=
--       Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
--     simpa only [smul_eq_mul] using
--       L2.memLp_bddSmul (H := ℝ) hφ.continuous.aestronglyMeasurable hb u
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/WeightedGradient/Leibniz`](https://prove2.me/theorems/08f6fe2c-4617-4e99-b213-1a499a864534), [`Energy/Relaxation/LinearPMap`](https://prove2.me/theorems/2ed50aac-81dd-45da-b8c8-597e80695a44), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`L2/BoundedMultiplier`](https://prove2.me/theorems/da75691d-014d-458a-86f4-ee7ec70daa33), [`Analysis/Semigroup/AdjointClosure`](https://prove2.me/theorems/ebe7d87f-ca1a-44b6-be50-ba265ba45b7d).
--
--   Theorems in source order:
--
--   - [`exists_seq_smooth_tendsto_graph`](https://prove2.me/theorems/c7be6850-4704-4912-95fa-1692fa90fd5a)
--   - [`exists_mem_domain_closedWeightedOperator_toLp_mul`](https://prove2.me/theorems/465ec746-a212-4a4a-a2ab-2d9cca0a20ec)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean) · `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean#L113-L122 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Leibniz
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLSModular_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointClosure

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Multiplier
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- A smooth compactly supported multiplier preserves `L²(ν)`. -/
theorem memLp_mul_of_contDiff_hasCompactSupport {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (u : Lp ℝ 2 (ν : Measure V)) :
    MemLp (fun y => φ y * u y) 2 (ν : Measure V) := by
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hb : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ M :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
  simpa only [smul_eq_mul] using
    L2.memLp_bddSmul (H := ℝ) hφ.continuous.aestronglyMeasurable hb u
end Multiplier
end LogConcave
end KLS
end FunctionalInequalities


