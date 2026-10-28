-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:21:06.885348+00:00
-- url     : https://prove2.me/theorems/73466029-c8a0-4ff1-b09b-fd66281b152c
-- title:
--   Constant function in the heat-semigroup form domain
-- statement:
--   For a full-dimensional log-concave probability measure $\nu$ and any bounded linear weight $B$, `one_mem_domain_closedWeightedOperator` states that the constant class `L2.const ν 1` belongs to the domain of `closedWeightedOperator`, provided $(\operatorname{int}\operatorname{supp}\nu)\ne\varnothing$. This is an auxiliary domain statement for the closed weighted-gradient operator; it does not itself state the Markov properties of the semigroup.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Semigroup.Generated.Markov
--   import FunctionalInequalities.Energy.SmoothGradient.Dirichlet
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem one_mem_domain_closedWeightedOperator (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) :
--       L2.const ν 1 ∈ (hν.closedWeightedOperator m B hi).domain := by
--     let hac := hν.absolutelyContinuous_haar m hi
--     rw [WeightedGradient.L2_const_eq_toLp]
--     exact (hν.weightedOperator m B hi).le_closure.1
--       (WeightedGradient.toLp_mem_domain_operator ν B hac (WeightedGradient.IsTest.const 1))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Semigroup/Generated/Markov`](https://prove2.me/theorems/eb87f5d0-8e1d-478d-a79d-311567a4288c), [`Energy/SmoothGradient/Dirichlet`](https://prove2.me/theorems/9a06f3bf-ecba-4615-9943-6924b56d5b2f), [`KLS/LogConcave/HeatSemigroup/Basic`](https://prove2.me/theorems/d95536e9-6544-4702-9801-4293ad1362ac).
--
--   Theorems in source order:
--
--   - [`closedWeightedOperator_one_eq_zero`](https://prove2.me/theorems/a397e39c-598f-4ce0-b673-0b4857eee9cf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Markov.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Markov.lean#L223-L230 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Markov
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Dirichlet
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic

noncomputable section
open Filter InnerProductSpace MeasureTheory Topology
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.Euclidean
open FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
/-- The constant one belongs to the domain of the closed weighted gradient. -/
theorem one_mem_domain_closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    L2.const ν 1 ∈ (hν.closedWeightedOperator m B hi).domain := by
  let hac := hν.absolutelyContinuous_haar m hi
  rw [WeightedGradient.L2_const_eq_toLp]
  exact (hν.weightedOperator m B hi).le_closure.1
    (WeightedGradient.toLp_mem_domain_operator ν B hac (WeightedGradient.IsTest.const 1))
end LogConcave
end KLS
end FunctionalInequalities


