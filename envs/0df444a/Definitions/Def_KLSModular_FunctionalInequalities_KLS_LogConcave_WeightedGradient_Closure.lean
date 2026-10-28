-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:13:27.727331+00:00
-- url     : https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2
-- title:
--   Closure of the weighted-gradient operator
-- statement:
--   For a full-dimensional log-concave probability measure $\nu$ on a finite-dimensional inner-product space $V$, a Haar measure $m$, and a bounded linear weight $B:V\to V$, `closedWeightedOperator` is the closure of the weighted-gradient operator $g\mapsto B\nabla g$ from $L^2(\nu)$ to $L^2(\nu;V)$. When $(\operatorname{int}\operatorname{supp}\nu)\ne\varnothing$, `closedWeightedOperator_isClosed` states that this operator is closed, while `dense_domain_closedWeightedOperator` states that its domain is dense in $L^2(\nu)$. The theorem `toLp_mem_closedWeightedOperator_domain_of_isTest` places every weighted-gradient test function in the domain of the closure.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev closedWeightedOperator (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) :
--       Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
--     (hν.weightedOperator m B hi).closure
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/WeightedGradient/Basic`](https://prove2.me/theorems/72f5f80b-8a06-4b88-9c28-6818c4e64bc7).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Closure.lean) · `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Closure.lean#L26-L66 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
/-- The closed weighted gradient `T̄`: the closure of `g ↦ B ∘ ∇g` on `L²(ν)`. -/
abbrev closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  (hν.weightedOperator m B hi).closure
/-- `T̄` is closed. -/
theorem closedWeightedOperator_isClosed (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.closedWeightedOperator m B hi).IsClosed :=
  (hν.weightedOperator_isClosable m B hi).closure_isClosed
/-- Every weighted-gradient test class lies in the domain of `T̄`. This is the general-test
form of `KLS.LogConcave.toLp_mem_closedWeightedOperator_domain`, whose test is smooth and
compactly supported. -/
theorem toLp_mem_closedWeightedOperator_domain_of_isTest (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {g : V → ℝ}
    (h : WeightedGradient.IsTest ν B g) :
    h.memLp.toLp g ∈ (hν.closedWeightedOperator m B hi).domain :=
  (LinearPMap.le_closure _).1
    (WeightedGradient.toLp_mem_domain_operator ν B (hν.absolutelyContinuous_haar m hi) h)
/-- `T̄` is densely defined: its domain contains the dense domain of `T`. -/
theorem dense_domain_closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.closedWeightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  (hν.dense_domain_weightedOperator m B hi).mono fun _ hx =>
    (LinearPMap.le_closure (hν.weightedOperator m B hi)).1 hx
end FullDimensional
end LogConcave
end KLS
end FunctionalInequalities


