-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:20:04.266704+00:00
-- url     : https://prove2.me/theorems/d95536e9-6544-4702-9801-4293ad1362ac
-- title:
--   Heat semigroup from the closed weighted gradient
-- statement:
--   For a full-dimensional log-concave probability law $\nu$, Haar measure $m$, weight $B$, and $t\ge 0$, `HeatSemigroup.operator` defines a continuous linear operator on $L^2(\nu)$ by applying the abstract generated-semigroup construction to the closed weighted gradient `closedWeightedOperator`. It is the operator-theoretic realization of $P_t=\exp(-t\overline T^{\dagger}\overline T)$, where $\overline T$ is the closed weighted-gradient operator.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Semigroup.Generated.Generator
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Closure
--   import Mathlib.MeasureTheory.Function.L2Space
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def operator (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
--       {t : ℝ} (ht : 0 ≤ t) : Lp ℝ 2 (ν : Measure V) →L[ℝ] Lp ℝ 2 (ν : Measure V) :=
--     FunctionalInequalities.Analysis.Semigroup.Generated.operator (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
--       (hν.dense_domain_closedWeightedOperator m B hi) ht
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Semigroup/Generated/Generator`](https://prove2.me/theorems/4116615d-8652-46e9-ac77-48d88ebf2d17), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Basic.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Basic.lean#L52-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
namespace HeatSemigroup
/-- **The heat semigroup of `ν`**: `P_t = exp (-t T̄†T̄)` on `L²(ν)`, for `t ≥ 0`, obtained from the
abstract construction `FunctionalInequalities.Analysis.Semigroup.Generated.operator` applied to the closed weighted gradient. -/
def operator (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) : Lp ℝ 2 (ν : Measure V) →L[ℝ] Lp ℝ 2 (ν : Measure V) :=
  FunctionalInequalities.Analysis.Semigroup.Generated.operator (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
end HeatSemigroup
variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
end FullDimensional
end LogConcave
end KLS
end FunctionalInequalities


