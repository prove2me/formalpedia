-- Prove2me | Definitions.Def_OAIQ036S005
-- name    : OAIQ036S005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T04:51:25.58966+00:00
-- url     : https://prove2.me/theorems/fcba445f-e7de-4594-989c-532ade4fde18
-- title:
--   Definitions bundle OAIQ036S005 of the split of OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.SK.Analytic.spinGaussianLaw`, `OAI.SK.Analytic.tripleMiddleBoundary`, `OAI.SK.Analytic.tripleMiddleSchedule`, `OAI.SK.Analytic.tripleMiddleVector`, `OAI.SK.Analytic.tripleModifiedBoundary`, `OAI.SK.Analytic.tripleReplicaCode`, `OAI.SK.Analytic.tripleRetainedMiddle`, `OAI.SK.Analytic.tripleRetainedPrefix`, `OAI.SK.Analytic.tripleSchedule`, `OAI.SK.Analytic.weightedHierarchyReplica`, `OAI.SK.Analytic.weightedHierarchyTerminalMean`, `OAI.SK.Analytic.weightedHierarchyWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SKBarriers, in whole or in part: [`SKBarriers_Hierarchy_WeightedHierarchyProbability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Hierarchy/WeightedHierarchyProbability.lean), [`SKBarriers_Hierarchy_WeightedTerminalMean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Hierarchy/WeightedTerminalMean.lean), [`SKBarriers_Replicas_OverlapCode`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/OverlapCode.lean), [`SKBarriers_Replicas_TripleBaseFactor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleBaseFactor.lean), [`SKBarriers_Replicas_TripleRecursiveExpansion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleRecursiveExpansion.lean), [`SKBarriers_Replicas_TripleRetained`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleRetained.lean), [`SKBarriers_Replicas_TripleSchedule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleSchedule.lean), [`SKBarriers_Replicas_TripleScheduleMass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/TripleScheduleMass.lean), [`SKBarriers_SpinGlass_SpinStein`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/SpinGlass/SpinStein.lean).
--
--   **Imports.** It imports the bundles `OAIQ036S002` and `OAIQ036S003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SK.Analytic.tripleConstrainedPressure_schedule` and `OAI.SK.Analytic.tripleSchedule_value_expansion`; the proofs of `OAI.SK.Analytic.exists_block_adaptive_path`, `OAI.SK.Analytic.matrixFiniteInterpolation_offset`, `OAI.SK.Analytic.narrowSchedule_value_expansion`, `OAI.SK.Analytic.signed_small_scale`, `OAI.SK.Analytic.skBlockPressure_hasDerivAt`, `OAI.SK.Analytic.tripleConstrainedPressure_quadratic`, `OAI.SK.Analytic.tripleConstrainedPressure_schedule`, `OAI.SK.Analytic.tripleSchedule_value_expansion` and `OAI.SK.main`.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SKBarriers at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ036S002
import Definitions.Def_OAIQ036S003

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SpinStein
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def spinGaussianLaw (n : ℕ) (V : S → ParameterSpace n → ℝ) (x : ℝ) :
    Measure (S × ParameterSpace n) :=
  ((Measure.count : Measure S).prod (fiberGaussian n x)).tilted (fun sz => V sz.1 sz.2)

end SpinStein
end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedHierarchyProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

def weightedHierarchyWeight (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1))
    (z : ParameterSpace n) (s : S) : ℝ :=
  hierarchyMomentLevel n m (affineLogPartition c U) (fun z => affineGibbs c U z s) j z

def weightedHierarchyReplica (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : S → S → ℝ) : ℝ :=
  ∫ z, finiteReplicaMoment (weightedHierarchyWeight n m c U j z) K
    ∂hierarchyPathLaw n m (affineLogPartition c U) 0

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedTerminalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

def weightedHierarchyTerminalMean (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) : ℝ :=
  ∫ z, affineMoment c U g z ∂hierarchyPathLaw n m (affineLogPartition c U) 0

end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_OverlapCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def tripleReplicaCode {n : ℕ} (s : ReplicaConfig n 3) : Fin 3 → Fin (n+1) :=
  ![overlapCode (s 0) (s 1),overlapCode (s 0) (s 2),overlapCode (s 1) (s 2)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleMiddleVector (δ : ℝ) : TripleMiddleIncrement → Fin 3 → ℝ
  | .inl p => ![p.2.1,δ*p.2.2,-δ*p.2.2]
  | .inr p => ![0,p.2,p.2]

def tripleMiddleSchedule (δ : ℝ) (l : List TripleMiddleIncrement) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (productMass p,tripleMiddleVector δ p))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRecursiveExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def tripleMiddleBoundary (f : ℝ → ℝ) {n : ℕ}
    (X Z : ParameterSpace n →L[ℝ] ℝ) : ParameterSpace n → ℝ :=
  fun z => f (X z)+2*f (Z z)

def tripleModifiedBoundary (f : ℝ → ℝ) {n : ℕ}
    (X Z Y : ParameterSpace n →L[ℝ] ℝ) (δ : ℝ) : ParameterSpace n → ℝ :=
  fun z => f (X z)+f (Z z+δ*Y z)+f (Z z-δ*Y z)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleRetained
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def tripleRetainedMiddle (l : List TripleMiddleIncrement) : List (ℝ × TripleRetainedState) :=
  l.map (fun p => (productMass p,productVector p))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleBaseFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleRetainedPrefix (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) : List (ℝ × TripleRetainedState) :=
  tripleRetainedCommon c++tripleRetainedMiddle (mergedProductBranches w (weightedUnderlying w))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleSchedule (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  tripleCommonSchedule c++tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))++tripleTailSchedule t

end SK.Analytic

end
end

end OAI
end


