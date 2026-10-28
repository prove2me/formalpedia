-- Prove2me | Definitions.Def_OAIQ3Ff002
-- name    : OAIQ3Ff002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T23:31:23.143702+00:00
-- url     : https://prove2.me/theorems/d423c3b8-bc4d-4218-87bd-8cedc37e4988
-- title:
--   Definitions bundle OAIQ3Ff002 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 58 definitions, 9 instances and 22 theorems. The definitions and types are `OAI.FiniteFactor.sourceFiniteReferenceKernel`, `OAI.FiniteFactor.sourceFirstCoordinate`, `OAI.FiniteFactor.sourceFirstMultiplier`, `OAI.FiniteFactor.sourceFutureBad`, `OAI.FiniteFactor.sourceFutureBoundaryEvent`, `OAI.FiniteFactor.sourceIndicatorProjection`, `OAI.FiniteFactor.sourceMissCount`, `OAI.FiniteFactor.sourceMultiplication`, `OAI.FiniteFactor.sourceNormalEvaluation`, `OAI.FiniteFactor.sourceNormalEvaluationIsometry`, `OAI.FiniteFactor.sourceNormalRieszFunctional`, `OAI.FiniteFactor.sourceNormalRieszLinear`, `OAI.FiniteFactor.sourceNormalRieszOperator`, `OAI.FiniteFactor.sourceNormalRieszVector`, `OAI.FiniteFactor.sourceOmittedBadEvent`, `OAI.FiniteFactor.sourceOmittedError`, `OAI.FiniteFactor.sourceOperator`, `OAI.FiniteFactor.sourcePhaseFailure`, `OAI.FiniteFactor.sourcePhaseFailureMajorant`, `OAI.FiniteFactor.sourcePredualIdentification`, `OAI.FiniteFactor.sourceProjectionEvent`, `OAI.FiniteFactor.sourceProjectionLeftCoefficient`, `OAI.FiniteFactor.sourceProjectionRightCoefficient`, `OAI.FiniteFactor.sourceResamplingKernel`, `OAI.FiniteFactor.sourceRotationL2`, `OAI.FiniteFactor.sourceSamplingCorrelationBudget`, `OAI.FiniteFactor.sourceSamplingCube`, `OAI.FiniteFactor.sourceSamplingCylinder`, `OAI.FiniteFactor.sourceSamplingDiagonalContribution`, `OAI.FiniteFactor.sourceSamplingEmpiricalDensity`, `OAI.FiniteFactor.sourceSamplingEmptyTest`, `OAI.FiniteFactor.sourceSamplingEndpoint`, `OAI.FiniteFactor.sourceSamplingIdealDensity`, `OAI.FiniteFactor.sourceSamplingLambdaTest`, `OAI.FiniteFactor.sourceSamplingLimitRectangleMass`, `OAI.FiniteFactor.sourceSamplingPairRepresentative`, `OAI.FiniteFactor.sourceSamplingPositiveOrbits`, `OAI.FiniteFactor.sourceSamplingProduct`, `OAI.FiniteFactor.sourceSamplingRationalEndpoints`, `OAI.FiniteFactor.sourceSamplingRationalX` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FiniteFactor_BiasedPairs_ReferenceDomination`, `FiniteFactor_CrossedProduct_CentralDiagonal`, `FiniteFactor_CrossedProduct_FreeRotation`, `FiniteFactor_CrossedProduct_FutureBoundary`, `FiniteFactor_CrossedProduct_GeneratedAlgebra`, `FiniteFactor_CrossedProduct_HilbertSeparable`, `FiniteFactor_CrossedProduct_IndicatorProjection`, `FiniteFactor_CrossedProduct_NormalFunctionalSpace`, `FiniteFactor_CrossedProduct_NormalRiesz`, `FiniteFactor_CrossedProduct_OmittedBadEvents`, `FiniteFactor_CrossedProduct_Operator`, `FiniteFactor_CrossedProduct_PhaseCount`, `FiniteFactor_CrossedProduct_PhaseDecay`, `FiniteFactor_CrossedProduct_Phases`, `FiniteFactor_CrossedProduct_PredualIdentification`, `FiniteFactor_CrossedProduct_ProjectionColumns`, `FiniteFactor_CrossedProduct_ProjectionErrors`, `FiniteFactor_CrossedProduct_ProjectionEvent`, `FiniteFactor_CrossedProduct_ReferenceMixture`, `FiniteFactor_CrossedProduct_SmallPartitionSets`, `FiniteFactor_CrossedProduct_StageOperator`, `FiniteFactor_CrossedProduct_TagGeometry`, `FiniteFactor_CrossedProduct_TailTrimming`, `FiniteFactor_CrossedProduct_TorusErgodic`, `FiniteFactor_CrossedProduct_TorusModel`, `FiniteFactor_CrossedProduct_TorusRotation`, `FiniteFactor_CrossedProduct_Trace`, `FiniteFactor_CrossedProduct_TracialRepresentation`, `FiniteFactor_CrossedProduct_VacuumFunctional`, `FiniteFactor_CrossedProduct_VacuumSeparating`, `FiniteFactor_CrossedProduct_VectorFunctionalRelations`, `FiniteFactor_OrbitSampling_CompactTorus`, `FiniteFactor_OrbitSampling_Cube`, `FiniteFactor_OrbitSampling_CylinderSystem`, `FiniteFactor_OrbitSampling_DiagonalContribution`, `FiniteFactor_OrbitSampling_Error`, `FiniteFactor_OrbitSampling_IdealProduct`, `FiniteFactor_OrbitSampling_IdealRectangleLimit`, `FiniteFactor_OrbitSampling_LambdaRectangles`, `FiniteFactor_OrbitSampling_OrbitSupport`, `FiniteFactor_OrbitSampling_ProductError`, `FiniteFactor_OrbitSampling_ProductMoments`, `FiniteFactor_OrbitSampling_RationalTests`, `FiniteFactor_OrbitSampling_SelfSummability`, `FiniteFactor_OrbitSampling_Tail`, `FiniteFactor_OrbitSampling_TestedMarginals`, `FiniteFactor_OrbitSampling_TestedTransport`, `FiniteFactor_OrbitSampling_TorusSupport`, `FiniteFactor_OrbitSampling_WeakLimit`.
--
--   **Imports.** It imports the bundle `OAIQ3Ff000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.FiniteFactor.exists_source_prepared_finite`, `OAI.FiniteFactor.sourceInvariantProjection_trivial`, `OAI.FiniteFactor.sourceOmittedError_estimate`, `OAI.FiniteFactor.sourceProjectionEvent_error_pointwise`, `OAI.FiniteFactor.sourceProjectionEvent_mass_upper`, `OAI.FiniteFactor.sourceProjection_biased_prefix_pairs`, `OAI.FiniteFactor.sourceProjection_biased_ratio_augmented`, `OAI.FiniteFactor.sourceSamplingLambda_rectangle_limit_event`, `OAI.FiniteFactor.sourceSamplingSquaredError_ae` and `OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event`; the proofs of `OAI.FiniteFactor.exists_source_prepared_finite`, `OAI.FiniteFactor.main_theorem`, `OAI.FiniteFactor.sourceBiasedPrefix_domination`, `OAI.FiniteFactor.sourceInvariantProjection_trivial`, `OAI.FiniteFactor.sourceOmittedError_estimate`, `OAI.FiniteFactor.sourceProjectionEvent_error_pointwise`, `OAI.FiniteFactor.sourceProjectionEvent_mass_upper`, `OAI.FiniteFactor.sourceProjection_biased_prefix_pairs`, `OAI.FiniteFactor.sourceProjection_biased_ratio_augmented`, `OAI.FiniteFactor.sourceSamplingLambda_rectangle_limit_event`, `OAI.FiniteFactor.sourceSamplingSquaredError_ae`, `OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event` and `OAI.FiniteFactor.sourceSampling_mass_limit_event`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ3Ff000

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Operator
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A bounded multiplication operator from the actual source formula. -/
def sourceMultiplication {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (sourceMeasure ι) ∞ 2 2
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c))

/-- T=U pi(f), constructed as a bounded operator, with no assumed factor or
invariant-subspace properties. -/
def sourceOperator {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (sourceShift ι).comp (sourceMultiplication θ c hθ hc)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_StageOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

theorem sourceLogWeight_nonneg (i : SourceCoordinate) : 0 ≤ sourceLogWeight i :=
  le_max_of_le_right (sq_nonneg _)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseCount
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

def sourceMissCount (s : ℕ) : ℕ := Nat.ceil ((19/20 : ℝ)*(sourceBlockSize s : ℝ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseDecay
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- An explicit majorant for the positive-power union bound. -/
def sourcePhaseFailureMajorant (s : ℕ) : ℝ :=
  (sourceBlockSize s : ℝ)^((4/5 : ℝ)*(sourceBlockSize s : ℝ)) *
    2^sourceBlockSize s * (10*sourceWidth s 1)^sourceMissCount s

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_IdealProduct
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingIdealDensity (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (x : SourceCoordinate → ℝ) : ℝ :=
  ∏ i ∈ sourceSamplingPrefix stage,
    samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) (x i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_ProductMoments
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingProduct (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (n : ℤ) (θ x : SourceCoordinate → ℝ) : ℝ :=
  ∏ i ∈ sourceSamplingPrefix stage,
    samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (x i) (Int.fract ((n : ℝ)*θ i))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_SelfSummability
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingSelfBudget (stage : ℕ) : ℝ :=
  (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ))^(sourceSamplingPrefix stage).card /
    ((sourceSamplingPowers stage).card : ℝ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_DiagonalContribution
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- The self-pair part of the empirical squared norm, with its actual P^-2 weight. -/
def sourceSamplingDiagonalContribution (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) : ℝ :=
  (∑ n ∈ sourceSamplingPowers stage,
    ∫ x, sourceSamplingProduct stage r b E G n θ x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) / ((sourceSamplingPowers stage).card : ℝ)^2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_ProductError
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingCorrelationBudget (stage : ℕ) : ℝ :=
  ((sourceSamplingPrefix stage).card : ℝ)*(104*(sourceBlockSize stage : ℝ)^(-74 : ℝ))*Real.exp 135

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Error
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingEmpiricalDensity (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ x : SourceCoordinate → ℝ) : ℝ :=
  (∑ n ∈ sourceSamplingPowers stage, sourceSamplingProduct stage r b E G n θ x)/
    ((sourceSamplingPowers stage).card : ℝ)

/-- The full sampling error, including every distinct-pair and mixed term. -/
def sourceSamplingSquaredError (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) : ℝ :=
  ∫ x, (sourceSamplingEmpiricalDensity stage r b E G θ x-sourceSamplingIdealDensity stage r b E G x)^2
    ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

def sourceSamplingRectangle (E G : SourceCoordinate → Set ℝ) :
    Set ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  {p | ∀ i, p.1 i ∈ E i ∧ p.2 i ∈ G i}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

def sourceSamplingEndpoint (r : Bool)
    (p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) : SourceCoordinate → ℝ :=
  if r then p.2 else p.1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_RationalTests
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingRationalEndpoints (T : SourceSamplingRationalTest) (i : SourceCoordinate) :
    (ℚ × ℚ) × (ℚ × ℚ) :=
  if hi : i ∈ T.1 then T.2 ⟨i,hi⟩ else ((0,1),(0,1))

def sourceSamplingRationalX (T : SourceSamplingRationalTest) (i : SourceCoordinate) : Set ℝ :=
  Set.Icc (sourceSamplingRationalEndpoints T i).1.1 (sourceSamplingRationalEndpoints T i).1.2

def sourceSamplingRationalY (T : SourceSamplingRationalTest) (i : SourceCoordinate) : Set ℝ :=
  Set.Icc (sourceSamplingRationalEndpoints T i).2.1 (sourceSamplingRationalEndpoints T i).2.2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_IdealRectangleLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Explicit finite-coordinate rectangle mass of the triangular/diagonal
model. The triangular term retains the actual source weight integral. -/
def sourceSamplingLimitRectangleMass (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) : ℝ :=
  ∏ i ∈ I ∪ T.1,
    if i ∈ I then
      ∫ s, samplingTestedFirstDensity true (sourceSamplingWidth 0) (sourceSamplingCutoff 0)
        (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
    else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LambdaRectangles
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingLambdaTest (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (i : SourceCoordinate) (p : ℝ × ℝ) : Prop :=
  if i ∈ I then p.1 ∈ sourceSamplingRationalX T i ∧ p.2 ∈ sourceSamplingRationalY T i ∧ p.1 < p.2
  else p.1 ∈ sourceSamplingRationalX T i ∧ p.1 ∈ sourceSamplingRationalY T i

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Cube
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingCube : Set SourceSamplingPair :=
  {p | ∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 i ∈ Set.Icc (0 : ℝ) 1}

def sourceSamplingEmptyTest : SourceSamplingRationalTest := ⟨∅,fun _ => ((0,1),(0,1))⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CylinderSystem
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Finite cylinders in the full real product: coordinates outside the
finite support are unrestricted. On the conull cube these are the original
rational tests. The ambient real product is not asserted to be compact. -/
def sourceSamplingCylinder (T : SourceSamplingRationalTest) : Set SourceSamplingPair :=
  {p | ∀ i ∈ T.1, p.1 i ∈ sourceSamplingRationalX T i ∧ p.2 i ∈ sourceSamplingRationalY T i}

def sourceSamplingTestMeet (T U : SourceSamplingRationalTest) : SourceSamplingRationalTest :=
  ⟨T.1 ∪ U.1,fun i =>
    if i.1 ∈ T.1 then
      if i.1 ∈ U.1 then
        ((max (sourceSamplingRationalEndpoints T i).1.1 (sourceSamplingRationalEndpoints U i).1.1,
          min (sourceSamplingRationalEndpoints T i).1.2 (sourceSamplingRationalEndpoints U i).1.2),
         (max (sourceSamplingRationalEndpoints T i).2.1 (sourceSamplingRationalEndpoints U i).2.1,
          min (sourceSamplingRationalEndpoints T i).2.2 (sourceSamplingRationalEndpoints U i).2.2))
      else sourceSamplingRationalEndpoints T i
    else sourceSamplingRationalEndpoints U i⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_WeakLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingUntrimmedFinite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingPair :=
  ⟨sourceSamplingUntrimmed I s θ,inferInstance⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CompactTorus
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

instance sourceSamplingTorus_compact : CompactSpace SourceSamplingTorus := inferInstance

instance sourceSamplingTorus_borel : BorelSpace SourceSamplingTorus := Prod.borelSpace

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusModel
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

def sourceTorusQuotient (x : SourceCoordinate → ℝ) : SourceTorus := fun i => (x i : UnitAddCircle)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Tail
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

def sourceTailAngleSum (θ : SourceCoordinate → ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ, ∑ i : Fin (sourceBlockSize (s+n)), θ ⟨s+n,i⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TailTrimming
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

def sourceTailOrderFailure (θ : SourceCoordinate → ℝ) (s n : ℕ) : Set (SourceCoordinate → ℝ) :=
  ⋃ r : ℕ, ⋃ i : Fin (sourceBlockSize (s+r)),
    {x | Int.fract (x ⟨s+r,i⟩+(n : ℝ)*θ ⟨s+r,i⟩) < x ⟨s+r,i⟩}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_ReferenceDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

/-- Independent diagonal-or-Haar replacement at a finite set of coordinates. -/
def sourceFiniteReferenceKernel (F : Finset SourceCoordinate) :
    Kernel (SourceCoordinate → ℝ) (SourceCoordinate → ℝ) := by
  letI : ∀ i, IsMarkovKernel (if i ∈ F then sourceDiagonalHaarKernel else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  exact independentKernel (fun i => if i ∈ F then sourceDiagonalHaarKernel else Kernel.id)

instance sourceFiniteReferenceKernel_markov (F : Finset SourceCoordinate) :
    IsMarkovKernel (sourceFiniteReferenceKernel F) := by
  unfold sourceFiniteReferenceKernel
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FreeRotation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

def sourceFirstCoordinate : SourceCoordinate :=
  ⟨0, ⟨0, by have := (sourceStage 0).m_ge_100; change 0 < (sourceStage 0).m; omega⟩⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

def sourceWeightBase (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceBaseFunction where
  toFun := fun x => (sourceCocycle θ sourceLogWeight 1 x : ℂ)
  measurable := Complex.measurable_ofReal.comp (sourceCocycle_measurable θ sourceLogWeight 1)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro x hx
    rw [Complex.norm_real, Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
    exact sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumFunctional
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceVacuum_norm : ‖sourceVacuum‖ = 1 := by
  rw [sourceVacuum,norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def,sourceMeasure,Measure.prod_prod]

section

local notation "vacuumMeasurable" =>
  @Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
    (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
      (fun _ => Real.measurableSpace)) Int.instMeasurableSpace
local notation "vacuumSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring
local notation "vacuumIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ vacuumSemiring)
local notation "vacuumHilbertGroup" =>
  @MeasureTheory.Lp.instNormedAddCommGroup
    ((SourceCoordinate → ℝ) × ℤ) ℂ vacuumMeasurable
    (@Nat.cast ENNReal
      (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
      (Nat.succ (Nat.succ Nat.zero)))
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    fact_one_le_two_ennreal
local notation "vacuumHilbertInner" =>
  @MeasureTheory.L2.innerProductSpace
    ((SourceCoordinate → ℝ) × ℤ) ℂ ℂ Complex.instRCLike
    vacuumMeasurable (sourceMeasure SourceCoordinate)
    Complex.instNormedAddCommGroup (@RCLike.innerProductSpace ℂ Complex.instRCLike)
local notation "vacuumHilbertTopology" =>
  @UniformSpace.toTopologicalSpace (SourceHilbert SourceCoordinate)
    (@PseudoMetricSpace.toUniformSpace (SourceHilbert SourceCoordinate)
      (@MetricSpace.toPseudoMetricSpace (SourceHilbert SourceCoordinate)
        (@NormedAddCommGroup.toMetricSpace (SourceHilbert SourceCoordinate) vacuumHilbertGroup)))
local notation "vacuumHilbertAddition" =>
  @AddCommGroup.toAddCommMonoid (SourceHilbert SourceCoordinate)
    (@NormedAddCommGroup.toAddCommGroup (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
local notation "vacuumHilbertModule" =>
  @NormedSpace.toModule ℂ (SourceHilbert SourceCoordinate)
    (@DenselyNormedField.toNormedField ℂ
      (@RCLike.toDenselyNormedField ℂ Complex.instRCLike))
    (@NormedAddCommGroup.toSeminormedAddCommGroup
      (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
    (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
      vacuumHilbertInner)

abbrev sourceVacuumFunctional
    (operator : @ContinuousLinearMap ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
      (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
      (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
      vacuumHilbertModule vacuumHilbertModule) : ℂ :=
  @inner ℂ (SourceHilbert SourceCoordinate)
    (@InnerProductSpace.toInner ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
      vacuumHilbertInner) sourceVacuum
    (@AddHom.toFun (SourceHilbert SourceCoordinate) (SourceHilbert SourceCoordinate)
      (vacuumHilbertAddition).toAdd (vacuumHilbertAddition).toAdd
      (@LinearMap.toAddHom ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
        (SourceHilbert SourceCoordinate) (SourceHilbert SourceCoordinate)
        vacuumHilbertAddition vacuumHilbertAddition vacuumHilbertModule vacuumHilbertModule
        (@ContinuousLinearMap.toLinearMap ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
          (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
          (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
          vacuumHilbertModule vacuumHilbertModule operator)) sourceVacuum)

end

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CentralDiagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceFirstMultiplier : SourceBaseFunction where
  toFun x := (x sourceFirstCoordinate : ℂ)
  measurable := Complex.measurable_ofReal.comp (measurable_pi_apply sourceFirstCoordinate)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x hx := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx sourceFirstCoordinate).1]
    exact (hx sourceFirstCoordinate).2.le

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_OrbitSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingPositiveOrbits (s : ℕ) (θ : SourceCoordinate → ℝ) : Set SourceSamplingPair :=
  {p | ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = coordinateRotate θ n p.1}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TorusSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

def sourceSamplingPairRepresentative (z : SourceSamplingTorus) : SourceSamplingPair :=
  (sourceTorusRepresentative z.1,sourceTorusRepresentative z.2)

def sourceSamplingTorusOrderedOrbits (s : ℕ) (θ : SourceCoordinate → ℝ) : Set SourceSamplingTorus :=
  {p | (∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i) ∧
    ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusRotation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate
noncomputable section

def sourceTorusRotationStep (θ : SourceCoordinate → ℝ) (x : SourceTorus) : SourceTorus :=
  x + sourceTorusQuotient θ

theorem sourceTorusRotationStep_preserving (θ : SourceCoordinate → ℝ) :
    MeasurePreserving (sourceTorusRotationStep θ) sourceTorusHaar sourceTorusHaar := by
  have hm (i : SourceCoordinate) : Measurable (fun z : UnitAddCircle => z + (θ i : UnitAddCircle)) := by fun_prop
  refine ⟨by unfold sourceTorusRotationStep; fun_prop,?_⟩
  change (Measure.infinitePi _).map (fun x i => x i + (θ i : UnitAddCircle)) = _
  rw [Measure.infinitePi_map_pi _ hm]
  simp only [(measurePreserving_add_right (volume : Measure UnitAddCircle) _).map_eq]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

abbrev sourceRotationL2 (θ : SourceCoordinate → ℝ) :
    Lp ℂ 2 sourceTorusHaar →ₗᵢ[ℂ] Lp ℂ 2 sourceTorusHaar :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceTorusRotationStep θ) (sourceTorusRotationStep_preserving θ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumSeparating
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- The actual constant e_0 vector separates the source double commutant. -/
theorem sourceVacuum_separating (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (hv : H sourceVacuum = 0) : H = 0 := by
  have hkill (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
      H (sourceFiberIndicator A hA n) = 0 := by
    rw [sourceFiberIndicator_eq_orbit θ A hA n]
    have hs := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceCommutantRotation θ n sourceVacuum))
      (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
    have hr := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T sourceVacuum) (sourceAlgebra_commutes_rotation θ hH n)
    change sourceScalar (sourceBaseIndicator A hA) (H (sourceCommutantRotation θ n sourceVacuum)) =
      H (sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n sourceVacuum)) at hs
    change sourceCommutantRotation θ n (H sourceVacuum) = H (sourceCommutantRotation θ n sourceVacuum) at hr
    rw [← hs, ← hr, hv]
    simp
  have hstar : star H = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change star H f = 0
    apply sourceFiberIndicators_total
    intro A hA n
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, hkill]
    simp
  exact star_eq_zero.mp hstar

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ReferenceMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters Finset
open scoped ENNReal
noncomputable section

def sourceResamplingKernel (I : Finset SourceCoordinate) :
    Kernel (SourceCoordinate → ℝ) (SourceCoordinate → ℝ) := by
  letI : ∀ i : SourceCoordinate, IsMarkovKernel
      (if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  exact independentKernel (fun i : SourceCoordinate =>
    if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id)

instance sourceResamplingKernel_markov (I : Finset SourceCoordinate) :
    IsMarkovKernel (sourceResamplingKernel I) := by
  unfold sourceResamplingKernel
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FutureBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceFutureBad (j n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) : Set SourceBiasedSample :=
  {ω | 1-sourceExclusionWidth j ⟨j+1+n,i⟩ ≤ (ω ⟨j+1+n,i⟩).2.1 ∨
    (ω ⟨j+1+n,i⟩).2.2 ≤ sourceExclusionWidth j ⟨j+1+n,i⟩}

def sourceFutureBoundaryEvent (j : ℕ) : Set SourceBiasedSample :=
  (⋃ n : ℕ, ⋃ i : Fin (sourceBlockSize (j+1+n)), sourceFutureBad j n i)ᶜ

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_HilbertSeparable
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The actual regular-representation Hilbert space is separable. This uses
the countably generated Borel structure of the countable real product times
Z and the finite exponent 2. It does not assert a predual for the algebra. -/
instance sourceHilbert_separable : TopologicalSpace.SeparableSpace (SourceHilbert SourceCoordinate) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_SmallPartitionSets
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceSmallPartitionSet (n : ℕ) (j : Fin n) : Set (SourceCoordinate → ℝ) :=
  {x | x sourceFirstCoordinate ∈ Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ))}

theorem sourceSmallPartitionSet_measurable (n : ℕ) (j : Fin n) :
    MeasurableSet (sourceSmallPartitionSet n j) :=
  measurableSet_Ico.preimage (measurable_pi_apply sourceFirstCoordinate)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_IndicatorProjection
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceIndicatorProjection (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  sourcePi θ (sourceBaseIndicator A hA)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_NormalFunctionalSpace
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

theorem sourceVectorFunctional_norm (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) :
    ‖sourceVectorFunctional θ ξ η‖ ≤ ‖ξ‖*‖η‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro A
  change ‖inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η)‖ ≤ _
  calc
    _ ≤ ‖ξ‖ * ‖(A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖A‖ * ‖η‖) := mul_le_mul_of_nonneg_left
      ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate).le_opNorm η) (norm_nonneg _)
    _ = (‖ξ‖*‖η‖)*‖A‖ := by ring

instance sourceNormalFunctionalSpace_complete (θ : SourceCoordinate → ℝ) :
    CompleteSpace (sourceNormalFunctionalSpace θ) := by
  unfold sourceNormalFunctionalSpace
  infer_instance

theorem sourceVectorFunctional_mem (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) : sourceVectorFunctional θ ξ η ∈ sourceNormalFunctionalSpace θ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(ξ,η),rfl⟩)

instance sourceNormalPredualSpace_normedGroup (θ : SourceCoordinate → ℝ) :
    NormedAddCommGroup (SourceNormalPredualSpace θ) := by
  unfold SourceNormalPredualSpace
  exact Submodule.normedAddCommGroup (E := StrongDual ℂ (SourceAlgebraSpace θ))
    (sourceNormalFunctionalSpace θ)

instance sourceNormalPredualSpace_normedSpace (θ : SourceCoordinate → ℝ) :
    NormedSpace ℂ (SourceNormalPredualSpace θ) := by
  unfold SourceNormalPredualSpace
  exact Submodule.normedSpace (𝕜 := ℂ) (E := StrongDual ℂ (SourceAlgebraSpace θ))
    (sourceNormalFunctionalSpace θ)

instance sourceNormalPredualSpace_complete (θ : SourceCoordinate → ℝ) :
    CompleteSpace (SourceNormalPredualSpace θ) :=
  inferInstanceAs (CompleteSpace (sourceNormalFunctionalSpace θ))

/-- Evaluation by each actual algebra element on the constructed space. -/
def sourceNormalEvaluation (θ : SourceCoordinate → ℝ) (A : SourceAlgebraSpace θ) :
    StrongDual ℂ (SourceNormalPredualSpace θ) := by
  exact (ContinuousLinearMap.apply ℂ ℂ A).comp
    (sourceNormalFunctionalSpace θ).subtypeL

@[simp] theorem sourceNormalEvaluation_vector (θ : SourceCoordinate → ℝ) (A : SourceAlgebraSpace θ)
    (ξ η : SourceHilbert SourceCoordinate) :
    sourceNormalEvaluation θ A ⟨sourceVectorFunctional θ ξ η,sourceVectorFunctional_mem θ ξ η⟩ =
      inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η) := rfl

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VectorFunctionalRelations
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

def sourceVectorInSpace (θ : SourceCoordinate → ℝ) (ξ η : SourceHilbert SourceCoordinate) :
    SourceNormalPredualSpace θ := ⟨sourceVectorFunctional θ ξ η,sourceVectorFunctional_mem θ ξ η⟩

theorem sourceVectorInSpace_add_left (θ : SourceCoordinate → ℝ) (ξ ξ' η : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ (ξ+ξ') η = sourceVectorInSpace θ ξ η + sourceVectorInSpace θ ξ' η := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ (ξ+ξ') (A.val η) = inner ℂ ξ (A.val η) + inner ℂ ξ' (A.val η)
  exact inner_add_left _ _ _

theorem sourceVectorInSpace_smul_left (θ : SourceCoordinate → ℝ) (c : ℂ) (ξ η : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ (c • ξ) η = star c • sourceVectorInSpace θ ξ η := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ (c • ξ) (A.val η) = star c * inner ℂ ξ (A.val η)
  exact inner_smul_left _ _ _

theorem sourceVectorInSpace_add_right (θ : SourceCoordinate → ℝ) (ξ η η' : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ ξ (η+η') = sourceVectorInSpace θ ξ η + sourceVectorInSpace θ ξ η' := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (η+η')) = inner ℂ ξ (A.val η) + inner ℂ ξ (A.val η')
  rw [map_add,inner_add_right]

theorem sourceVectorInSpace_smul_right (θ : SourceCoordinate → ℝ) (c : ℂ) (ξ η : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ ξ (c • η) = c • sourceVectorInSpace θ ξ η := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (c • η)) = c * inner ℂ ξ (A.val η)
  rw [map_smul,inner_smul_right]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_NormalRiesz
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

def sourceNormalRieszLinear (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate →ₗ[ℂ] ℂ where
  toFun ξ := star (F (sourceVectorInSpace θ ξ η))
  map_add' ξ ξ' := by
    exact (congrArg (fun v : SourceNormalPredualSpace θ => star (F v))
      (sourceVectorInSpace_add_left θ ξ ξ' η)).trans
        ((congrArg star (F.map_add _ _)).trans (star_add _ _))
  map_smul' c ξ := by
    calc
      _ = star (F (star c • sourceVectorInSpace θ ξ η)) :=
        congrArg (fun v : SourceNormalPredualSpace θ => star (F v))
          (sourceVectorInSpace_smul_left θ c ξ η)
      _ = star (star c * F (sourceVectorInSpace θ ξ η)) := congrArg star (F.map_smul (star c) _)
      _ = c * star (F (sourceVectorInSpace θ ξ η)) := by simp [star_mul,mul_comm]

theorem sourceNormalRieszLinear_bound (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η ξ : SourceHilbert SourceCoordinate) :
    ‖sourceNormalRieszLinear θ F η ξ‖ ≤ (‖F‖*‖η‖)*‖ξ‖ := by
  change ‖star (F (sourceVectorInSpace θ ξ η))‖ ≤ _
  rw [norm_star]
  calc
    _ ≤ ‖F‖*‖sourceVectorInSpace θ ξ η‖ := F.le_opNorm _
    _ ≤ ‖F‖*(‖ξ‖*‖η‖) := mul_le_mul_of_nonneg_left (sourceVectorFunctional_norm θ ξ η) (norm_nonneg _)
    _ = (‖F‖*‖η‖)*‖ξ‖ := by ring

def sourceNormalRieszFunctional (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    StrongDual ℂ (SourceHilbert SourceCoordinate) :=
  (sourceNormalRieszLinear θ F η).mkContinuous (‖F‖*‖η‖) (sourceNormalRieszLinear_bound θ F η)

def sourceNormalRieszVector (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate :=
  (InnerProductSpace.toDual ℂ (SourceHilbert SourceCoordinate)).symm (sourceNormalRieszFunctional θ F η)

theorem sourceNormalRieszVector_inner (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (ξ η : SourceHilbert SourceCoordinate) :
    inner ℂ ξ (sourceNormalRieszVector θ F η) = F (sourceVectorInSpace θ ξ η) := by
  have he := congrArg (fun f : StrongDual ℂ (SourceHilbert SourceCoordinate) => f ξ)
    ((InnerProductSpace.toDual ℂ (SourceHilbert SourceCoordinate)).apply_symm_apply
      (sourceNormalRieszFunctional θ F η))
  change inner ℂ (sourceNormalRieszVector θ F η) ξ = star (F (sourceVectorInSpace θ ξ η)) at he
  have hs := congrArg star he
  calc
    _ = star (inner ℂ (sourceNormalRieszVector θ F η) ξ) := (inner_conj_symm ξ _).symm
    _ = _ := by simpa only [star_star] using hs

theorem sourceNormalRieszVector_norm (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (η : SourceHilbert SourceCoordinate) :
    ‖sourceNormalRieszVector θ F η‖ ≤ ‖F‖*‖η‖ := by
  rw [sourceNormalRieszVector,LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/-- Every functional on the constructed Banach space gives an actual bounded
operator by Riesz representation. Membership in the source algebra is proved
separately by commutation, not assumed here. -/
def sourceNormalRieszOperator (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  LinearMap.mkContinuous
    { toFun := sourceNormalRieszVector θ F
      map_add' := fun η η' => by
        apply ext_inner_left ℂ
        intro ξ
        rw [inner_add_right,sourceNormalRieszVector_inner,sourceNormalRieszVector_inner,
          sourceNormalRieszVector_inner,sourceVectorInSpace_add_right,map_add]
      map_smul' := fun c η => by
        apply ext_inner_left ℂ
        intro ξ
        rw [inner_smul_right,sourceNormalRieszVector_inner,sourceNormalRieszVector_inner,
          sourceVectorInSpace_smul_right,map_smul]
        rfl }
    ‖F‖ (sourceNormalRieszVector_norm θ F)

theorem sourceNormalRieszOperator_inner (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) (ξ η : SourceHilbert SourceCoordinate) :
    inner ℂ ξ (sourceNormalRieszOperator θ F η) = F (sourceVectorInSpace θ ξ η) :=
  sourceNormalRieszVector_inner θ F ξ η

theorem sourceNormalRieszOperator_norm (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) : ‖sourceNormalRieszOperator θ F‖ ≤ ‖F‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Phases
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

def sourcePhaseFailure (s : ℕ) : Set (SourceCoordinate → ℝ) :=
  ⋃ n ∈ Finset.Icc 1 (Nat.floor (sourcePhaseUpper s)),
    if sourcePhaseLower s ≤ (n : ℝ) then sourceFewPhases s (n : ℤ) else ∅

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OmittedBadEvents
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The source omitted-index masks. Near tagged indices and retained terms
have empty masks. Far assignments depend on n,v and fixed angles only. -/
def sourceOmittedBadEvent (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n v : ℤ) (b : Bool) :
    Set SourceBiasedSample :=
  if h : (((sourceStageState j).K : ℤ) < |v| ∨ ((sourceStageState j).K : ℤ) < |n+v|) ∧
      sourcePhaseLower j < |(omittedIndex (sourceStageState j).K n v : ℝ)| then
    (sourceChosenAssignment θ hθ j hphase (omittedIndex (sourceStageState j).K n v) h.2.le).badEvent b
  else ∅

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PredualIdentification
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

/-- The reconstructed operator belongs to the original algebra, by its
verified double-commutant definition. -/
theorem sourceNormalRieszOperator_mem (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) :
    sourceNormalRieszOperator θ F ∈ sourceAlgebra θ := by
  rw [← (sourceAlgebra θ).commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  change inner ℂ ξ (b (sourceNormalRieszOperator θ F η)) =
    inner ℂ ξ (sourceNormalRieszOperator θ F (b η))
  have hv : sourceVectorInSpace θ ξ (b η) = sourceVectorInSpace θ (star b ξ) η := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro A
    change inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (b η)) =
      inner ℂ (star b ξ) ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η)
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      inner ℂ ξ (T η)) ((VonNeumannAlgebra.mem_commutant_iff.mp hb) A A.property)
  calc
    _ = inner ℂ (star b ξ) (sourceNormalRieszOperator θ F η) :=
      (ContinuousLinearMap.adjoint_inner_left b (sourceNormalRieszOperator θ F η) ξ).symm
    _ = F (sourceVectorInSpace θ (star b ξ) η) := sourceNormalRieszOperator_inner θ F _ η
    _ = F (sourceVectorInSpace θ ξ (b η)) := congrArg F hv.symm
    _ = _ := (sourceNormalRieszOperator_inner θ F ξ (b η)).symm

/-- Equality on actual vector functionals determines a functional on their
closed span. -/
theorem sourceNormalFunctionals_ext (θ : SourceCoordinate → ℝ)
    (F G : StrongDual ℂ (SourceNormalPredualSpace θ))
    (h : ∀ ξ η, F (sourceVectorInSpace θ ξ η) = G (sourceVectorInSpace θ ξ η)) : F = G := by
  let S : Submodule ℂ (StrongDual ℂ (SourceAlgebraSpace θ)) :=
    Submodule.span ℂ (Set.range (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
      sourceVectorFunctional θ z.1 z.2))
  have hs : ∀ φ ∈ S, ∀ hφ : φ ∈ sourceNormalFunctionalSpace θ, F ⟨φ,hφ⟩ = G ⟨φ,hφ⟩ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨⟨ξ,η⟩,rfl⟩ := hφ
      intro _
      exact h ξ η
    | zero => intro _; exact (map_zero F).trans (map_zero G).symm
    | add φ ψ hφ hψ ihφ ihψ =>
      intro hsum
      have hφ' := Submodule.le_topologicalClosure S hφ
      have hψ' := Submodule.le_topologicalClosure S hψ
      change F (⟨φ,hφ'⟩+⟨ψ,hψ'⟩) = G (⟨φ,hφ'⟩+⟨ψ,hψ'⟩)
      exact (F.map_add ⟨φ,hφ'⟩ ⟨ψ,hψ'⟩).trans
        ((congrArg₂ (· + ·) (ihφ hφ') (ihψ hψ')).trans (G.map_add ⟨φ,hφ'⟩ ⟨ψ,hψ'⟩).symm)
    | smul c φ hφ ihφ =>
      intro hsmul
      have hφ' := Submodule.le_topologicalClosure S hφ
      change F (c • ⟨φ,hφ'⟩) = G (c • ⟨φ,hφ'⟩)
      exact (F.map_smul c ⟨φ,hφ'⟩).trans
        ((congrArg (fun z : ℂ => c • z) (ihφ hφ')).trans (G.map_smul c ⟨φ,hφ'⟩).symm)
  let j : S → SourceNormalPredualSpace θ := fun φ => ⟨φ,Submodule.le_topologicalClosure S φ.property⟩
  have hd : DenseRange j := (denseRange_inclusion_iff (Submodule.le_topologicalClosure S)).mpr
    (by intro φ hφ; exact hφ)
  apply ContinuousLinearMap.ext
  intro φ
  have hsub : Set.range j ⊆ {ψ | F ψ = G ψ} := by
    rintro ψ ⟨χ,rfl⟩
    exact hs χ χ.property _
  exact (closure_minimal hsub (isClosed_eq F.continuous G.continuous)) (hd φ)

/-- Every continuous functional on the constructed separable Banach space
is evaluation by an element of the original source algebra. -/
theorem sourceNormalEvaluation_surjective (θ : SourceCoordinate → ℝ) :
    Function.Surjective (sourceNormalEvaluation θ) := by
  intro F
  refine ⟨⟨sourceNormalRieszOperator θ F,sourceNormalRieszOperator_mem θ F⟩,?_⟩
  apply sourceNormalFunctionals_ext
  intro ξ η
  exact sourceNormalRieszOperator_inner θ F ξ η

theorem sourceNormalEvaluation_norm (θ : SourceCoordinate → ℝ) (A : SourceAlgebraSpace θ) :
    ‖sourceNormalEvaluation θ A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro φ
    change ‖(φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)) A‖ ≤ _
    exact ((φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)).le_opNorm A).trans_eq (mul_comm _ _)
  · have he : sourceNormalRieszOperator θ (sourceNormalEvaluation θ A) =
        (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) := by
      apply ContinuousLinearMap.ext
      intro η
      apply ext_inner_left ℂ
      intro ξ
      exact sourceNormalRieszOperator_inner θ (sourceNormalEvaluation θ A) ξ η
    change ‖(A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)‖ ≤ _
    rw [← he]
    exact sourceNormalRieszOperator_norm θ (sourceNormalEvaluation θ A)

def sourceNormalEvaluationIsometry (θ : SourceCoordinate → ℝ) :
    SourceAlgebraSpace θ →ₗᵢ[ℂ] StrongDual ℂ (SourceNormalPredualSpace θ) where
  toFun := sourceNormalEvaluation θ
  map_add' A B := by apply ContinuousLinearMap.ext; intro φ; exact map_add (φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)) A B
  map_smul' c A := by apply ContinuousLinearMap.ext; intro φ; exact map_smul (φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)) c A
  norm_map' := sourceNormalEvaluation_norm θ

/-- The full dual identification, with the exact conjugate-linear convention
required by Target.HasSeparablePredual. -/
def sourcePredualIdentification (θ : SourceCoordinate → ℝ) :
    StrongDual ℂ (SourceNormalPredualSpace θ) ≃ₗᵢ⋆[ℂ] SourceAlgebraSpace θ :=
  (LinearIsometryEquiv.ofSurjective (sourceNormalEvaluationIsometry θ)
    (sourceNormalEvaluation_surjective θ)).symm.trans (starₗᵢ ℂ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionColumns
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ComplexConjugate
noncomputable section

def sourceProjectionLeftCoefficient (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) (k : ℤ) : ℂ :=
  leftCoefficient (fun k => sourceCocycle θ sourceLogWeight k x) (sourceProjectionColumn p x) k

def sourceProjectionRightCoefficient (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (y : SourceCoordinate → ℝ) (k : ℤ) : ℂ :=
  rightCoefficient (fun k => sourceCocycle θ sourceLogWeight k y) (sourceComplementColumn p y) k

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TagGeometry
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Endpoint consequence of a source tag; the label implication and positive
probability are separate obligations, not encoded into this predicate. -/
def sourceTagEndpointEvent (j : ℕ) : Set SourceBiasedSample :=
  {ω | ∃ i : Fin (sourceBlockSize j),
    sourceBiasedEndpoint (fun _ => false) ω ⟨j,i⟩ < 1/(sourceBlockSize j : ℝ) ∧
    1-1/(sourceBlockSize j : ℝ) ≤ sourceBiasedEndpoint (fun _ => true) ω ⟨j,i⟩}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionEvent
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

/-- The actual three conditions defining E_j in the source, with j+1 indexing. -/
def sourceProjectionEvent
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) : Set SourceBiasedSample :=
  sourceTaggedEvent j ∩ sourceBoundaryEvent j ∩ sourceDiagonalEvent p j

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionErrors
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceTruncatedCoefficient (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) (n : ℤ)
    (ω : SourceBiasedSample) : ℂ :=
  laurentProductCoefficient (sourceStageState j).K
    (sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω))
    (sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω)) (-n)

def sourceOmittedError (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℤ) (b : Bool) (ω : SourceBiasedSample) : ℝ :=
  ∑' k : ℤ, (sourceOmittedBadEvent θ hθ j hphase n k b).indicator
    (fun ω => ‖sourceProjectionColumn p (sourceBiasedEndpoint (fun _ => false) ω) k‖ *
      ‖sourceComplementColumn p (sourceBiasedEndpoint (fun _ => true) ω) (n+k)‖) ω

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Trace
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- Traciality of the actual, previously constructed normal vacuum functional. -/
theorem sourceVacuumFunctional_tracial (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (A * B) = sourceVacuumFunctional (B * A) := by
  have hh := sourceConjugation_inner_symm θ (A sourceVacuum) (B sourceVacuum)
  rw [sourceConjugation_algebra_vacuum θ hA, sourceConjugation_algebra_vacuum θ hB] at hh
  have hc := congrArg (starRingEnd ℂ) hh
  rw [inner_conj_symm, inner_conj_symm] at hc
  change inner ℂ sourceVacuum (A (B sourceVacuum)) = inner ℂ sourceVacuum (B (A sourceVacuum))
  rw [← ContinuousLinearMap.adjoint_inner_left A (B sourceVacuum) sourceVacuum,
    ← ContinuousLinearMap.adjoint_inner_left B (A sourceVacuum) sourceVacuum]
  exact hc.symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TracialRepresentation
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- Actual instantiation of the certified tracial-representation API.
Both central obligations are proved for this source algebra. -/
def sourceTracialRepresentation (θ : SourceCoordinate → ℝ) :
    TracialRepresentation (sourceAlgebra θ) where
  vector := sourceVacuum
  norm_vector := sourceVacuum_norm
  cyclic := fun S T => sourceVacuumFunctional_tracial θ S.property T.property
  separating := fun T hT => Subtype.ext (sourceVacuum_separating θ T.property hT)

end
end FiniteFactor

end OAI
end


