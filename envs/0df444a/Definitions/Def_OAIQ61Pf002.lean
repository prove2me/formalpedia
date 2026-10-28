-- Prove2me | Definitions.Def_OAIQ61Pf002
-- name    : OAIQ61Pf002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T22:02:41.915004+00:00
-- url     : https://prove2.me/theorems/321379bb-626a-43af-813c-795d6e12a9e5
-- title:
--   Definitions bundle OAIQ61Pf002 of the split of OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 132 definitions, 4 instances and 12 theorems. The definitions and types are `OAI.SphericalPerceptronFreeEnergy.markedTangentTriple`, `OAI.SphericalPerceptronFreeEnergy.negativeClique`, `OAI.SphericalPerceptronFreeEnergy.negativeMatrices`, `OAI.SphericalPerceptronFreeEnergy.normalizedPatternLog`, `OAI.SphericalPerceptronFreeEnergy.oneDecoratedVisit`, `OAI.SphericalPerceptronFreeEnergy.paddedControlNodes`, `OAI.SphericalPerceptronFreeEnergy.pairRestorationBound`, `OAI.SphericalPerceptronFreeEnergy.parametricHeatVelocity`, `OAI.SphericalPerceptronFreeEnergy.patchControl`, `OAI.SphericalPerceptronFreeEnergy.pathControlCost`, `OAI.SphericalPerceptronFreeEnergy.patternMatrices`, `OAI.SphericalPerceptronFreeEnergy.poissonLaplace`, `OAI.SphericalPerceptronFreeEnergy.prefixBlock`, `OAI.SphericalPerceptronFreeEnergy.pureLabelIndex`, `OAI.SphericalPerceptronFreeEnergy.pureLabelResponse`, `OAI.SphericalPerceptronFreeEnergy.quadraticCascadeReciprocalSlope`, `OAI.SphericalPerceptronFreeEnergy.quantileRoundLaw`, `OAI.SphericalPerceptronFreeEnergy.quantileSpinLaw`, `OAI.SphericalPerceptronFreeEnergy.quantileTrial`, `OAI.SphericalPerceptronFreeEnergy.relabelBlock`, `OAI.SphericalPerceptronFreeEnergy.replaceBlock`, `OAI.SphericalPerceptronFreeEnergy.replaceEvent`, `OAI.SphericalPerceptronFreeEnergy.restorationReciprocal`, `OAI.SphericalPerceptronFreeEnergy.roundTime`, `OAI.SphericalPerceptronFreeEnergy.roundedCavityValue`, `OAI.SphericalPerceptronFreeEnergy.roundedLevelCode`, `OAI.SphericalPerceptronFreeEnergy.roundedPairCoeff`, `OAI.SphericalPerceptronFreeEnergy.roundedPairFunction`, `OAI.SphericalPerceptronFreeEnergy.roundedProfileMoment`, `OAI.SphericalPerceptronFreeEnergy.roundedSingleCoeff`, `OAI.SphericalPerceptronFreeEnergy.sampleQuantileLower`, `OAI.SphericalPerceptronFreeEnergy.sampleQuantileUpper`, `OAI.SphericalPerceptronFreeEnergy.scalarArray`, `OAI.SphericalPerceptronFreeEnergy.scalarBlock`, `OAI.SphericalPerceptronFreeEnergy.scalarPairMatrixTest`, `OAI.SphericalPerceptronFreeEnergy.scalarRestorationPairMoment`, `OAI.SphericalPerceptronFreeEnergy.scalarRestorationSingleMoment`, `OAI.SphericalPerceptronFreeEnergy.sharedMarksHamiltonian`, `OAI.SphericalPerceptronFreeEnergy.singleRestorationBound`, `OAI.SphericalPerceptronFreeEnergy.sourceBaseEnergy` and 92 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Perceptron_Brownian_CountableGaussianField`, `Perceptron_Cascade_EnrichedPoissonVariance`, `Perceptron_Cascade_PoissonLaplace`, `Perceptron_Cascade_WeightedTotalBiasedLaw`, `Perceptron_Cascade_WeightedTrialLaw`, `Perceptron_Cavity_BulkAnnealedTangent`, `Perceptron_Cavity_BulkCavityRecursion`, `Perceptron_Cavity_BulkMarkedArray`, `Perceptron_Cavity_CavityRoundedLower`, `Perceptron_Cavity_FreshDensity`, `Perceptron_Cavity_FreshMomentLimit`, `Perceptron_Cavity_FreshReference`, `Perceptron_Cavity_FreshReplicaKernel`, `Perceptron_Cavity_LabelFreshKernel`, `Perceptron_Cavity_LabelFreshLog`, `Perceptron_Control_ControlDrift`, `Perceptron_Control_ControlledPrefix`, `Perceptron_Control_StepControl`, `Perceptron_Control_StepControlTail`, `Perceptron_Interpolation_FieldArray`, `Perceptron_Interpolation_KernelInfiniteReplica`, `Perceptron_Interpolation_OverlapArray`, `Perceptron_Interpolation_OverlapBlock`, `Perceptron_Interpolation_PerturbationContact`, `Perceptron_Interpolation_ReplicaIBP`, `Perceptron_Interpolation_TripleGaussianReplica`, `Perceptron_Pressure_CountableTerminalRestoration`, `Perceptron_Pressure_PatternMatrices`, `Perceptron_Pressure_TerminalVariational`, `Perceptron_Pressure_VectorPartition`, `Perceptron_Sphere_UnitSphereTangent`, `Perceptron_Variational_AnnealedIBP`, `Perceptron_Variational_AtomicPairVisitLaw`, `Perceptron_Variational_BackwardScore`, `Perceptron_Variational_BoundedC1`, `Perceptron_Variational_CompactRestorationWitness`, `Perceptron_Variational_Contact`, `Perceptron_Variational_CountableSingleRestoration`, `Perceptron_Variational_CouplingKernel`, `Perceptron_Variational_CovarianceMatrix`, `Perceptron_Variational_DensityDerivative`, `Perceptron_Variational_DensityLipschitz`, `Perceptron_Variational_EnrichedUniformBounds`, `Perceptron_Variational_EnrichedVarianceBound`, `Perceptron_Variational_Field`, `Perceptron_Variational_FieldContinuity`, `Perceptron_Variational_FieldDerivative`, `Perceptron_Variational_FieldRounding`, `Perceptron_Variational_FieldWord`, `Perceptron_Variational_FixedCount`, `Perceptron_Variational_GlobalContact`, `Perceptron_Variational_GlobalContactLimit`, `Perceptron_Variational_IndexedGaussianCovariance`, `Perceptron_Variational_IndexedGaussianCovarianceLaw`, `Perceptron_Variational_IndexedVisit`, `Perceptron_Variational_IntegratedConvex`, `Perceptron_Variational_LabelPairTestValue`, `Perceptron_Variational_LabelProfileReference`, `Perceptron_Variational_LabelProfileSingleReference`, `Perceptron_Variational_LabelRestorationKernel`, `Perceptron_Variational_LabelRestorationMoments2`, `Perceptron_Variational_LabelRestorationPair`, `Perceptron_Variational_LabelRestorationSingle`, `Perceptron_Variational_LabelRestoredValue`, `Perceptron_Variational_LabelSingleRestoredValue`, `Perceptron_Variational_LabelValue`, `Perceptron_Variational_ProbabilityMaps`, `Perceptron_Variational_ProductMarkLaw`, `Perceptron_Variational_PureLabel`, `Perceptron_Variational_QuantileReference`, `Perceptron_Variational_QuantileUpperTail`, `Perceptron_Variational_RoundedCoupling`, `Perceptron_Variational_RoundedLaw`, `Perceptron_Variational_RoundedMarkedSelection`, `Perceptron_Variational_StableLaplaceConstant`, `Perceptron_Variational_StableMassKernel`, `Perceptron_Variational_StableTotalBiasedLaw`, `Perceptron_Variational_SynchronizedLimit`, `Perceptron_Variational_TripleIndex`, `Perceptron_Variational_UniformGrid`.
--
--   **Imports.** It imports the published bundle `Def_PerceptronFreeEnergy`; the bundles `OAIQ61Pf000` and `OAIQ61Pf001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit`, `OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good`, `OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control`, `OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth`, `OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean_integral`, `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists`, `OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap`, `OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog_fresh`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_perturbation_comparison`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_poissonMean`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative`, `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_memLp`, `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_variance`, `OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog_value`, `OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value`, `OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness`, `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior`, `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_positive_density`, `OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law`, `OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate`, `OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_density`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_exists`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_limit_field_along`, `OAI.SphericalPerceptronFreeEnergy.source_perturbation_contact_exists` and `OAI.SphericalPerceptronFreeEnergy.source_zeroField_original_compare`; the proofs of `OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto`, `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data`, `OAI.SphericalPerceptronFreeEnergy.bulk_limit_geometry`, `OAI.SphericalPerceptronFreeEnergy.bulk_limit_gg`, `OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency`, `OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit`, `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists`, `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_evaluation`, `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value`, `OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good`, `OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit`, `OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error`, `OAI.SphericalPerceptronFreeEnergy.compactGG_freshLog_control`, `OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth`, `OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform`, `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG`, `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights`, `OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused_integral`, `OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old`, `OAI.SphericalPerceptronFreeEnergy.indexedTerminalPairMean_integral`, `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists`, `OAI.SphericalPerceptronFreeEnergy.main`, `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists`, `OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap`, `OAI.SphericalPerceptronFreeEnergy.sourceCountExpectedLog_fresh`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_density_comparison`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_patternFree`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_perturbation_comparison`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_poissonMean`, `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure_pure_derivative`, `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_memLp`, `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure_variance`, `OAI.SphericalPerceptronFreeEnergy.sourceLabelFreshLog_value`, `OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value`, `OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness`, `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior`, `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_positive_density`, `OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law`, `OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate`, `OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_density`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_exists`, `OAI.SphericalPerceptronFreeEnergy.source_global_contact_limit_field_along`, `OAI.SphericalPerceptronFreeEnergy.source_perturbation_contact_exists` and `OAI.SphericalPerceptronFreeEnergy.source_zeroField_original_compare`.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000
import Definitions.Def_OAIQ61Pf001

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {S : Type*}

def truncatedCountableGaussianField (v : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ) :=
  gaussianPrefixField (maskedGaussianCoefficient v L) n

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonLaplace
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def poissonLaplace {S : Type*} [MeasurableSpace S] (f : S → ℝ) (η : Measure S) : ℝ :=
  expNegENNReal (∫⁻ x, ENNReal.ofReal (f x) ∂η)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_VectorPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
  {W : S → ℝ} {V : S → StrongDual ℝ E}

def vectorLogDerivative (W : S → ℝ) (V : S → StrongDual ℝ E) (x : E) : StrongDual ℝ E :=
  (vectorPartition ρ W V x)⁻¹ • (∫ s, Real.exp (W s + V s x) • V s ∂ρ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def stableLaplaceConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1-Real.exp (-Real.exp x)) ∂stableLogIntensity b

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

open TopologicalSpace

open scoped Polynomial

def terminalTrial (m : Trial) (r : Time) : Trial where
  toFun := fun t => if r ≤ t then 1 else m t
  monotone := by
    intro s t hst
    by_cases hs : r ≤ s
    · simp only [ite_eq_left hs,ite_eq_left (hs.trans hst)]
      exact le_rfl
    · by_cases ht : r ≤ t
      · simpa only [ite_eq_right hs,ite_eq_left ht] using m.le_one s
      · simpa only [ite_eq_right hs,ite_eq_right ht] using m.monotone hst
  measurable := Measurable.ite measurableSet_Ici measurable_const m.measurable
  nonneg := by intro t; split_ifs; norm_num; exact m.nonneg t
  le_one := by intro t; split_ifs; exact le_rfl; exact m.le_one t

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlDrift
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def pathControlCost (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (m t * v t ω ^ 2) ∂timeLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def terminalVariational (P : Measure BrownianPath) (α : ℝ) (f : ℝ →ᵇ ℝ) : EReal :=
  ⨅ m : Trial, ((α * controlValue P f m : ℝ) : EReal) + (entropy m).toEReal

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedC1
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

def parametricHeatVelocity (g : Jet3) : List HeatIntervalParam → ℝ → (ℝ→ᵇ ℝ)
  | [], _ => 0
  | p::ps, t => p.rate • heatGenerator p.coefficient (parametricHeatJet g (p::ps) t) +
      heatTiltCLM (p.duration t).toNNReal p.coefficient (parametricHeatJet g ps t).f
        (parametricHeatVelocity g ps t)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableMassKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable

instance stableMassKernel_finite : IsFiniteKernel stableMassKernel := by
  refine ⟨1, by simp, ?_⟩
  intro η
  change (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ)⁻¹ *
    (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ) ≤ 1
  exact ENNReal.inv_mul_le_one _

def stableCountKernel : Kernel (Measure ℝ) ℝ :=
  stableMassKernel.withDensity (fun η x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x)))

instance stableCountKernel_sFinite : IsSFiniteKernel stableCountKernel :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

@[fun_prop] lemma measurable_fin_cons {A : Type*} [MeasurableSpace A] {n : ℕ}
    {f : A → ℝ} {g : A → Fin n → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => (Fin.cons (f a) (g a) : Fin (n+1) → ℝ)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp hg

def stableDistinctMoment : List ℝ → {m : ℕ} → Measure ℝ → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | r::rs, _, η, z => ∫⁻ x, if ∃ i, z i = x then 0 else
      ENNReal.ofReal (Real.exp (r*x))*stableDistinctMoment rs η (Fin.cons x z) ∂stableCountKernel η

instance stableLogIntensity_noAtoms (b : ℝ) : NullSingletonClass (stableLogIntensity b) := by
  unfold stableLogIntensity
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableTotalBiasedLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable

def stableTotalBiasedLaw (a b : ℝ) : Measure (Measure ℝ) :=
  normalizedMeasure ((poissonRandomMeasureLaw (stableLogIntensity b)).withDensity
    (fun η => ENNReal.ofReal (stablePoissonTotal η^a)))

def stableOrderedDistinctMass (rs : List ℝ) (η : Measure ℝ) {m : ℕ} (z : Fin m → ℝ) : ℝ≥0∞ :=
  stableDistinctMoment rs η z*ENNReal.ofReal (stablePoissonTotal η^(-rs.sum))

def stableBlockProbability : List ℕ → {m : ℕ} → Measure ℝ → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | n::ns, _, η, z => ∫⁻ x, if ∃ i, z i = x then 0 else
      (stableMassKernel η {x})^(n-1)*stableBlockProbability ns η (Fin.cons x z) ∂stableMassKernel η

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedTotalBiasedLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable
section MarkedStable
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]

def weightedTotalBiasedLaw (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) (F : S → ℝ) :
    Measure (Measure (ℝ × S)) :=
  normalizedMeasure ((poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).withDensity
    (fun η => ENNReal.ofReal (poissonWeightedTotal F η^a)))

end MarkedStable

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProductMarkLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

def quadraticCascadeReciprocalSlope (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeReciprocalSlope σ b n (fun i => z i.succ)+
      (1/(quadraticCascadePrecision σ b n (fun i => z i.succ))-
        1/(quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_EnrichedPoissonVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma patternPrefix_measurable (N M : ℕ) : Measurable (patternPrefix N M) := by
  unfold patternPrefix
  fun_prop

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapBlock
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

section Positivity

variable {Ω : Type*} [MeasurableSpace Ω]

def negativeMatrices (n : ℕ) (δ : ℝ) : Set (OverlapBlock n) :=
  {q | ∀ i j : Fin n, i < j → q i j < -δ}

def negativeClique (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (δ : ℝ) : Set Ω :=
  (overlapBlock R n) ⁻¹' negativeMatrices n δ

end Positivity

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def prefixBlock {n m : ℕ} (h : n ≤ m) (Q : OverlapBlock m) : OverlapBlock n :=
  fun a b => Q (Fin.castLE h a) (Fin.castLE h b)

def starMatrices (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    Set (OverlapBlock (r + 1 + k)) :=
  {Q | prefixBlock (Nat.le_add_right (r + 1) k) Q ∈ s ∧
    ∀ j : Fin (r + 1 + k), j.val ≠ r → Q ⟨r, by omega⟩ j < t}

def starEvent (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    Set OverlapArray :=
  copyEvent r s r ∩ {Q | ∀ j < r + 1 + k, j ≠ r → Q r j < t}

def relabelBlock {n : ℕ} (e : Equiv.Perm (Fin n)) (B : OverlapBlock n) : OverlapBlock n :=
  fun i j => B (e i) (e j)

def replaceBlock {n : ℕ} (p : Fin n) (j : ℕ) (Q : OverlapArray) : OverlapBlock n :=
  fun a b => Q (replaceIndex p j a) (replaceIndex p j b)

def replaceEvent {n : ℕ} (p : Fin n) (s : Set (OverlapBlock n)) (j : ℕ) : Set OverlapArray :=
  replaceBlock p j ⁻¹' s

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternMatrices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def patternMatrices {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) : Set (OverlapBlock n) :=
  {B | ∀ i j, i ≠ j → B i j ∈ C (labels i) (labels j)}

open Matrix
open scoped InnerProductSpace

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleIndex
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def triangleEvent (a b c t : ℝ) : Set OverlapArray :=
  {Q | Q 0 1 < a ∧ b < Q 0 2 ∧ Q 0 2 < t ∧ c < Q 1 2 ∧ Q 1 2 < t}

def scalarArray (f : ℝ × ℝ → ℝ) (Q : PairedOverlapArray) : OverlapArray :=
  fun i j => f (Q i j)

def scalarBlock (f : ℝ × ℝ → ℝ) {n : ℕ} (Q : PairedOverlapBlock n) : OverlapBlock n :=
  fun i j => f (Q i j)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma sourceGaussianRow_measurable {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (i : ℕ) : Measurable (sourceGaussianRow p d h u i) :=
  indexedGaussianRow_measurable _ _ (enrichedFeature_continuous _ _ _ _ _).measurable i

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

def sourceGaussianTestFeature (N : ℕ) (p : Fin N → ℕ) (j : Fin N) :
    NormalizedSpin N → EnrichedMark N N p := enrichedFeature N N p 0 (Pi.single j 1)

def sourceGaussianTestRow {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (j : Fin N) :
    ℕ → NormalizedSpin N×IndexedLeaf k → ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k
    (profileGaussianRoot (enrichedCoordinateLevel p d h))
    (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceGaussianTestFeature N p j)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ReplicaIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceJointMonomial {N k : ℕ} (p d : Fin N → ℕ) (j : Fin N)
    (x y : NormalizedSpin N×IndexedLeaf k) : ℝ :=
  (((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ))^(d j)*spinOverlap x.1 y.1^(p j)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedVarianceBound
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceCascadeRealization (n k : ℕ) (p : Fin (n+1) → ℕ)
    (a : IndexedCascadeBase k × (ℕ → ℝ)) :=
  ((indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) a.2).1,
    indexedCascadeRealize k (a.1,(indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) a.2).2))

def sourceDisorderRealization (n k : ℕ) (p : Fin (n+1) → ℕ) :
    SourceIndexedDisorder n k → ℕ × ((ℕ → Fin (n+1) → ℝ) ×
      (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k)) :=
  Prod.map id (Prod.map id (sourceCascadeRealization n k p))

def sourceIndexedPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) : SourceIndexedDisorder n k → ℝ :=
  enrichedRandomPressure n k f p d u h ∘ sourceDisorderRealization n k p

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceDisorderReassoc (n k : ℕ) (a : SourceBaseData n k × (ℕ → ℝ)) : SourceIndexedDisorder n k :=
  (a.1.1,(a.1.2.1,(a.1.2.2,a.2)))

def sourceBaseEnergy (n k : ℕ) (f : ℝ →ᵇ ℝ) (h : Fin (k+1) → ℝ)
    (a : SourceBaseData n k) : NormalizedSpin (n+1) × IndexedLeaf k → ℝ :=
  enrichedIndexedBoundedEnergy n a.1 k f (patternPrefix (n+1) a.1 a.2.1) h

lemma sourceBaseEnergy_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (h : Fin (k+1) → ℝ) :
    Measurable (Function.uncurry (sourceBaseEnergy n k f h)) := by
  have hm : Measurable (fun a : ℕ × (((ℕ → Fin (n+1) → ℝ) × IndexedCascadeBase k) ×
      (NormalizedSpin (n+1) × IndexedLeaf k)) =>
      sourceBaseEnergy n k f h (a.1,a.2.1) a.2.2) := by
    apply measurable_from_prod_countable_right
    intro M
    exact ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp
      (((patternPrefix_measurable (n+1) M).comp measurable_fst.fst).prodMk measurable_snd.fst)).sub measurable_const
  exact hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

def sourceKernelPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  (1/(n+1:ℕ))*Real.log (tiltPartition (sourceSpinLeafKernel n k a.1)
    (enrichedIndexedHamiltonian n a.1.1 k f (patternPrefix (n+1) a.1.1 a.1.2.1) p d h u a.2) 1)

def sourceCouplingHamiltonian (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (a : SourceBaseData n k × (ℕ → ℝ)) :=
  enrichedIndexedHamiltonian n a.1.1 k f (patternPrefix (n+1) a.1.1 a.1.2.1) p d h u a.2

def sourceCouplingEnergy (n k : ℕ) (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (j : Fin (n+1)) (a : SourceBaseData n k × (ℕ → ℝ))
    (x : NormalizedSpin (n+1) × IndexedLeaf k) :=
  perturbationAmplitude (n+1) (fun _ => 1) j*
    countableGaussianField (sourceGaussianTestRow p d h j)
      (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) a.2 x

lemma sourceCouplingBase_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (h : Fin (k+1) → ℝ) :
    Measurable (fun a : (SourceBaseData n k × (ℕ → ℝ)) ×
      (NormalizedSpin (n+1) × IndexedLeaf k) => sourceBaseEnergy n k f h a.1.1 a.2) :=
  (sourceBaseEnergy_measurable n k f h).comp (measurable_fst.fst.prodMk measurable_snd)

lemma sourceCouplingField_measurable (n k : ℕ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) :
    Measurable (fun a : (SourceBaseData n k × (ℕ → ℝ)) ×
      (NormalizedSpin (n+1) × IndexedLeaf k) =>
      countableGaussianField (sourceGaussianRow p d h u)
        (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) a.1.2 a.2) :=
  measurable_disorder_state_lift (countableGaussianField_measurable
    (sourceGaussianRow_measurable p d h u) (indexedGaussianRowLength_measurable k))

lemma sourceCouplingHamiltonian_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) :
    Measurable (Function.uncurry (sourceCouplingHamiltonian n k f p d h u)) := by
  exact (sourceCouplingBase_measurable n k f h).add (sourceCouplingField_measurable n k p d h u)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Contact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceCouplingMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k a.1)
    (fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x)
    (sourceCouplingEnergy n k p d h j a) 1

def sourceCouplingThermal (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  let H := fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x
  let Y := sourceCouplingEnergy n k p d h j a
  Real.sqrt (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k a.1) H
    (fun x => |Y x-tiltMean (sourceSpinLeafKernel n k a.1) H Y 1|) 1

def sourceCouplingVariance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  let H := fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x
  let Y := sourceCouplingEnergy n k p d h j a
  (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k a.1) H
    (fun x => (Y x-tiltMean (sourceSpinLeafKernel n k a.1) H Y 1)^2) 1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AnnealedIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceCouplingCovariance (n k : ℕ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (x y : NormalizedSpin (n+1)×IndexedLeaf k) :=
  perturbationAmplitude (n+1) (fun _ => 1) j * perturbationAmplitude (n+1) u j *
    sourceJointMonomial p d j x y

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceJointOverlap {N k : ℕ} (x y : NormalizedSpin N×IndexedLeaf k) : CompactJointOverlap :=
  (⟨spinOverlap x.1 y.1,abs_le.mp (spinOverlap_abs_le x.1 y.1)⟩,
    ⟨((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ),by
      constructor
      · positivity
      · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
        exact_mod_cast (indexedCommonDepth k y.2 x.2).isLt.le⟩)

lemma sourceJointOverlap_measurable (N k : ℕ) :
    Measurable (Function.uncurry (sourceJointOverlap (N:=N) (k:=k))) := by
  apply Measurable.prodMk
  · apply Measurable.subtype_mk
    exact (measurable_fst.fst.subtype_val.inner measurable_snd.fst.subtype_val)
  · apply Measurable.subtype_mk
    have hm : Measurable (fun a : IndexedLeaf k × IndexedLeaf k =>
      ((indexedCommonDepth k a.2 a.1).val:ℝ)/(k+1:ℕ)) := measurable_of_countable _
    exact hm.comp (measurable_fst.snd.prodMk measurable_snd.snd)

def sourceJointArray {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) : CompactArray CompactJointOverlap :=
  fun i j => sourceJointOverlap (x i) (x j)

lemma sourceJointArray_measurable (N k : ℕ) : Measurable (sourceJointArray (N:=N) (k:=k)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (sourceJointOverlap_measurable N k).comp (show Measurable (fun x : ℕ → NormalizedSpin N×IndexedLeaf k => (x i,x j)) from by fun_prop)

def sourceGibbsArrayLaw (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) :
    ProbabilityMeasure (CompactArray CompactJointOverlap) :=
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let H := sourceCouplingHamiltonian n k f p d h u
  let μ := annealedInfiniteReplicaMeasure (sourceFullSpinLeafKernel n k) P H
    (sourceCouplingHamiltonian_measurable n k f p d h u)
  ⟨μ.map (fun a => sourceJointArray a.2),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact ((sourceJointArray_measurable (n+1) k).comp measurable_snd).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldWord
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def sphericalHeatValue (n : ℕ) (l : List (ℝ×ℝ)) : ℝ :=
  gaussianBackward (stdGaussian (Spin (n+1))) l
    (logSphericalExp n (Real.sqrt (n+1:ℕ))) 0/(n+1:ℕ)-(l.map fun c => c.2^2).sum/2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformGrid
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def sphericalGridValue (n k : ℕ) (v : Fin (k+2) → ℝ) : ℝ :=
  sphericalHeatValue n (List.ofFn fun i => (uniformExponents k i,Real.sqrt (v i)))

def sphericalGridDual (k : ℕ) (v : Fin (k+2) → ℝ) : ℝ :=
  sInf (finiteSphericalDualValues (uniformWeights k) (varianceLevels (fun i => v i.castSucc))
    (fun i => (uniformWeights_pos k i).le) (uniformWeights_sum k))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldRounding
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy


def quantileTrial (q : Time → Time) : Trial where
  toFun := fun t => timeLaw.real {u | q u ≤ t}
  monotone := by
    intro s t hst
    exact measureReal_mono (fun u hu => hu.trans hst)
  measurable := by
    apply Monotone.measurable
    intro s t hst
    exact measureReal_mono (fun u hu => hu.trans hst)
  nonneg := fun _ => measureReal_nonneg
  le_one := by
    intro t
    simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedTrialLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def weightedTrialLaw {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time) : Measure Time :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (q i)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedVisit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

section

def oneDecoratedVisit {X : Type} (h : X → ℝ≥0∞) : (n : ℕ) → DecoratedVisitShape X n
  | 0 => (1,h)
  | n+1 => [oneDecoratedVisit h n]

end

def twoDecoratedVisit {X : Type} (h k : X → ℝ≥0∞) : (n : ℕ) → Fin (n+1) → DecoratedVisitShape X n
  | 0,_ => (2,fun x => h x*k x)
  | n+1,d => Fin.cases [oneDecoratedVisit h n,oneDecoratedVisit k n]
      (fun i => [twoDecoratedVisit h k n i]) d

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AtomicPairVisitLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def twoVisitMass (n : ℕ) (z : Fin n → ℝ) (d : Fin (n+1)) : ℝ≥0∞ :=
  cascadeShapeLikelihood n z 0 ((twoDecoratedVisit (X := Unit) (fun _ => 1) (fun _ => 1) n d).bare n)

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_UnitSphereTangent
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSpinHAddNatOfNatSphereLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def unitSphereAmbientLaw (N : ℕ) : Measure (Spin N) :=
  (unitSphereLaw N).map (fun x : NormalizedSpin N => x.val)

instance unitSphereAmbientLaw_probability (n : ℕ) : IsProbabilityMeasure (unitSphereAmbientLaw (n+1)) := by
  unfold unitSphereAmbientLaw
  apply (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2
  have : NeZero ((volume : Measure (Spin (n+1))).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegratedConvex
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

variable {I : Type} [Fintype I]

def vectorGaussianRow {S : Type*} (V : S→EuclideanSpace ℝ I) (i : ℕ) (x : S) : ℝ :=
  finiteGaussianRow countableCoordinate (fun j => V x j) i

def vectorGaussianLength (I : Type) [Fintype I] : ℕ :=
  finiteGaussianRowLength (countableCoordinate (ι:=I))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkAnnealedTangent
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ContDiff

def tangentDerivTest (N : ℕ) (G : ℝ→ᵇℝ) (x : Fin 2→NormalizedSpin N) : ℝ :=
  deriv (G : ℝ→ℝ) (spinOverlap (x 0) (x 1))*(1-spinOverlap (x 0) (x 1)^2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovarianceLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {V I : Type} [Countable V] [Fintype I] [DecidableEq I]

variable {S : Type} [MeasurableSpace S]
variable (n : ℕ)

def sharedMarksHamiltonian (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (g : SharedVertex n→EuclideanSpace ℝ I) (x : S×IndexedLeaf n) : ℝ :=
  W x + ∑ l : Fin (n+1), ∑ i : I, g (indexedLeafSharedVertex n x.2 l) i * V x.1 i

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_PerturbationContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceExpectedPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (u : Fin (n+1) → ℝ) : ℝ :=
  ∫ a, sourceKernelPressure n k f p d u h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldContinuity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceFieldCoefficients {N k : ℕ} (p d : Fin N→ℕ) (h : Fin (k+1)→ℝ) :
    Fin (k+1)→EnrichedIndex N N p→ℝ :=
  hierarchyRowCoefficients k (profileGaussianRoot (enrichedCoordinateLevel p d h))
    (profileGaussianStep (enrichedCoordinateLevel p d h))

def sourceFieldDistance {N k : ℕ} (p d : Fin N→ℕ) (u : Fin N→ℝ)
    (h' h : Fin (k+1)→ℝ) : ℝ :=
  let D := indexedCoefficientSquare k (sourceFieldCoefficients p d h)*(enrichedFeatureBound N u:ℝ)^2
  let E := indexedCoefficientSquare k (fun l i => sourceFieldCoefficients p d h' l i-
    sourceFieldCoefficients p d h l i)*(enrichedFeatureBound N u:ℝ)^2
  (1/(N:ℝ))*(2*(Real.sqrt (2*D+2*E)*Real.sqrt E))+|h' (Fin.last k)-h (Fin.last k)|

def sourceDirectionProfile {N k : ℕ} (p : Fin N→ℕ) (a : Fin (k+1)→ℝ)
    (l : Fin (k+1)) : EnrichedIndex N N p→ℝ :=
  Sum.elim (fun _ => 2*a l) (fun _ => 0)

def sourceDirectionCoefficients {N k : ℕ} (p : Fin N→ℕ) (a : Fin (k+1)→ℝ) :
    Fin (k+1)→EnrichedIndex N N p→ℝ :=
  hierarchyRowCoefficients k (profileGaussianRoot (sourceDirectionProfile p a))
    (profileGaussianStep (sourceDirectionProfile p a))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


def sourceFieldObservable {N k : ℕ} (a : Fin (k+1)→ℝ)
    (x : Fin 2→NormalizedSpin N×IndexedLeaf k) : ℝ :=
  a (indexedCommonDepth k (x 0).2 (x 1).2)*spinOverlap (x 1).1 (x 0).1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DensityDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceCountExpectedLog (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ) (M : ℕ) : ℝ :=
  ∫ a, enrichedPoissonLog n k f p d u h (M,a) ∂enrichedRowsDisorderLaw n k p z

def sourceDensityIncrement (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ) (t : ℝ≥0) : ℝ :=
  ∫ M, sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M
    ∂poissonMeasure ((n+1:ℕ)*t)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_PureLabel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def pureLabelIndex {N : ℕ} (p : Fin N→ℕ) (j : Fin N) (hp : p j=0) : EnrichedIndex N N p :=
  Sum.inr ⟨j,fun l => Fin.elim0 (Fin.cast hp l)⟩

def pureLabelResponse {N : ℕ} (p d : Fin N→ℕ) (j : Fin N) (hp : p j=0)
    (k : ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) : ℝ :=
  ((diagonalCascadeWord (enrichedIncrementFactors p d h) k z).map
    (fun a => a.1*(a.2 (pureLabelIndex p j hp))^2)).sum

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_SynchronizedLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceLabelLaw (k : ℕ) (w : Fin (k+1)→ℝ) : Measure unitInterval :=
  ∑ l, ENNReal.ofReal (w l) • Measure.dirac (sourceLabelLevel k l)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshReplicaKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

def sourceFreshMoment (n k : ℕ) (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) : ℝ :=
  ∫ a, ∫ g, (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => ψ (inner ℝ x.1.val g)) 1)^r ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)))
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlledPrefix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def patchControl (v : Time → BrownianPath → ℝ) (s t : Time) (a : BrownianPath → ℝ) :
    Time → BrownianPath → ℝ := fun r ω => if r ∈ Set.Ioc s t then a ω else v r ω

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

def timeMesh (a b : Time) (n k : ℕ) : Time :=
  Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one ((k : ℝ)/(n+1)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def paddedControlNodes {n : ℕ} (q : Fin (n+1)→Time) : Fin (n+3)→Time :=
  Fin.cons 0 (Fin.snoc q 1)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceFreshPartitionLaw (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    ProbabilityMeasure (FreshPartitionRange f) :=
  freshThermalLaw (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u)
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    (fun x => x.1.val) (measurable_subtype_coe.comp measurable_fst) f

def sourceFreshLog (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) : ℝ :=
  ∫ a, ∫ g, Real.log (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => Real.exp (f (inner ℝ x.1.val g))) 1)
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)))
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceLabelFreshMoment (n k : ℕ) (q : Fin (k+1)→ℝ) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) : ℝ :=
  ∫ a, ∫ g, (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ ψ
      (labelProfileField q g x)) 1)^r ∂countableGaussianLaw
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceLabelPartitionLaw (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) : ProbabilityMeasure (FreshPartitionRange ψ) :=
  boundedThermalLaw (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) countableGaussianLaw
    (sourceCouplingHamiltonian n k f p d h u)
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    (labelLogResponse q hq1 ψ) (labelLogResponse_measurable q hq1 ψ) ψ

def sourceLabelFreshLog (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) : ℝ :=
  ∫ a, ∫ g, Real.log (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ (expBCF 1 ψ)
      (labelProfileField q g x)) 1) ∂countableGaussianLaw
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceFreshReferenceLog (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (A : ℕ→EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (R : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (F : EuclideanSpace ℝ (Fin 1)→ℝ) (v : SourceFreshReferenceData n k p) : ℝ :=
  Real.log (tiltMean (indexedLeafProbability k v.2.1)
    (fun l => enrichedTerminal n M f a p u (h (Fin.last k))
      (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
        ((fun _ => enrichedRootMap p d h v.1.2),v.2.2.2) l 0))
    (fun l => Real.exp (F (indexedLeafState (gaussianLinearMarkStep A) k
      ((fun _ => R v.1.1),v.2.2.1) l 0))) 1)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceLabelReassoc (n k : ℕ) :
    ((SourceBaseData n k × (ℕ→ℝ)) × (ℕ→ℝ)) ≃ᵐ SourceLabelData n k :=
  (MeasurableEquiv.prodAssoc).trans
    (((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodComm)).trans
      ((MeasurableEquiv.prodAssoc).trans
        ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodAssoc))))

def sourceLabelLogIntegrand (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (a : (SourceBaseData n k × (ℕ→ℝ)) × (ℕ→ℝ)) : ℝ :=
  Real.log (boundedThermalPartition (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p d h u) (labelLogResponse q hq1 ψ) a)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControlTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def uniformControlNodes (n : ℕ) (i : Fin (n+1)) : Time :=
  ⟨(i:ℝ)/(n+1),div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity : (0:ℝ)<n+1)).mpr (by exact_mod_cast i.isLt.le)⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileUpperTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def uniformQuantileLower (n : ℕ) (q : Time→Time) (i : Fin (n+1)) : Time :=
  q (uniformQuantileGrid n i.castSucc)
def uniformQuantileUpper (n : ℕ) (q : Time→Time) (i : Fin (n+1)) : Time :=
  q (uniformQuantileGrid n i.succ)
def sampleQuantileLower (n : ℕ) (q : Time→Time) (u : Time) : Time :=
  uniformQuantileLower n q (uniformQuantileCell n u)
def sampleQuantileUpper (n : ℕ) (q : Time→Time) (u : Time) : Time :=
  uniformQuantileUpper n q (uniformQuantileCell n u)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def timeSpin (x : Time) : CompactOverlap := ⟨x.val,by linarith [x.prop.1],x.prop.2⟩
lemma timeSpin_continuous : Continuous timeSpin := by unfold timeSpin; fun_prop

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def quantileSpinLaw (q : Time→Time) (hq : Measurable q) : ProbabilityMeasure CompactOverlap :=
  ⟨timeLaw.map (fun u=>timeSpin (q u)),(Measure.isProbabilityMeasure_map_iff
    (timeSpin_continuous.measurable.comp hq).aemeasurable).2 inferInstance⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A : Type*} {S : Type} [MeasurableSpace A] [MeasurableSpace S] {k r : ℕ}

variable (κ : Kernel A (S×IndexedLeaf k)) [IsMarkovKernel κ]
variable (H : A → S×IndexedLeaf k → ℝ)
variable (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
variable (v w : Fin r → ℝ →ᵇ ℝ) (F : (Fin r → S×IndexedLeaf k) → ℝ)

def restorationReciprocal (f : ℝ →ᵇ ℝ) (r : ℕ) : C(RestorationRange f,ℝ) :=
  ⟨fun x => (x.val^r)⁻¹, (continuous_subtype_val.pow r).inv₀
    (fun x => (pow_pos ((Real.exp_pos _).trans_le x.prop.1) r).ne')⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments2
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

def sourceLabelRestorationMoment (n k r : ℕ) (q : Fin (k+1) → ℝ) (s : ℝ≥0)
    (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (j : ℕ) : ℝ :=
  ∫ a, ∫ b, (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a) (labelRestorationWeight q s ψ b) 1)^j *
    gibbsReplicaMean (sourceFullSpinLeafKernel n k a) (sourceCouplingHamiltonian n k f p d h u a) r
      (labelRestorationTest q s ψ v w (fun x => F (fun i l => sourceJointOverlap (x i) (x l))) b)
    ∂countableGaussianLaw.prod countableGaussianLaw ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

variable (n k r : ℕ) (q : Fin (k+1) → ℝ) (s : ℝ≥0)
variable (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
variable (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ)
variable (z : Fin k → ℝ) (t : ℝ≥0)

def sourceLabelRestorationNumerator :=
  labelKernelNumerator (sourceFullSpinLeafKernel n k) (sourceCouplingHamiltonian n k f p d h u)
    q s ψ v w (fun x => F (fun i l => sourceJointOverlap (x i) (x l)))
def sourceLabelRestorationDenominator :=
  labelKernelCompactDenominator (sourceFullSpinLeafKernel n k) (sourceCouplingHamiltonian n k f p d h u) q s ψ

def sourceLabelRestorationRatio : ℝ :=
  ∫ a, sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u a *
    restorationReciprocal ψ r (sourceLabelRestorationDenominator n k q s f ψ p d h u a)
    ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_CountableTerminalRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable (I J K : Type) [Fintype I] [Fintype J] [Fintype K]

variable {I J K}
def tripleGaussianStep
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) :
    TripleGaussianState I J K×TripleGaussianMark I J K→TripleGaussianState I J K :=
  fun p => ((gaussianLinearMarkStep A (p.1.1.1,p.2.1.1),
    gaussianLinearMarkStep B (p.1.1.2,p.2.1.2)),gaussianLinearMarkStep C (p.1.2,p.2.2))

def tripleGaussianTerminal
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ) :
    TripleGaussianState I J K→ℝ := fun x => (H (x.1.1 0)+G (x.1.2 0))+F (x.2 0)

def tripleGaussianObservable (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ) :
    TripleGaussianState I J K→ℝ := fun x => f (x.1.1 0)*g (x.1.2 0)

def tripleGaussianRoot
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) :
    TripleGaussianMark I J K→TripleGaussianState I J K :=
  fun p => ((fun _ => R p.1.1,fun _ => Q p.1.2),fun _ => T p.2)

def tripleGaussianPair (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (p : TripleGaussianData I J K k) : ℝ :=
  indexedTerminalPairMean (tripleGaussianStep A B C) k (tripleGaussianTerminal H G F)
    (tripleGaussianRoot R Q T p.1) d (tripleGaussianObservable f g)
    (p.2.1,indexedMarksZip k p.2.2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TripleGaussianReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def tripleGaussianCountableData (k : ℕ) (b : IndexedCascadeBase k)
    (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)) : TripleGaussianData I J K k :=
  ((((indexedGaussianDisorder k I t.1.1).1,(indexedGaussianDisorder k J t.1.2).1),
    (indexedGaussianDisorder k K t.2).1),
    (b,(indexedMarksZip k ((indexedGaussianDisorder k I t.1.1).2,
      (indexedGaussianDisorder k J t.1.2).2),(indexedGaussianDisorder k K t.2).2)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationPair
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {S K : Type} [MeasurableSpace S] [Fintype K]

def sourceLabelPairRatio (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ)
    (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))) : ℝ :=
  gibbsReplicaMean (enrichedIndexedBaseMeasure n k t.1)
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) 2
    (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
      (fun xs => if indexedCommonDepth k (xs 0).2 (xs 1).2=d then 1 else 0) t.2.1) /
    (tiltMean (enrichedIndexedBaseMeasure n k t.1)
      (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) (labelRestorationWeight q s g.f t.2.1) 1)^2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestoredValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceLabelPairReassoc (n k : ℕ) :
    ((SourceBaseData n k×(ℕ→ℝ))×((ℕ→ℝ)×(ℕ→ℝ))) ≃ᵐ SourceLabelPairData n k :=
  (MeasurableEquiv.prodAssoc).trans
    (((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodComm)).trans
      ((MeasurableEquiv.prodAssoc).trans
        ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.prodAssoc))))

def sourceLabelPairIntegrand (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :=
  labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p e h u) q s g.f (fun _ : Fin 2 => v) (fun _ => w) (labelDepthTest k d)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def scalarPairMatrixTest (F : CompactOverlap →ᵇ ℝ) : Matrix (Fin 2) (Fin 2) ℝ →ᵇ ℝ :=
  F.compContinuous ⟨fun Q => Set.projIcc (-1) 1 (by norm_num) (Q 1 0),
    by fun_prop⟩

def scalarRestorationPairMoment (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) (j : ℕ) :
    Matrix (Fin (2+j)) (Fin (2+j)) ℝ →ᵇ ℝ :=
  scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j *
    freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 2 => v) j)) *
    freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 2 => w) j))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactRestorationWitness
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

def pairRestorationBound (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) : ℝ :=
  ‖F‖*(∏ _ : Fin 2, ‖expBCF 1 f*v‖)*(∏ _ : Fin 2, ‖expBCF 1 f*w‖)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedMarkedSelection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def roundTime (q : BoundedField 1) (n : ℕ) (u : Time) : Time :=
  ⟨q.round n u,⟨(q.round n).nonneg u,(q.round n).le_bound u⟩⟩

lemma roundTime_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundTime q n) :=
  (q.round n).monotone

def roundedPairCoeff (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    Fin ((strictRoundModel q n).depth+1)→ℝ :=
  labelPairCoefficient (strictRoundModel q n).depth (stepCumulative (strictRoundModel q n).weight)
    (strictRoundModel q n).value g
    ⟨1-roundTimeValue q n (Fin.last (strictRoundModel q n).depth),
      sub_nonneg.mpr (roundTimeValue q n _).prop.2⟩ v

def roundedPairFunction (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) (r : ℝ) : ℝ :=
  finiteMonotoneExtension (strictRoundModel q n).value (roundedPairCoeff q n g v) (roundLower n r)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

def markedTangentTriple (K : ℝ) (G : ℝ→ᵇℝ) : CompactBlock (BulkPairRange K) 3→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => G (Q 1 2).1.val*(Q 1 0).2.val*((Q 2 0).1.val-(Q 1 2).1.val*(Q 1 0).1.val),by fun_prop⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableSingleRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def tripleGaussianMean (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (p : TripleGaussianData I J K k) : ℝ :=
  indexedTerminalMean (tripleGaussianStep A B C) k (tripleGaussianTerminal H G F)
    (tripleGaussianRoot R Q T p.1) (tripleGaussianObservable f g)
    (p.2.1,indexedMarksZip k p.2.2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationSingle
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S K : Type} [MeasurableSpace S] [Fintype K]

def sourceLabelSingleRatio (n M k : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))) : ℝ :=
  gibbsReplicaMean (enrichedIndexedBaseMeasure n k t.1)
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) 1
    (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
      (fun _ => 1) t.2.1) /
    (tiltMean (enrichedIndexedBaseMeasure n k t.1)
      (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) (labelRestorationWeight q s g.f t.2.1) 1)^1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelSingleRestoredValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction Topology

def sourceLabelSingleIntegrand (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ) :=
  labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p e h u) q s g.f (fun _ : Fin 1 => v) (fun _ => w) (fun _ => 1)

def singleRestorationBound (f v w : ℝ →ᵇ ℝ) : ℝ :=
  ‖expBCF 1 f*v‖*‖expBCF 1 f*w‖

def scalarRestorationSingleMoment (f v w : ℝ →ᵇ ℝ) (j : ℕ) :
    Matrix (Fin (1+j)) (Fin (1+j)) ℝ →ᵇ ℝ :=
  freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 1 => v) j)) *
    freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 1 => w) j))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileSingleReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def roundedSingleCoeff (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) : ℝ :=
  labelSingleCoefficient (strictRoundModel q n).depth (stepCumulative (strictRoundModel q n).weight)
    (strictRoundModel q n).value g
    ⟨1-roundTimeValue q n (Fin.last (strictRoundModel q n).depth),
      sub_nonneg.mpr (roundTimeValue q n _).prop.2⟩ v

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProbabilityMaps
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction BigOperators NNReal

def quantileRoundLaw (η : Measure Time) [IsProbabilityMeasure η] (j : ℕ) : ProbabilityMeasure Time :=
  ProbabilityMeasure.map (⟨timeLaw,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Time)
    (f := roundTime (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j) (roundTime_mono _ j).measurable.aemeasurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

def roundedLevelCode (q : BoundedField 1) (n : ℕ) (r : Time) :
    Fin ((strictRoundModel q n).depth+1) :=
  orderedLevelCode (strictRoundModel q n).value (roundLower n r)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def timeGridRound (n : ℕ) (r : Time) : Time :=
  roundTime (unitQuantileField id monotone_id) n r

def timeMarkedDecode {K : Type*} (P : Time → K) (D : K) (Q : CompactArray Time) : CompactArray K :=
  fun i j => if i = j then D else P (Q i j)

lemma timeMarkedDecode_measurable {K : Type*} [MeasurableSpace K]
    {P : Time → K} (hP : Measurable P) (D : K) : Measurable (timeMarkedDecode P D) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold timeMarkedDecode
  split_ifs
  · exact measurable_const
  · exact hP.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCavityRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy



def roundedCavityValue (n d : ℕ) (g : Jet3) (P : Measure BrownianPath)
    (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) {K a : ℝ}
    (ha0 : 0≤a) (haK : a≤K) (j : ℕ) : ℝ :=
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  (n+1:ℕ)*(a/2+finiteSphericalFieldValue n M.depth M.weight
    (fun l=>(roundedCavityPair η B ha0 haK j l).2.val/2))+
    d*controlValue P g.f (weightedStepTrial M.weight (roundTimeValue F j)
      (fun l=>(M.weight_pos l).le) M.weight_sum)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityRoundedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def roundedProfileMoment (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) (j : ℕ) : ℝ :=
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  ∑ i,M.weight i*(cappedA η B (roundTimeValue F j i)/2)*(roundTimeValue F j i:ℝ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FixedCount
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceCountHamiltonian (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a : SourceCountData n k) : NormalizedSpin (n+1) × IndexedLeaf k → ℝ :=
  sourceCouplingHamiltonian n k f p d h u (sourceCountEmbedding n M k a)

def sourceCountLog (n M k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a : SourceCountData n k) : ℝ :=
  Real.log (tiltPartition (sourceCountKernel n k a) (sourceCountHamiltonian n M k f p d h u a) 1)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshDensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceDisorderUnassoc (n k : ℕ) (a : SourceIndexedDisorder n k) : SourceBaseData n k × (ℕ→ℝ) :=
  ((a.1,(a.2.1,a.2.2.1)),a.2.2.2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FieldArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceFieldArrayTest {k : ℕ} (a : Fin (k+1)→ℝ) : CompactArray CompactJointOverlap→ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => (sourceFieldPolynomial a).eval (Q 1 0).2.val*(Q 1 0).1.val,
    by fun_prop⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DensityLipschitz
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceContactDomain (n k : ℕ) : Set (SourceContactParameter n k) :=
  {a | (∀ l, 0≤a.2.1 l) ∧ Monotone a.2.1 ∧ ∀ j, a.2.2 j∈Icc 1 2}

def sourceJointPressure (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (z : Fin k→ℝ) (a : SourceContactParameter n k) : ℝ :=
  sourceExpectedPressure n k f p d a.2.1 z a.1 a.2.2

def sourceContactDistance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (a' a : SourceContactParameter n k) : ℝ :=
  ‖f‖*|(a'.1:ℝ)-(a.1:ℝ)|+sourceFieldDistance p d a'.2.2 a'.2.1 a.2.1+
    ∑ j : Fin (n+1), (4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ))*|a'.2.2 j-a.2.2 j|

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Field
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def normalizedPatternLog (n M : ℕ) (f : ℝ →ᵇ ℝ) (a : Fin M→Fin (n+1)→ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (normalizedPatternEnergy (n+1) M f a x) ∂unitSphereLaw (n+1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceContactCompactDomain (n k : ℕ) (α : ℝ≥0) (H : ℝ) : Set (SourceContactParameter n k) :=
  Icc 0 α ×ˢ (sourceStepFieldCap k H ×ˢ Icc (fun _ => 1) (fun _ => 2))

def sourceStepContactObjective (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (a : SourceContactParameter n k) : ℝ :=
  -sourceJointPressure n k f p d (stepCumulative w) a-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+
    (entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContactLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

def sourceThresholdDirection {k : ℕ} (q : Fin (k+1)→Time) (r : ℝ) : Fin (k+1)→ℝ :=
  fun i => if r≤(q i:ℝ) then 1 else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end


