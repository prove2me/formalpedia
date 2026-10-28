-- Prove2me | Definitions.Def_OAIQ61Pf000
-- name    : OAIQ61Pf000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:59:57.815769+00:00
-- url     : https://prove2.me/theorems/a00d1e9a-4780-482d-9d5e-e00de72b1948
-- title:
--   Definitions bundle OAIQ61Pf000 of the split of OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 990 declarations of OpenAI's Lean: 698 definitions, 7 inductive types or structures, 65 instances and 220 theorems. The definitions and types are `OAI.SphericalPerceptronFreeEnergy.BoundedC1`, `OAI.SphericalPerceptronFreeEnergy.BoundedField`, `OAI.SphericalPerceptronFreeEnergy.BoundedField.round`, `OAI.SphericalPerceptronFreeEnergy.BulkCavityData`, `OAI.SphericalPerceptronFreeEnergy.BulkDisorder`, `OAI.SphericalPerceptronFreeEnergy.BulkMark`, `OAI.SphericalPerceptronFreeEnergy.BulkPairRange`, `OAI.SphericalPerceptronFreeEnergy.CascadeShapeMatches`, `OAI.SphericalPerceptronFreeEnergy.CascadeShapeReplicas`, `OAI.SphericalPerceptronFreeEnergy.CascadeVisitShape`, `OAI.SphericalPerceptronFreeEnergy.CascadeVisitShape.Valid`, `OAI.SphericalPerceptronFreeEnergy.CavityBulkNoiseIndex`, `OAI.SphericalPerceptronFreeEnergy.CavityGoodParameters`, `OAI.SphericalPerceptronFreeEnergy.CavityIncrementRandom`, `OAI.SphericalPerceptronFreeEnergy.CavityPartitionRange`, `OAI.SphericalPerceptronFreeEnergy.CavityProxyRandom`, `OAI.SphericalPerceptronFreeEnergy.CavityRPCMark`, `OAI.SphericalPerceptronFreeEnergy.CavityRPCState`, `OAI.SphericalPerceptronFreeEnergy.CavityReplicaIndex`, `OAI.SphericalPerceptronFreeEnergy.CavityShellSpin`, `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactLabelGeometry`, `OAI.SphericalPerceptronFreeEnergy.CompactLabelNodes`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactSpinGeometry`, `OAI.SphericalPerceptronFreeEnergy.CovarianceMatrix`, `OAI.SphericalPerceptronFreeEnergy.DecoratedCascade`, `OAI.SphericalPerceptronFreeEnergy.DecoratedVisitShape`, `OAI.SphericalPerceptronFreeEnergy.DecoratedVisitShape.Valid`, `OAI.SphericalPerceptronFreeEnergy.DecoratedVisitShape.bare`, `OAI.SphericalPerceptronFreeEnergy.DistinctAssignmentGood`, `OAI.SphericalPerceptronFreeEnergy.EnrichedIndex`, `OAI.SphericalPerceptronFreeEnergy.EnrichedMark`, `OAI.SphericalPerceptronFreeEnergy.FiniteBlock`, `OAI.SphericalPerceptronFreeEnergy.FiniteFieldModel`, `OAI.SphericalPerceptronFreeEnergy.FiniteFieldModel.weight`, `OAI.SphericalPerceptronFreeEnergy.FiniteGG`, `OAI.SphericalPerceptronFreeEnergy.FiniteOverlap` and 665 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Perceptron_Brownian_CavityGaussianFields`, `Perceptron_Brownian_CountableGaussianField`, `Perceptron_Brownian_GaussianField`, `Perceptron_Brownian_GaussianFieldAlgebra`, `Perceptron_Cascade_CascadeHeat`, `Perceptron_Cascade_CavityCappedRPC`, `Perceptron_Cascade_CavityFiniteRPC`, `Perceptron_Cascade_DecoratedWeightedTotal`, `Perceptron_Cascade_EnrichedPoissonVariance`, `Perceptron_Cascade_IndexedCascadeRegular`, `Perceptron_Cascade_IndexedMarkedPoisson`, `Perceptron_Cascade_IndexedPoisson`, `Perceptron_Cascade_IndexedTiltedLeaves`, `Perceptron_Cascade_IndexedTiltedWeights`, `Perceptron_Cascade_IndexedVertices`, `Perceptron_Cascade_PoissonLaplace`, `Perceptron_Cascade_StableCascade`, `Perceptron_Cascade_TwoVisitWeights`, `Perceptron_Cascade_WeightedCDF`, `Perceptron_Cascade_WeightedTotalBiasedLaw`, `Perceptron_Cavity_AmbientBulkFeature`, `Perceptron_Cavity_BulkAnnealedTangent`, `Perceptron_Cavity_BulkCavityData`, `Perceptron_Cavity_BulkCavityRecursion`, `Perceptron_Cavity_BulkCompactGG`, `Perceptron_Cavity_BulkConcentration`, `Perceptron_Cavity_BulkCoupling`, `Perceptron_Cavity_BulkDeviation`, `Perceptron_Cavity_BulkEnergyDeviation`, `Perceptron_Cavity_BulkFreshRestore`, `Perceptron_Cavity_BulkGoodParameters`, `Perceptron_Cavity_BulkLimitGeometry`, `Perceptron_Cavity_BulkMarkedArray`, `Perceptron_Cavity_BulkMarkedMoments`, `Perceptron_Cavity_BulkMarkedPairLimit`, `Perceptron_Cavity_BulkModel`, `Perceptron_Cavity_BulkPairLaw`, `Perceptron_Cavity_BulkParameterDeviation`, `Perceptron_Cavity_BulkRadialIBP`, `Perceptron_Cavity_BulkRadialIdentity`, `Perceptron_Cavity_BulkRadialLimit`, `Perceptron_Cavity_BulkReplicaDominated`, `Perceptron_Cavity_BulkReplicaStein`, `Perceptron_Cavity_BulkRestorationLimit`, `Perceptron_Cavity_BulkRestoredObservables`, `Perceptron_Cavity_BulkSingleEmpiricalLimit`, `Perceptron_Cavity_BulkSingleLimit`, `Perceptron_Cavity_BulkTangentError`, `Perceptron_Cavity_BulkThermal`, `Perceptron_Cavity_CavityAnnealedUncap`, `Perceptron_Cavity_CavityBlockProduct`, `Perceptron_Cavity_CavityBulkCoefficients`, `Perceptron_Cavity_CavityBulkLog`, `Perceptron_Cavity_CavityBulkUncappedLog`, `Perceptron_Cavity_CavityCompensator`, `Perceptron_Cavity_CavityConditionalIncrement`, `Perceptron_Cavity_CavityCountableIsotropic`, `Perceptron_Cavity_CavityCounts`, `Perceptron_Cavity_CavityCovarianceComparison`, `Perceptron_Cavity_CavityDiagonalKernel`, `Perceptron_Cavity_CavityDisintegration`, `Perceptron_Cavity_CavityExpectedCompensator`, `Perceptron_Cavity_CavityFiniteIncrement`, `Perceptron_Cavity_CavityFreshReplacement`, `Perceptron_Cavity_CavityGaussianQuadratic`, `Perceptron_Cavity_CavityGaussianReplica`, `Perceptron_Cavity_CavityGaussianTransport`, `Perceptron_Cavity_CavityGeometry`, `Perceptron_Cavity_CavityGoodFreshLower`, `Perceptron_Cavity_CavityIncrementLaw`, `Perceptron_Cavity_CavityLabelAnnealed`, `Perceptron_Cavity_CavityLabelArray`, `Perceptron_Cavity_CavityLabelMoment`, `Perceptron_Cavity_CavityLabelPartition`, `Perceptron_Cavity_CavityMeanCap`, `Perceptron_Cavity_CavityNormalizedIncrement`, `Perceptron_Cavity_CavityOldExpectation`, `Perceptron_Cavity_CavityPerturbationCovariance`, `Perceptron_Cavity_CavityProductLaw`, `Perceptron_Cavity_CavityResidualFormula`, `Perceptron_Cavity_CavityResidualUncap`, `Perceptron_Cavity_CavityRoundedLower`, `Perceptron_Cavity_CavityShellExpansion`, `Perceptron_Cavity_CavityShellLimit`, `Perceptron_Cavity_CavityShellPerturbation`, `Perceptron_Cavity_CavityShellPolar`, `Perceptron_Cavity_CavitySphericalMoments`, `Perceptron_Cavity_CavityTaylorFinite`, `Perceptron_Cavity_CavityUniformRemainder`, `Perceptron_Cavity_ContinuousCavityProfile`, `Perceptron_Cavity_CountableFreshMoment`, `Perceptron_Cavity_FreshDiagonalNoise`, `Perceptron_Cavity_FreshGGUniqueness`, `Perceptron_Cavity_FreshMarkedKernel`, `Perceptron_Cavity_FreshReference`, `Perceptron_Cavity_FreshReplicaKernel`, `Perceptron_Cavity_FreshThermalLaw`, `Perceptron_Cavity_LabelFreshKernel`, `Perceptron_Cavity_LabelFreshLog`, `Perceptron_Control_ControlDrift`, `Perceptron_Control_ControlledPrefix`, `Perceptron_Control_FreshControl`, `Perceptron_Control_QuantileControlContinuity`, `Perceptron_Control_StepControl`, `Perceptron_Control_StepControlTail`, `Perceptron_Interpolation_ArrayGeometry`, `Perceptron_Interpolation_CompactArrayMap`, `Perceptron_Interpolation_FiniteOverlap`, `Perceptron_Interpolation_GibbsOverlapArray`, `Perceptron_Interpolation_GibbsReplicaMean`, `Perceptron_Interpolation_KernelInfiniteReplica`, `Perceptron_Interpolation_KernelReplicaGibbs`, `Perceptron_Interpolation_OverlapArray`, `Perceptron_Interpolation_OverlapBlock`, `Perceptron_Interpolation_RestorationReplicaBlocks`, `Perceptron_Interpolation_TripleGaussianReplica`, `Perceptron_Pressure_CountableTerminalRestoration`, `Perceptron_Pressure_EnrichedPatternMean`, `Perceptron_Pressure_EnrichedPatternVariance`, `Perceptron_Pressure_FiniteTerminal`, `Perceptron_Pressure_IndexedTerminalProduct`, `Perceptron_Pressure_PatternFree`, `Perceptron_Pressure_PatternMatrices`, `Perceptron_Pressure_RootPartition`, `Perceptron_Pressure_TerminalRestorationCoefficients`, `Perceptron_Pressure_TerminalVariational`, `Perceptron_Pressure_VectorPartition`, `Perceptron_Sphere_GaussianAffineCoordinate`, `Perceptron_Sphere_GaussianCoordinateProjection`, `Perceptron_Sphere_GaussianPolar`, `Perceptron_Sphere_GaussianRotation`, `Perceptron_Sphere_SphereBridge`, `Perceptron_Sphere_SphereHeat`, `Perceptron_Sphere_SphereIsometryMap`, `Perceptron_Sphere_SphereKernel`, `Perceptron_Sphere_SphereLimit`, `Perceptron_Variational_AmplitudeConvex`, `Perceptron_Variational_AtomicBranches`, `Perceptron_Variational_AtomicPairVisitLaw`, `Perceptron_Variational_BackwardScore`, `Perceptron_Variational_BcfEvalRingHom`, `Perceptron_Variational_BlockFocus`, `Perceptron_Variational_BoundedC1`, `Perceptron_Variational_CappedAContinuity`, `Perceptron_Variational_CompactEnvelope`, `Perceptron_Variational_CompactGGDensity`, `Perceptron_Variational_CompactGGEvents`, `Perceptron_Variational_CompactGGFiniteCode`, `Perceptron_Variational_CompactJointMonomials`, `Perceptron_Variational_CompactRestorationWitness`, `Perceptron_Variational_CompactScalarGG`, `Perceptron_Variational_Contact`, `Perceptron_Variational_ContactGGRate`, `Perceptron_Variational_ConvexUniform`, `Perceptron_Variational_CountableMarkedDiagonal`, `Perceptron_Variational_CouplingKernel`, `Perceptron_Variational_CovarianceMatrix`, `Perceptron_Variational_DecoratedFocus`, `Perceptron_Variational_DecoratedShapeLaw`, `Perceptron_Variational_DecoratedTiltTotal`, `Perceptron_Variational_DensityLipschitz`, `Perceptron_Variational_DepthLaw`, `Perceptron_Variational_DiagonalDeviation`, `Perceptron_Variational_DilationExpansion`, `Perceptron_Variational_EnrichedMoments`, `Perceptron_Variational_EnrichedUniformBounds`, `Perceptron_Variational_EnrichedVarianceBound`, `Perceptron_Variational_EntropicHeat`, `Perceptron_Variational_EntropicParameter`, `Perceptron_Variational_FieldRounding`, `Perceptron_Variational_FieldWord`, `Perceptron_Variational_FiniteFieldModel`, `Perceptron_Variational_FiniteGaussianRow`, `Perceptron_Variational_FixedCount`, `Perceptron_Variational_FocusedSampleLaw`, `Perceptron_Variational_FocusedShapeProbability`, `Perceptron_Variational_GaussianAverage`, `Perceptron_Variational_GaussianBackward`, `Perceptron_Variational_GaussianBlock`, `Perceptron_Variational_GaussianBoltzmann`, `Perceptron_Variational_GaussianComparison`, `Perceptron_Variational_GaussianCoupling`, `Perceptron_Variational_GaussianCovarianceDerivative`, `Perceptron_Variational_GaussianMarkRecursion`, `Perceptron_Variational_GibbsRestoration`, `Perceptron_Variational_HeatGrid`, `Perceptron_Variational_HeatLogBCF`, `Perceptron_Variational_HeatTilt`, `Perceptron_Variational_IndexedAncestry`, `Perceptron_Variational_IndexedDiagonalField`, `Perceptron_Variational_IndexedFractionalLog`, `Perceptron_Variational_IndexedGaussianCovarianceLaw`, `Perceptron_Variational_IndexedGaussianMarks`, `Perceptron_Variational_IndexedLeafTotal`, `Perceptron_Variational_IndexedMarkProduct`, `Perceptron_Variational_IndexedObservableTransport`, `Perceptron_Variational_IndexedVisit`, `Perceptron_Variational_IntegrableGibbs`, `Perceptron_Variational_IntegratedConvex`, `Perceptron_Variational_LabelPairTestValue`, `Perceptron_Variational_LabelProfileReference`, `Perceptron_Variational_LabelProfileReferenceFull`, `Perceptron_Variational_LabelReference`, `Perceptron_Variational_LabelReferenceValue`, `Perceptron_Variational_LabelRestorationKernel`, `Perceptron_Variational_LabelRestorationMoments`, `Perceptron_Variational_LabelRestorationMoments2`, `Perceptron_Variational_LabelRestorationPair`, `Perceptron_Variational_LabelRestoredValue`, `Perceptron_Variational_LabelThermalLaw`, `Perceptron_Variational_LabelValue`, `Perceptron_Variational_LevelTrialApprox`, `Perceptron_Variational_LocalMaxSecondDerivNonpos`, `Perceptron_Variational_MarkedBlockParameter`, `Perceptron_Variational_MarkedGraphLaw`, `Perceptron_Variational_MarkedTangentCanonical`, `Perceptron_Variational_MarkedTotalBiasedLaw`, `Perceptron_Variational_NormSquareBand`, `Perceptron_Variational_OrderedCode`, `Perceptron_Variational_ParameterResampling`, `Perceptron_Variational_PiMarkLaw`, `Perceptron_Variational_ProductMarkLaw`, `Perceptron_Variational_PureLabel`, `Perceptron_Variational_QuantileLimit`, `Perceptron_Variational_QuantileUpperTail`, `Perceptron_Variational_QuantitativeGG`, `Perceptron_Variational_RoundedLaw`, `Perceptron_Variational_RoundedMarkedSelection`, `Perceptron_Variational_RoundedPairCoefficients`, `Perceptron_Variational_Shape`, `Perceptron_Variational_ShapeProbability`, `Perceptron_Variational_ShapeSampleLaw`, `Perceptron_Variational_ShellBridge`, `Perceptron_Variational_StableLaplaceConstant`, `Perceptron_Variational_StableLogIntensity`, `Perceptron_Variational_StableMassKernel`, `Perceptron_Variational_StableTotalBiasedLaw`, `Perceptron_Variational_StationaryExistence`, `Perceptron_Variational_StepDual`, `Perceptron_Variational_StepEntropy`, `Perceptron_Variational_SynchronizedLimit`, `Perceptron_Variational_TensorFeatures`, `Perceptron_Variational_TiltedPathDiagonal`, `Perceptron_Variational_TiltedVisitKernel`, `Perceptron_Variational_TiltedVisitKernelLaw`, `Perceptron_Variational_Trial`, `Perceptron_Variational_TripleIndex`, `Perceptron_Variational_UnboundedContact`, `Perceptron_Variational_UniformQuantileCells`.
--
--   **Imports.** It imports the published bundle `Def_PerceptronFreeEnergy`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ61Pf002`; the statements `OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto`, `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data`, `OAI.SphericalPerceptronFreeEnergy.bulk_limit_geometry`, `OAI.SphericalPerceptronFreeEnergy.bulk_limit_gg`, `OAI.SphericalPerceptronFreeEnergy.bulk_marked_self_consistency`, `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists`, `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_evaluation`, `OAI.SphericalPerceptronFreeEnergy.cavityLabel_full_value`, `OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit`, `OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error`, `OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower`, `OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform`, `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_finiteGG`, `OAI.SphericalPerceptronFreeEnergy.indexedDepthLaw_pair_weights`, `OAI.SphericalPerceptronFreeEnergy.indexedSampleFocused_integral`, `OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old` and `OAI.SphericalPerceptronFreeEnergy.omittedBulkDeviation_integral_tendsto`; the proofs of `OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower` and `OAI.SphericalPerceptronFreeEnergy.omittedBulkDeviation_integral_tendsto`.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_PerceptronFreeEnergy

section
-- module Solutions.OAIQ061_PF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FiniteOverlap
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

abbrev FiniteOverlap (L : Type*) := ℕ → ℕ → L
abbrev FiniteBlock (L : Type*) (n : ℕ) := Fin n → Fin n → L

def finiteBlock {L : Type*} (n : ℕ) (R : FiniteOverlap L) : FiniteBlock L n :=
  fun i j => R i j

def finiteRow {L : Type*} (n : ℕ) (R : FiniteOverlap L) : Fin n → L :=
  fun i => R i n

def FiniteGG {L : Type*} [MeasurableSpace L] (μ : Measure (FiniteOverlap L)) : Prop :=
  ∀ n, 1 ≤ n → ∀ (i : Fin n) (A : FiniteBlock L n) (c : L),
    μ.real {R | finiteBlock n R = A ∧ R i n = c} =
      μ.real {R | finiteBlock n R = A} * μ.real {R | R 0 1 = c} / n +
      (∑ j ∈ Finset.univ.erase i, μ.real {R | finiteBlock n R = A ∧ R i j = c}) / n

def finiteFiberRow {L : Type*} [MeasurableSpace L]
    (μ : Measure (FiniteOverlap L)) (n : ℕ) (A : FiniteBlock L n) : Measure (Fin n → L) :=
  (μ.restrict {R | finiteBlock n R = A}).map (finiteRow n)

def finiteExtension {L : Type*} (d : L) {n : ℕ}
    (p : FiniteBlock L n × (Fin n → L)) : FiniteBlock L (n+1) :=
  fun i j => Fin.lastCases (Fin.lastCases d p.2 j)
    (fun ii => Fin.lastCases (p.2 ii) (p.1 ii) j) i

def finitePointMeasure {S : Type*} [MeasurableSpace S] (n : ℕ) (x : Fin n → S) : Measure S :=
  ∑ i : Fin n, Measure.dirac (x i)

@[fun_prop] lemma finitePointMeasure_measurable {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (finitePointMeasure (S := S) n) := by
  unfold finitePointMeasure
  fun_prop

def finitePoissonLaw {S : Type*} [MeasurableSpace S] (r : ℝ≥0) (ν : Measure S) :
    Measure (Measure S) :=
  Measure.sum fun n : ℕ =>
    poissonMeasure r {n} • (Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)

instance finitePoissonLaw_probability {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finitePoissonLaw r ν) := by
  constructor
  rw [finitePoissonLaw,Measure.sum_apply _ MeasurableSet.univ]
  have hmass (n : ℕ) : ((Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) univ = 1 := by
    rw [Measure.map_apply (finitePointMeasure_measurable n) MeasurableSet.univ,
      preimage_univ,measure_univ]
  simp only [Measure.smul_apply,hmass,smul_eq_mul,mul_one]
  have hh := hasSum_one_poissonMeasure r
  simp_rw [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hh.summable,hh.tsum_eq]
  norm_num

def expNegENNReal (u : ℝ≥0∞) : ℝ := (EReal.exp (-(u : EReal))).toReal

lemma expNegENNReal_continuous : Continuous expNegENNReal := by
  have hc : Continuous (fun u : ℝ≥0∞ => EReal.exp (-(u : EReal))) := ENNReal.continuous_exp.comp continuous_coe_ennreal_ereal.neg
  rw [continuous_iff_continuousAt]
  intro u
  apply (ENNReal.continuousAt_toReal ?_).comp hc.continuousAt
  apply ne_of_lt
  exact lt_of_le_of_lt (EReal.exp_le_one_iff.mpr
    (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg u))) ENNReal.one_lt_top

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_PoissonLaplace
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

@[simp] lemma expNegENNReal_top : expNegENNReal ⊤ = 0 := by simp [expNegENNReal]

@[simp] lemma expNegENNReal_zero : expNegENNReal 0 = 1 := by simp [expNegENNReal]

def countablePoissonLaw {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) : Measure (Measure S) :=
  (Measure.infinitePi fun i => finitePoissonLaw (r i) (ν i)).map Measure.sum

instance countablePoissonLaw_probability {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (countablePoissonLaw r ν) := by
  unfold countablePoissonLaw
  have hm : Measurable (Measure.sum : (ℕ → Measure S) → Measure S) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sum_apply _ hs]
    exact Measurable.ennreal_tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact hm.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def laplaceTest {ι : Type*} [Fintype ι] (a : ι → ℝ≥0) : (ι → ℝ≥0∞) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => expNegENNReal (∑ i, (a i : ℝ≥0∞) * x i), by
      apply expNegENNReal_continuous.comp
      exact continuous_finsetSum _ fun i _ =>
        (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (continuous_apply i)⟩

@[simp] lemma laplaceTest_zero {ι : Type*} [Fintype ι] :
    laplaceTest (0 : ι → ℝ≥0) = 1 := by
  ext x
  simp [laplaceTest]

def countablePoissonIntensity {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) : Measure S :=
  Measure.sum fun i => (r i : ℝ≥0∞) • ν i

def finiteIntensityMarks {S : Type*} [MeasurableSpace S] [Nonempty S] (κ : Measure S) : Measure S :=
  if κ univ = 0 then Measure.dirac (Classical.choice ‹Nonempty S›) else (κ univ)⁻¹ • κ

instance finiteIntensityMarks_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] : IsProbabilityMeasure (finiteIntensityMarks κ) := by
  by_cases hκ : κ univ = 0
  · simp only [finiteIntensityMarks,ite_eq_left hκ]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  · constructor
    simp [finiteIntensityMarks,hκ,ENNReal.inv_mul_cancel hκ (measure_ne_top _ _)]

def poissonRandomMeasureLaw {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] : Measure (Measure S) :=
  countablePoissonLaw (fun i => ((sfiniteSeq κ i) univ).toNNReal)
    (fun i => finiteIntensityMarks (sfiniteSeq κ i))

instance poissonRandomMeasureLaw_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] : IsProbabilityMeasure (poissonRandomMeasureLaw κ) := by
  unfold poissonRandomMeasureLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLogIntensity
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

def stableLogIntensity (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (b * Real.exp (-b*x)))

instance stableLogIntensity_sigmaFinite (b : ℝ) : SigmaFinite (stableLogIntensity b) := by
  unfold stableLogIntensity
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def logMarkShift {S : Type*} (F : S → ℝ) (p : ℝ × S) : ℝ × S :=
  (p.1 + F p.2,p.2)

def finiteMeasureCutKernel {S : Type*} [MeasurableSpace S] (n : ℕ) : Kernel (Measure S) S where
  toFun η := if η univ ≤ n then η else 0
  measurable' := measurable_id.piecewise
    (measurableSet_le (Measure.measurable_coe .univ) measurable_const) measurable_const

instance finiteMeasureCutKernel_finite {S : Type*} [MeasurableSpace S] (n : ℕ) :
    IsFiniteKernel (finiteMeasureCutKernel (S := S) n) := by
  refine ⟨n,by simp,fun η => ?_⟩
  change (if η univ ≤ n then η else 0) univ ≤ n
  split_ifs with h
  · exact h
  · simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
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

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def tiltIntegral (v F : S → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (t * v x) * F x ∂μ

def tiltPartition (v : S → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (t * v x) ∂μ

def tiltMean (v F : S → ℝ) (t : ℝ) : ℝ := tiltIntegral μ v F t / tiltPartition μ v t

def tiltLaw (v : S → ℝ) (t : ℝ) : Measure S :=
  (ENNReal.ofReal (tiltPartition μ v t))⁻¹ •
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (t * v x)))

end Tilt

def replicaPotential {S : Type*} (v : S → ℝ) (n : ℕ) (x : Fin n → S) : ℝ := ∑ i, v (x i)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianField
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

section GaussianField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def gaussianField (n : ℕ) (v : Fin n → S → ℝ) (g : Fin n → ℝ) (x : S) : ℝ :=
  ∑ i, g i * v i x

end GaussianField

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
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

abbrev CovarianceMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] := {C : Matrix ι ι ℝ // C.PosSemidef}

instance covarianceMatrixMeasurableSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (CovarianceMatrix ι) :=
  inferInstanceAs (MeasurableSpace {C : ι → ι → ℝ // Matrix.PosSemidef C})

instance covarianceMatrixBorelSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    BorelSpace (CovarianceMatrix ι) :=
  inferInstanceAs (BorelSpace {C : ι → ι → ℝ // Matrix.PosSemidef C})

def gaussianCovarianceLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (p : EuclideanSpace ℝ ι × CovarianceMatrix ι) :
    ProbabilityMeasure (EuclideanSpace ℝ ι) := ⟨multivariateGaussian p.1 p.2.val, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

lemma gaussianCovarianceLaw_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (gaussianCovarianceLaw (ι := ι)) := by
  classical
  have : SequentialSpace (EuclideanSpace ℝ ι × CovarianceMatrix ι) :=
    inferInstanceAs (SequentialSpace (EuclideanSpace ℝ ι × {C : ι → ι → ℝ // Matrix.PosSemidef C}))
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto (fun n => charFun (multivariateGaussian (p n).1 (p n).2.val) t) atTop
    (𝓝 (charFun (multivariateGaussian p₀.1 p₀.2.val) t))
  simp_rw [charFun_multivariateGaussian (p _).2.property,charFun_multivariateGaussian p₀.2.property]
  have hc : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι =>
      Complex.exp (((inner ℝ t q.1 : ℝ) : ℂ)*Complex.I -
        ((∑ i, t i * ∑ j, q.2.val i j * t j : ℝ) : ℂ)/2)) := by
    have he (i j : ι) : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => q.2.val i j) :=
      (show Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => q.2.val) from
        continuous_subtype_val.comp continuous_snd).matrix_elem i j
    have hi : Continuous (fun q : EuclideanSpace ℝ ι × CovarianceMatrix ι => inner ℝ t q.1) :=
      continuous_const.inner continuous_fst
    exact ((Complex.continuous_ofReal.comp hi).mul continuous_const |>.sub
      ((Complex.continuous_ofReal.comp (continuous_finsetSum _ fun i _ => continuous_const.mul
        (continuous_finsetSum _ fun j _ => (he i j).mul continuous_const))).div_const 2)).cexp
  exact hc.continuousAt.tendsto.comp hp

lemma gaussianCovariance_integral_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    Continuous (fun p : EuclideanSpace ℝ ι × CovarianceMatrix ι =>
      ∫ x, f x ∂multivariateGaussian p.1 p.2.val) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp gaussianCovarianceLaw_continuous

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianRows (v : ι → E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => innerSL ℝ (v i))

end GaussianRows

def gaussianReplicaTest {ι : Type*} [Fintype ι] (f : ℝ →ᵇ ℝ) : EuclideanSpace ℝ ι →ᵇ ℝ :=
  ∏ i, f.compContinuous ⟨fun z => z i, by fun_prop⟩

def gramCovariance {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E) : CovarianceMatrix ι :=
  ⟨Matrix.gram ℝ v,Matrix.posSemidef_gram ℝ v⟩

def gaussianCovarianceKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) : CovarianceMatrix ι →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun C => ∫ z, f z ∂multivariateGaussian 0 C.val,
      (gaussianCovariance_integral_continuous f).comp (continuous_const.prodMk continuous_id)⟩
    (2*‖f‖) (by
      intro C D
      calc
        dist (∫ z, f z ∂multivariateGaussian 0 C.val) (∫ z, f z ∂multivariateGaussian 0 D.val) ≤
            ‖∫ z, f z ∂multivariateGaussian 0 C.val‖ + ‖∫ z, f z ∂multivariateGaussian 0 D.val‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_integral_le_norm _) (f.norm_integral_le_norm _)
        _ = 2*‖f‖ := by ring)

open TopologicalSpace

abbrev CompactOverlap := Set.Icc (-1 : ℝ) 1
abbrev CompactJointOverlap := CompactOverlap × unitInterval
abbrev CompactArray (K : Type*) := ℕ → ℕ → K
abbrev CompactBlock (K : Type*) (n : ℕ) := Fin n → Fin n → K

def compactBlock {K : Type*} (n : ℕ) (Q : CompactArray K) : CompactBlock K n :=
  fun i j => Q i j

lemma compactBlock_continuous {K : Type*} [TopologicalSpace K] (n : ℕ) :
    Continuous (compactBlock (K := K) n) := by unfold compactBlock; fun_prop

def compactGGDefect {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) : ℝ :=
  (n : ℝ)*(∫ Q, f (compactBlock n Q)*g (Q i n) ∂μ) -
    (∫ Q, f (compactBlock n Q) ∂μ)*(∫ Q : CompactArray K, g (Q 0 1) ∂μ) -
    ∑ j ∈ Finset.univ.erase i, ∫ Q, f (compactBlock n Q)*g (Q i j) ∂μ

open scoped Polynomial

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
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

@[simp] theorem timeLaw_eq_volume : timeLaw = (volume : Measure Time) := rfl

instance instIsProbabilityMeasureElemRealTimeTimeLaw : IsProbabilityMeasure timeLaw := by
  rw [timeLaw_eq_volume]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instNullSingletonClassElemRealTimeTimeLaw : NullSingletonClass timeLaw := by
  rw [timeLaw_eq_volume]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[simp] theorem controlCost_zero (P : Measure BrownianPath) (m : Trial) :
    controlCost P m (fun _ _ => 0) = 0 := by
  simp [controlCost]

@[simp] theorem controlPayoff_zero (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    controlPayoff P f m (fun _ _ => 0) = ∫ ω, f (brownianEval 1 ω) ∂P := by
  simp [controlPayoff]

def oneTrial : Trial where
  toFun := fun _ => 1
  monotone := monotone_const
  measurable := measurable_const
  nonneg := fun _ => zero_le_one
  le_one := fun _ => le_rfl

@[simp] theorem oneTrial_apply (t : Time) : oneTrial t = 1 := rfl

@[simp] theorem tailIntegral_oneTrial (t : Time) :
    tailIntegral oneTrial t = 1 - (t : ℝ) := by
  simp [tailIntegral, Measure.real, ENNReal.toReal_ofReal, sub_nonneg.mpr t.2.2]

@[simp] theorem entropy_oneTrial : entropy oneTrial = 0 := by
  simp [entropy]

instance instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw (N : ℕ) : IsProbabilityMeasure (unitSphereLaw (N + 1)) := by
  have : NeZero ((volume : Measure (Spin (N + 1))).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instIsProbabilityMeasureSpinHAddNatOfNatSphereLaw (N : ℕ) : IsProbabilityMeasure (sphereLaw (N + 1)) := by
  unfold sphereLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlDrift
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

def controlDrift (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) : ℝ :=
  ∫ t, m t * v t ω ∂timeLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
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

@[instance_reducible] def rawBrownianSigma (s : ℝ≥0) : MeasurableSpace BrownianPath :=
  ⨆ r : {r : ℝ≥0 // r ≤ s},
    MeasurableSpace.comap (brownianEval r.val) (borel ℝ)

def clipControl (L : ℝ) (v : Time → BrownianPath → ℝ) : Time → BrownianPath → ℝ :=
  fun t ω => max (-L) (min L (v t ω))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianAverage
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

lemma bounded_real_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : AEMeasurable Y P)
    (C : ℝ) (hC : ∀ᵐ ω ∂P, |Y ω| ≤ C) : Integrable Y P := by
  exact (integrable_const C).mono' hY.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hC)

lemma boundedContinuousFunction_integrable_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (f : ℝ →ᵇ ℝ) {X : Ω → ℝ}
    (hX : AEMeasurable X P) : Integrable (fun ω => f (X ω)) P := by
  exact bounded_real_integrable (f.continuous.measurable.comp_aemeasurable hX) ‖f‖
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (X ω))

def gaussianAverage (s : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x + z) ∂gaussianReal 0 s

lemma gaussianAverage_integrable (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Integrable (fun z => f (x + z)) (gaussianReal 0 s) :=
  boundedContinuousFunction_integrable_comp f (by fun_prop)

lemma gaussianAverage_abs_le (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |gaussianAverage s f x| ≤ ‖f‖ := by
  simpa [gaussianAverage, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const (μ := gaussianReal 0 s)
      (Filter.Eventually.of_forall fun z => f.norm_coe_le_norm (x+z))

lemma gaussianAverage_continuous (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Continuous (gaussianAverage s f) := by
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro x; exact (gaussianAverage_integrable s f x).aestronglyMeasurable
  · intro x; exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm (x+z)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun z => f.continuous.comp (continuous_id.add continuous_const)

def gaussianAverageBCF (s : ℝ≥0) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨gaussianAverage s f, gaussianAverage_continuous s f⟩
    (2*‖f‖) (by
      intro x y
      change |gaussianAverage s f x - gaussianAverage s f y| ≤ 2 * ‖f‖
      exact (abs_sub _ _).trans (by linarith [gaussianAverage_abs_le s f x, gaussianAverage_abs_le s f y]))

@[simp] lemma gaussianAverageBCF_coe (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (gaussianAverageBCF s f : ℝ → ℝ) = gaussianAverage s f := rfl

@[simp] lemma gaussianAverage_zero (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage 0 f x = f x := by simp [gaussianAverage]

lemma gaussianAverage_hasDerivAt (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f : ℝ → ℝ) (f' x) x) (x : ℝ) :
    HasDerivAt (gaussianAverage s f) (gaussianAverage s f' x) x := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun x z => f (x+z)) (F' := fun x z => f' (x+z)) (bound := fun _ => ‖f'‖)
    (μ := gaussianReal 0 s) (by simp)
    (Filter.Eventually.of_forall fun x => (gaussianAverage_integrable s f x).aestronglyMeasurable)
    (gaussianAverage_integrable s f x)
    (gaussianAverage_integrable s f' x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z x _ => f'.norm_coe_le_norm (x+z)) (integrable_const _)
    (Filter.Eventually.of_forall fun z x _ => by convert! (hf (x+z)).comp x ((hasDerivAt_id x).add_const z) using 1; simp only [mul_one])).2

lemma exp_bcf_bound (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |Real.exp (d * f x)| ≤ Real.exp (|d| * ‖f‖) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    d * f x ≤ |d * f x| := le_abs_self _
    _ = |d| * |f x| := abs_mul _ _
    _ ≤ |d| * ‖f‖ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (abs_nonneg d)

def expBCF (d : ℝ) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => Real.exp (d*f x), by fun_prop⟩
    (2 * Real.exp (|d| * ‖f‖)) (by
      intro x y; change |Real.exp (d * f x) - Real.exp (d * f y)| ≤ 2 * Real.exp (|d| * ‖f‖)
      exact (abs_sub _ _).trans (by linarith [exp_bcf_bound d f x, exp_bcf_bound d f y]))

@[simp] lemma expBCF_apply (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    expBCF d f x = Real.exp (d * f x) := rfl

lemma gaussianAverage_exp_pos (s : ℝ≥0) (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    0 < gaussianAverage s (expBCF d f) x := by
  apply integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos (d*f (x+z))).le)
    (gaussianAverage_integrable s (expBCF d f) x) |>.mpr
  simpa only [Function.support, expBCF_apply, ne_eq, Real.exp_ne_zero, not_false_eq_true,
    Set.ofPred_true, measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)

lemma gaussianAverage_exp_bounds (s : ℝ≥0) (d : ℝ) (hd : 0 ≤ d) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (-d*‖f‖) ≤ gaussianAverage s (expBCF d f) x ∧
      gaussianAverage s (expBCF d f) x ≤ Real.exp (d*‖f‖) := by
  have hf : ∀ z, |f (x+z)| ≤ ‖f‖ := fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (x+z)
  constructor
  · have hi := integral_mono (integrable_const (Real.exp (-d*‖f‖)))
      (gaussianAverage_integrable s (expBCF d f) x) (fun z =>
        Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (hf z)).1]))
    simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi
  · have hi := integral_mono (gaussianAverage_integrable s (expBCF d f) x)
      (integrable_const (Real.exp (d*‖f‖))) (fun z =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hf z)).2 hd))
    simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

def heatLog (s : ℝ≥0) (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  if d = 0 then gaussianAverage s f x else (d : ℝ)⁻¹ * Real.log (gaussianAverage s (expBCF d f) x)

lemma heatLog_abs_le (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : |heatLog s d f x| ≤ ‖f‖ := by
  unfold heatLog
  split_ifs with hd
  · exact gaussianAverage_abs_le s f x
  have hd' : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  obtain ⟨hlo,hhi⟩ := gaussianAverage_exp_bounds s d d.coe_nonneg f x
  have hz := gaussianAverage_exp_pos s d f x
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log hz hhi
  rw [Real.log_exp] at hl hu
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hd'.le),
    mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hd'.le), inv_mul_cancel₀ hd'.ne']

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
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

lemma heatLog_continuous (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : Continuous (heatLog s d f) := by
  change Continuous (fun x => heatLog s d f x)
  by_cases hd : d = 0
  · simpa [heatLog, hd] using gaussianAverage_continuous s f
  · have hh := (gaussianAverage_continuous s (expBCF d f)).log (fun x => (gaussianAverage_exp_pos s d f x).ne')
    simpa only [heatLog, hd, ↓reduceIte] using hh.const_mul (d : ℝ)⁻¹

def heatLogBCF (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨heatLog s d f, heatLog_continuous s d f⟩
    (2*‖f‖) (by
      intro x y; change |heatLog s d f x - heatLog s d f y| ≤ 2 * ‖f‖
      exact (abs_sub _ _).trans (by linarith [heatLog_abs_le s d f x, heatLog_abs_le s d f y]))

@[simp] lemma heatLogBCF_coe (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (heatLogBCF s d f : ℝ → ℝ) = heatLog s d f := rfl

structure Jet3 where
  f : ℝ →ᵇ ℝ
  d1 : ℝ →ᵇ ℝ
  d2 : ℝ →ᵇ ℝ
  d3 : ℝ →ᵇ ℝ
  has1 : ∀ x, HasDerivAt (f : ℝ → ℝ) (d1 x) x
  has2 : ∀ x, HasDerivAt (d1 : ℝ → ℝ) (d2 x) x
  has3 : ∀ x, HasDerivAt (d2 : ℝ → ℝ) (d3 x) x

def Jet3.gaussianAverage (s : ℝ≥0) (g : Jet3) : Jet3 where
  f := gaussianAverageBCF s g.f
  d1 := gaussianAverageBCF s g.d1
  d2 := gaussianAverageBCF s g.d2
  d3 := gaussianAverageBCF s g.d3
  has1 := gaussianAverage_hasDerivAt s g.f g.d1 g.has1
  has2 := gaussianAverage_hasDerivAt s g.d1 g.d2 g.has2
  has3 := gaussianAverage_hasDerivAt s g.d2 g.d3 g.has3

def Jet3.exp (d : ℝ) (g : Jet3) : Jet3 where
  f := expBCF d g.f
  d1 := d • (expBCF d g.f * g.d1)
  d2 := expBCF d g.f * (d^2 • (g.d1^2) + d • g.d2)
  d3 := expBCF d g.f * (d^3 • (g.d1^3) + (3*d^2) • (g.d1*g.d2) + d • g.d3)
  has1 x := by
    convert! ((g.has1 x).const_mul d).exp using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [expBCF]
    ring
  has2 x := by
    have he := ((g.has1 x).const_mul d).exp
    have h := (he.mul (g.has2 x)).const_mul d
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [expBCF]; ring
  has3 x := by
    have he := ((g.has1 x).const_mul d).exp
    have h := he.mul (((g.has2 x).pow 2).const_mul (d^2) |>.add ((g.has3 x).const_mul d))
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [expBCF]; ring

lemma inv_bcf_bound {g : ℝ →ᵇ ℝ} {c : ℝ} (hc : 0 < c) (hg : ∀ x, c ≤ g x) (x : ℝ) :
    |(g x)⁻¹| ≤ c⁻¹ := by
  rw [abs_of_pos (inv_pos.mpr (hc.trans_le (hg x)))]
  exact inv_anti₀ hc (hg x)

def invBCF (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (g x)⁻¹, g.continuous.inv₀ (fun x => (hc.trans_le (hg x)).ne')⟩
    (2*c⁻¹) (by
      intro x y; change |(g x)⁻¹ - (g y)⁻¹| ≤ 2*c⁻¹
      exact (abs_sub _ _).trans (by linarith [inv_bcf_bound hc hg x, inv_bcf_bound hc hg y]))

@[simp] lemma invBCF_apply (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) (x : ℝ) :
    invBCF g c hc hg x = (g x)⁻¹ := rfl

lemma invBCF_hasDerivAt (g g' : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x)
    (hder : ∀ x, HasDerivAt (g : ℝ → ℝ) (g' x) x) (x : ℝ) :
    HasDerivAt (invBCF g c hc hg : ℝ → ℝ) (- g' x * (invBCF g c hc hg x)^2) x := by
  convert! (hder x).inv (hc.trans_le (hg x)).ne' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [invBCF_apply, div_eq_mul_inv, inv_pow]

def Jet3.heatLogPos (s d : ℝ≥0) (hd : d ≠ 0) (g : Jet3) : Jet3 :=
  let A := (g.exp d).gaussianAverage s
  let c := Real.exp (-d * ‖g.f‖)
  let hc : 0 < c := Real.exp_pos _
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  { f := heatLogBCF s d g.f
    d1 := (d : ℝ)⁻¹ • (A.d1 * J)
    d2 := (d : ℝ)⁻¹ • (A.d2 * J - A.d1^2 * J^2)
    d3 := (d : ℝ)⁻¹ • (A.d3 * J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))
    has1 x := by
      have hh := ((A.has1 x).log (hc.trans_le (hA x)).ne').const_mul (d : ℝ)⁻¹
      convert! hh using 1
      · ext y
        simp only [heatLogBCF_coe, heatLog, hd, ↓reduceIte]
        rfl
    has2 x := by
      have hi := invBCF_hasDerivAt A.f A.d1 c hc hA A.has1 x
      have hh := ((A.has2 x).mul hi).const_mul (d : ℝ)⁻¹
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
        BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_pow,
        Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
      ring
    has3 x := by
      have hi := invBCF_hasDerivAt A.f A.d1 c hc hA A.has1 x
      have hh := (((A.has3 x).mul hi).sub (((A.has2 x).pow 2).mul (hi.pow 2))).const_mul (d : ℝ)⁻¹
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
        BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_add,
        BoundedContinuousFunction.coe_pow, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      ring }

def Jet3.heatLog (s d : ℝ≥0) (g : Jet3) : Jet3 :=
  if hd : d = 0 then g.gaussianAverage s else g.heatLogPos s d hd

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_FiniteTerminal
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

def Jet3.ofCompactSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : Jet3 := by
  have h1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3 : ContDiff ℝ ∞ (deriv (deriv (deriv f))) := (contDiff_infty_iff_deriv.mp h2).2
  exact {
    f := ofCompactSupport f hf.continuous hs
    d1 := ofCompactSupport (deriv f) h1.continuous hs.deriv
    d2 := ofCompactSupport (deriv (deriv f)) h2.continuous hs.deriv.deriv
    d3 := ofCompactSupport (deriv (deriv (deriv f))) h3.continuous hs.deriv.deriv.deriv
    has1 := fun x => (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
    has2 := fun x => (h1.differentiable (by norm_num)).differentiableAt.hasDerivAt
    has3 := fun x => (h2.differentiable (by norm_num)).differentiableAt.hasDerivAt }

@[simp] lemma Jet3.ofCompactSmooth_apply (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (x : ℝ) : (Jet3.ofCompactSmooth f hf hs).f x = f x := rfl

abbrev RadialSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))

def radialNormalizer (n : ℕ) : ℝ := ((2*Real.pi)^(((n+1 : ℕ) : ℝ)/2))⁻¹

def canonicalRadialDensity (n : ℕ) (b : ℝ) (x : RadialSpace n) : ℝ :=
  radialNormalizer n * Real.exp (-(b/2)*‖x‖^2)

def canonicalRadialMass (n : ℕ) (b : ℝ) : Measure (RadialSpace n) :=
  volume.withDensity (fun x => ENNReal.ofReal (canonicalRadialDensity n b x))

lemma radialNormalizer_pos (n : ℕ) : 0 < radialNormalizer n := by
  unfold radialNormalizer
  positivity

lemma canonicalRadialDensity_pos (n : ℕ) (b : ℝ) (x : RadialSpace n) :
    0 < canonicalRadialDensity n b x := mul_pos (radialNormalizer_pos n) (Real.exp_pos _)

lemma canonicalRadialDensity_continuous (n : ℕ) (b : ℝ) :
    Continuous (canonicalRadialDensity n b) := by unfold canonicalRadialDensity; fun_prop

lemma integrable_exp_neg_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : RadialSpace n => Real.exp (-(b/2)*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := ((b/2 : ℝ) : ℂ)) (by simpa using half_pos hb) 0 (0 : RadialSpace n)).re
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg,
    ]
  exact (Complex.exp_ofReal_re _).symm

lemma canonicalRadialDensity_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (canonicalRadialDensity n b) :=
  (integrable_exp_neg_norm_sq n hb).const_mul _

lemma canonicalRadialDensity_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x, canonicalRadialDensity n b x) = b ^ (-((n+1 : ℕ) : ℝ)/2) := by
  simp only [canonicalRadialDensity]
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (half_pos hb)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show Real.pi/(b/2) = (2*Real.pi)/b by ring,Real.div_rpow (by positivity) hb.le]
  unfold radialNormalizer
  rw [show -((n+1 : ℕ) : ℝ)/2 = -(((n+1 : ℕ) : ℝ)/2) by ring, Real.rpow_neg hb.le]
  field_simp

instance instIsProbabilityMeasureRadialSpaceCanonicalRadialMassOfNatReal (n : ℕ) : IsProbabilityMeasure (canonicalRadialMass n 1) := by
  constructor
  rw [canonicalRadialMass,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal
      (canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1))
      (Eventually.of_forall fun x => (canonicalRadialDensity_pos n 1 x).le),
    canonicalRadialDensity_integral n (by norm_num : (0:ℝ)<1)]
  simp

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereIsometryMap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSpinHAddNatOfNatSphereLaw
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
section SphereInvariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereIsometryMap (e : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    Metric.sphere (0 : E) 1 := ⟨e x, by simp⟩

omit [FiniteDimensional ℝ E] in
lemma sphereIsometryMap_measurable (e : E ≃ₗᵢ[ℝ] E) : Measurable (sphereIsometryMap e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sphereIsometryMap_preimage_cone (e : E ≃ₗᵢ[ℝ] E) (s : Set (Metric.sphere (0 : E) 1)) :
    Ioo (0:ℝ) 1 • (Subtype.val '' (sphereIsometryMap e ⁻¹' s)) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨r,hr,e u,⟨sphereIsometryMap e u,hu,rfl⟩,by simp⟩
  · rintro ⟨r,hr,v,⟨u,hu,rfl⟩,he⟩
    refine ⟨r,hr,e.symm u,⟨sphereIsometryMap e.symm u,?_,rfl⟩,?_⟩
    · simpa [sphereIsometryMap] using hu
    · apply e.injective
      simpa only [map_smul,LinearIsometryEquiv.apply_symm_apply] using he

lemma sphereIsometryMap_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometryMap e) (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereIsometryMap_measurable e) hs,
    Measure.toSphere_apply' _ ((sphereIsometryMap_measurable e) hs),Measure.toSphere_apply' _ hs,
    sphereIsometryMap_preimage_cone]
  congr 1
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

end SphereInvariance

lemma unitSphereLaw_isometry_preserving {N : ℕ} (e : Spin N ≃ₗᵢ[ℝ] Spin N) :
    MeasurePreserving (sphereIsometryMap e) (unitSphereLaw N) (unitSphereLaw N) := by
  refine ⟨sphereIsometryMap_measurable e,?_⟩
  unfold unitSphereLaw
  rw [Measure.map_smul,
    (sphereIsometryMap_preserving e).map_eq]

def normalizedMeasure {S : Type*} [MeasurableSpace S] (μ : Measure S) : Measure S :=
  (μ univ)⁻¹ • μ

lemma measurable_measure_withDensity_fixed {S : Type*} [MeasurableSpace S]
    {f : S → ℝ≥0∞} (hf : Measurable f) : Measurable (fun μ : Measure S => μ.withDensity f) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [withDensity_apply _ hs,← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hf.indicator hs)

lemma normalizedMeasure_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (normalizedMeasure (S := S)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  change Measurable (fun μ : Measure S => (μ univ)⁻¹ * μ s)
  exact (Measure.measurable_coe MeasurableSet.univ).inv.mul (Measure.measurable_coe hs)

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_NormSquareBand
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

def normSquareBand (n : ℕ) (ε : ℝ) : Set (RadialSpace n) :=
  {x | ((n+1 : ℕ) : ℝ)*(1-ε) ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1+ε)}

lemma unitSphere_continuous_integrable {n : ℕ}
    {f : Metric.sphere (0 : Spin (n+1)) 1 → ℝ} (hf : Continuous f) :
    Integrable f (unitSphereLaw (n+1)) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun u => hC u (mem_univ _))

def sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) : ℝ :=
  ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.exp (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1)

lemma sphericalExp_even (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z (-r) = sphericalExp n z r := by
  have hemb : MeasurableEmbedding (sphereIsometryMap (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))) := by
    apply Measurable.measurableEmbedding
      (sphereIsometryMap_measurable _) _
    intro u v huv
    apply Subtype.ext
    have := congrArg Subtype.val huv
    simpa [sphereIsometryMap] using this
  have h := (unitSphereLaw_isometry_preserving (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))).integral_comp hemb
    (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (r * inner ℝ z (u:Spin (n+1))))
  simpa [sphericalExp,sphereIsometryMap] using h

lemma sphericalExp_eq_cosh (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z r =
      ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.cosh (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1) := by
  have hi (s : ℝ) : Integrable (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (s * inner ℝ z (u:Spin (n+1)))) (unitSphereLaw (n+1)) :=
    unitSphere_continuous_integrable (by fun_prop)
  simp only [Real.cosh_eq,integral_div]
  rw [integral_add (hi r) (by simpa only [neg_mul] using hi (-r))]
  simp only [← neg_mul]
  change sphericalExp n z r = (sphericalExp n z r + sphericalExp n z (-r))/2
  rw [sphericalExp_even]
  ring

lemma one_le_sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    1 ≤ sphericalExp n z r := by
  rw [sphericalExp_eq_cosh]
  calc
    (1:ℝ) = ∫ _ : Metric.sphere (0:Spin (n+1)) 1, (1:ℝ) ∂unitSphereLaw (n+1) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (unitSphere_continuous_integrable (by fun_prop)) (fun u => Real.one_le_cosh _)

section Polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma polar_lintegral (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ u : Metric.sphere (0:E) 1, ∫⁻ r : Ioi (0:ℝ),
        f ((r:ℝ) • (u:E)) ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
  let h := homeomorphUnitSphereProd E
  let F : Metric.sphere (0:E) 1 × Ioi (0:ℝ) → ℝ≥0∞ :=
    fun p => f ((p.2:ℝ) • (p.1:E))
  have hF : Measurable F := hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)
  calc
    _ = ∫⁻ x : ({(0:E)}ᶜ : Set E), f (x:E) ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫⁻ p, F p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      convert (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hF) using 1
      all_goals try with_reducible_and_instances rfl
      apply lintegral_congr
      intro x
      change f (x:E) = f ((h x).2.val • (h x).1.val)
      have he := congrArg Subtype.val (h.symm_apply_apply x)
      exact congrArg f he.symm
    _ = _ := lintegral_prod _ hF.aemeasurable

lemma polar_lintegral_swap (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂μ.toSphere ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) := by
  rw [polar_lintegral μ f hf]
  exact lintegral_lintegral_swap
    (hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)).aemeasurable

def normalizedAngular : Measure (Metric.sphere (0:E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

def haarRadiusMeasure : Measure (Ioi (0:ℝ)) :=
  μ.toSphere univ • Measure.volumeIoiPow (Module.finrank ℝ E - 1)

lemma angular_total_ne_zero : μ.toSphere univ ≠ 0 := by
  exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero μ)

lemma polar_lintegral_normalized (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂normalizedAngular μ ∂haarRadiusMeasure μ := by
  rw [haarRadiusMeasure,lintegral_smul_measure]
  simp only [normalizedAngular,lintegral_smul_measure,smul_eq_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (angular_total_ne_zero μ)),← mul_assoc,
    ENNReal.mul_inv_cancel (angular_total_ne_zero μ) (measure_ne_top _ _),one_mul]
  exact polar_lintegral_swap μ f hf

lemma polar_weighted_lintegral (f : E → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g ‖x‖ * f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), g r * (∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂normalizedAngular μ) ∂haarRadiusMeasure μ := by
  rw [polar_lintegral_normalized μ (fun x => g ‖x‖ * f x) ((hg.comp measurable_norm).mul hf)]
  apply lintegral_congr
  intro r
  have hnorm (u : Metric.sphere (0:E) 1) : ‖(r:ℝ) • (u:E)‖ = (r:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property]; simp
  simp only [hnorm]
  exact lintegral_const_mul _ ((hf.comp (measurable_subtype_coe.const_smul (r:ℝ))))

end Polar

def canonicalBandRadiusWeight (n : ℕ) (b ε : ℝ) : ℝ → ℝ≥0∞ :=
  {r : ℝ | ((n+1:ℕ):ℝ)*(1-ε) ≤ r^2 ∧ r^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)}.indicator
    (fun r => ENNReal.ofReal (radialNormalizer n * Real.exp (-(b/2)*r^2)))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatTilt
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

def heatTilt (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  gaussianAverage s (expBCF d f * h) x / gaussianAverage s (expBCF d f) x

lemma gaussianAverage_add (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (f+h : ℝ →ᵇ ℝ) x = gaussianAverage s f x + gaussianAverage s h x :=
  integral_add (gaussianAverage_integrable s f x) (gaussianAverage_integrable s h x)

lemma gaussianAverage_smul (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    gaussianAverage s (a • f : ℝ →ᵇ ℝ) x = a * gaussianAverage s f x := by
  exact integral_const_mul _ _

lemma heatTilt_add (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTilt s d f (h+k) x = heatTilt s d f h x + heatTilt s d f k x := by
  unfold heatTilt
  change gaussianAverage s (expBCF d f * (h+k) : ℝ →ᵇ ℝ) x / _ = _
  rw [mul_add,gaussianAverage_add,add_div]
  rfl

lemma heatTilt_smul (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (a x : ℝ) :
    heatTilt s d f (a • h) x = a * heatTilt s d f h x := by
  unfold heatTilt
  change gaussianAverage s (expBCF d f * (a • h) : ℝ →ᵇ ℝ) x / _ = _
  rw [mul_smul_comm,gaussianAverage_smul,mul_div_assoc]
  rfl

lemma heatTilt_const (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    heatTilt s d f (BoundedContinuousFunction.const ℝ a) x = a := by
  unfold heatTilt gaussianAverage
  simp only [Pi.mul_apply,BoundedContinuousFunction.const_apply]
  rw [integral_mul_const]
  exact mul_div_cancel_left₀ a (gaussianAverage_exp_pos s d f x).ne'

lemma heatTilt_mono (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ)
    (hh : ∀ x, h x ≤ k x) (x : ℝ) : heatTilt s d f h x ≤ heatTilt s d f k x := by
  apply div_le_div_of_nonneg_right _ (gaussianAverage_exp_pos s d f x).le
  exact integral_mono (gaussianAverage_integrable s (expBCF d f*h) x)
    (gaussianAverage_integrable s (expBCF d f*k) x)
    (fun z => mul_le_mul_of_nonneg_left (hh _) (Real.exp_pos _).le)

lemma heatTilt_abs_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatTilt s d f h x| ≤ ‖h‖ := by
  rw [abs_le]
  constructor
  · have hh := heatTilt_mono s d f (BoundedContinuousFunction.const ℝ (-‖h‖)) h
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).1) x
    simpa only [heatTilt_const] using hh
  · have hh := heatTilt_mono s d f h (BoundedContinuousFunction.const ℝ ‖h‖)
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).2) x
    simpa only [heatTilt_const] using hh

lemma heatTilt_continuous (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : Continuous (heatTilt s d f h) :=
  (gaussianAverage_continuous s (expBCF d f*h)).div
    (gaussianAverage_continuous s (expBCF d f)) (fun x => (gaussianAverage_exp_pos s d f x).ne')

def heatTiltBCF (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨heatTilt s d f h,heatTilt_continuous s d f h⟩
    (2*‖h‖) (fun x y => by
      change |heatTilt s d f h x - heatTilt s d f h y| ≤ 2*‖h‖
      exact (abs_sub _ _).trans (by linarith [heatTilt_abs_le s d f h x,heatTilt_abs_le s d f h y]))

@[simp] lemma heatTiltBCF_apply (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTiltBCF s d f h x = heatTilt s d f h x := rfl

lemma heatTiltBCF_norm_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : ‖heatTiltBCF s d f h‖ ≤ ‖h‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg h)).mpr (heatTilt_abs_le s d f h)

def heatTiltCLM (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := heatTiltBCF s d f
      map_add' := fun h k => by ext x; exact heatTilt_add s d f h k x
      map_smul' := fun a h => by ext x; exact heatTilt_smul s d f h a x }
    1 (fun h => by
      change ‖heatTiltBCF s d f h‖ ≤ 1*‖h‖
      simpa only [one_mul] using heatTiltBCF_norm_le s d f h)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BcfEvalRingHom
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

def bcfEvalRingHom (x : ℝ) : (ℝ →ᵇ ℝ) →+* ℝ where
  toFun := fun f => f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def heatGenerator (d : ℝ≥0) (g : Jet3) : ℝ →ᵇ ℝ :=
  (1/2 : ℝ) • (g.d2 + (d : ℝ) • g.d1^2)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedC1
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

def BoundedC1 (f : ℝ→ᵇ ℝ) : Prop := ∃ f' : ℝ→ᵇ ℝ, ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x

structure HeatIntervalParam where
  duration : ℝ → ℝ
  rate : ℝ
  coefficient : ℝ≥0

def parametricHeatJet (g : Jet3) : List HeatIntervalParam → ℝ → Jet3
  | [], _ => g
  | p::ps, t => (parametricHeatJet g ps t).heatLog (p.duration t).toNNReal p.coefficient

def heatBoundaryTerms (g : Jet3) (θ : ℝ) : List HeatIntervalParam → ℝ → List (ℝ×(ℝ→ᵇ ℝ))
  | [], _ => []
  | [_], _ => []
  | p::q::ps, a =>
    let u := parametricHeatJet g (q::ps) θ
    let T := heatTiltCLM (p.duration θ).toNNReal p.coefficient u.f
    (((q.coefficient:ℝ)-(p.coefficient:ℝ))*(a+p.rate),T (u.d1^2)) ::
      (heatBoundaryTerms g θ (q::ps) (a+p.rate)).map (fun z => (z.1,T z.2))

def heatBoundarySum (g : Jet3) (θ : ℝ) (ps : List HeatIntervalParam) (a : ℝ) : ℝ→ᵇ ℝ :=
  ((heatBoundaryTerms g θ ps a).map (fun z => z.1 • z.2)).sum

def firstHeatGenerator (g : Jet3) (ps : List HeatIntervalParam) (θ : ℝ) : ℝ→ᵇ ℝ :=
  match ps with
  | [] => 0
  | p::_ => heatGenerator p.coefficient (parametricHeatJet g ps θ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_StableCascade
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

def StableCascade : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×StableCascade n))

instance stableCascadeNonempty (n : ℕ) : Nonempty (StableCascade n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×StableCascade n))⟩

def cascadeTotalE : (n : ℕ) → StableCascade n → ℝ≥0∞
  | 0, _ => 1
  | n+1, η => ∫⁻ p : ℝ×StableCascade n,
      ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 ∂η

def cascadeTotal (n : ℕ) (η : StableCascade n) : ℝ := (cascadeTotalE n η).toReal

def cascadeLaw : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (StableCascade n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      (cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n))),by exact poissonRandomMeasureLaw_probability _⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableMassKernel
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

def stableMassKernel : Kernel (Measure ℝ) ℝ where
  toFun η := normalizedMeasure (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)))
  measurable' := normalizedMeasure_measurable.comp (measurable_measure_withDensity_fixed (by fun_prop))

def stableEppfValue (a b : ℝ) (rs : List ℝ) : ℝ :=
  Real.Gamma (1-a)/Real.Gamma (rs.sum-a)*
    (∏ ℓ ∈ Finset.range (rs.length-1), (((ℓ:ℝ)+1)*b-a))*
    (rs.map (fun r => Real.Gamma (r-b)/Real.Gamma (1-b))).prod

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableTotalBiasedLaw
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

variable {S : Type*} [MeasurableSpace S]

def markedStableTotalE (η : Measure (ℝ × S)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂η

@[fun_prop] lemma markedStableTotalE_measurable : Measurable (markedStableTotalE (S := S)) :=
  Measure.measurable_lintegral (by fun_prop)

def markedStableTotal (η : Measure (ℝ × S)) : ℝ := (markedStableTotalE η).toReal

@[fun_prop] lemma markedStableTotal_measurable : Measurable (markedStableTotal (S := S)) :=
  markedStableTotalE_measurable.ennreal_toReal

def markedStableMassKernel : Kernel (Measure (ℝ × S)) (ℝ × S) where
  toFun η := normalizedMeasure (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)))
  measurable' := normalizedMeasure_measurable.comp (measurable_measure_withDensity_fixed (by fun_prop))

instance markedStableMassKernel_finite : IsFiniteKernel (markedStableMassKernel (S := S)) := by
  refine ⟨1, by simp, ?_⟩
  intro η
  change (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ)⁻¹ *
    (η.withDensity (fun p => ENNReal.ofReal (Real.exp p.1)) univ) ≤ 1
  exact ENNReal.inv_mul_le_one _

def markedStableCountKernel : Kernel (Measure (ℝ × S)) (ℝ × S) :=
  markedStableMassKernel.withDensity (fun η p => ENNReal.ofReal (markedStableTotal η*Real.exp (-p.1)))

instance markedStableCountKernel_sfinite : IsSFiniteKernel (markedStableCountKernel (S := S)) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

variable [Nonempty S]

def markedDistinctMoment : List (ℝ × (S → ℝ≥0∞)) → {m : ℕ} → Measure (ℝ × S) → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | rf::rs, _, η, z => ∫⁻ p, if ∃ i, z i = p.1 then 0 else
      ENNReal.ofReal (Real.exp (rf.1*p.1))*rf.2 p.2*
        markedDistinctMoment rs η (Fin.cons p.1 z) ∂markedStableCountKernel η

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedTotalBiasedLaw
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
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]

def markedTotalBiasedLaw (ν : Measure S) [IsProbabilityMeasure ν] (a b : ℝ) : Measure (Measure (ℝ × S)) :=
  normalizedMeasure ((poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).withDensity
    (fun η => ENNReal.ofReal (markedStableTotal η^a)))

def markedOrderedDistinctMass (rs : List (ℝ × (S → ℝ≥0∞))) (η : Measure (ℝ × S)) {m : ℕ} (z : Fin m → ℝ) : ℝ≥0∞ :=
  markedDistinctMoment rs η z*ENNReal.ofReal (markedStableTotal η^(-(rs.map Prod.fst).sum))

def markedBlockProbability : List (ℕ × (S → ℝ≥0∞)) → {m : ℕ} → Measure (ℝ × S) → (Fin m → ℝ) → ℝ≥0∞
  | [], _, _, _ => 1
  | nf::ns, _, η, z => ∫⁻ p, if ∃ i, z i = p.1 then 0 else
      (stableMassKernel (η.map Prod.fst) {p.1})^(nf.1-1)*nf.2 p.2*
        markedBlockProbability ns η (Fin.cons p.1 z) ∂markedStableMassKernel η

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedTotalBiasedLaw
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
section MarkedStable
variable {S : Type*} [MeasurableSpace S]
variable [Nonempty S]

def exponentialMarkTilt (ν : Measure S) (b : ℝ) (X : S → ℝ) : Measure S :=
  normalizedMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*X x))))

def centeredLogMark (ν : Measure S) (b : ℝ) (X : S → ℝ) : S → ℝ :=
  fun x => X x-Real.log (∫ y, Real.exp (b*X y) ∂ν)/b

end MarkedStable

def cascadeBiasedLaw (n : ℕ) (z : Fin n → ℝ) (a : ℝ) : Measure (StableCascade n) :=
  normalizedMeasure ((cascadeLaw n z : Measure (StableCascade n)).withDensity
    (fun η => ENNReal.ofReal (cascadeTotal n η^a)))

@[reducible] def CascadeVisitShape : ℕ → Type
  | 0 => ℕ
  | n+1 => List (CascadeVisitShape n)

def cascadeVisitCount : (n : ℕ) → CascadeVisitShape n → ℕ
  | 0, r => r
  | n+1, ss => (ss.map (cascadeVisitCount n)).sum

def CascadeVisitShape.Valid : (n : ℕ) → CascadeVisitShape n → Prop
  | 0, r => 1 ≤ r
  | n+1, ss => ss ≠ [] ∧ ∀ s ∈ ss, CascadeVisitShape.Valid n s

def cascadeShapeProbability : (n : ℕ) → (Fin n → ℝ) → CascadeVisitShape n → StableCascade n → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, z, ss, η => markedBlockProbability
      (ss.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)))
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)

def cascadeShapeLikelihood : (n : ℕ) → (Fin n → ℝ) → ℝ → CascadeVisitShape n → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, z, a, ss =>
      (ss.map (cascadeShapeLikelihood n (fun i => z i.succ) (z 0))).prod *
      ENNReal.ofReal (stableEppfValue a (z 0) (ss.map (fun s => (cascadeVisitCount n s : ℝ))))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FocusedShapeProbability
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

def focusedShapeProbability : (n : ℕ) → (Fin n → ℝ) → ℕ → CascadeVisitShape n → StableCascade n → ℝ≥0∞
  | n, z, 0, s, η => cascadeShapeProbability n z s η
  | 0, _, _+1, _, _ => 0
  | _+1, _, _+1, [], _ => 0
  | n+1, z, d+1, s::ss, η => markedBlockProbability
      ((cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
        ss.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)))
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)

def focusedShapeNumerator : (n : ℕ) → (Fin n → ℝ) → ℝ → ℕ → CascadeVisitShape n → ℝ
  | n, _, a, 0, s => (cascadeVisitCount n s : ℝ)-a
  | 0, _, _, _+1, _ => 0
  | _+1, _, _, _+1, [] => 0
  | n+1, z, _, d+1, s::_ => focusedShapeNumerator n (fun i => z i.succ) (z 0) d s

@[reducible] def DecoratedCascade (S : Type) [MeasurableSpace S] : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×(S×DecoratedCascade S n)))

instance decoratedCascadeNonempty (S : Type) [MeasurableSpace S] (n : ℕ) :
    Nonempty (DecoratedCascade S n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×(S×DecoratedCascade S n)))⟩

def decoratedCascadeLaw {S : Type} [MeasurableSpace S] [Nonempty S]
    (ν : ProbabilityMeasure S) : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (DecoratedCascade S n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))),
        by exact poissonRandomMeasureLaw_probability _⟩

def decoratedCascadeTransform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → StableCascade n
  | 0, _, _ => ()
  | n+1, F, p => (markedStableCountKernel p.2).map (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2)))

def decoratedWeightedTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, F, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n),
      ENNReal.ofReal (Real.exp (q.1+F 0 (p.1,q.2.1))) *
        decoratedWeightedTotalE step n (fun i => F i.succ) (step (p.1,q.2.1),q.2.2)
          ∂markedStableCountKernel p.2

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_DecoratedWeightedTotal
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

def decoratedWeightedTotal {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ) (p : X×DecoratedCascade S n) : ℝ :=
      (decoratedWeightedTotalE step n F p).toReal

def fractionalLogMoment {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (b : ℝ) (f : X×S → ℝ) (x : X) : ℝ :=
  Real.log (∫ s, Real.exp (b*f (x,s)) ∂ν)/b

lemma fractionalLogMoment_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (b : ℝ) {f : X×S → ℝ} (hf : Measurable f) :
    Measurable (fractionalLogMoment ν b f) := by
  exact (((hf.const_mul b).exp.stronglyMeasurable.integral_prod_right').measurable.log).div_const b

def finiteCascadeLogRecursion {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (X → ℝ) → X → ℝ
  | 0, _, H => H
  | n+1, z, H => fractionalLogMoment ν (z 0)
      (fun p => finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step p))

lemma finiteCascadeLogRecursion_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) {H : X → ℝ} (hH : Measurable H) :
    Measurable (finiteCascadeLogRecursion ν step n z H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact fractionalLogMoment_measurable ν (z 0) ((ih (fun i => z i.succ)).comp hs)

def finiteCascadeShifts {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (X → ℝ) → Fin n → X×S → ℝ
  | 0, _, _ => Fin.elim0
  | n+1, z, H => Fin.cases
      (fun p => finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step p) -
        finiteCascadeLogRecursion ν step (n+1) z H p.1)
      (finiteCascadeShifts ν step n (fun i => z i.succ) H)

lemma finiteCascadeShifts_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) {H : X → ℝ} (hH : Measurable H) :
    ∀ i, Measurable (finiteCascadeShifts ν step n z H i) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) j) i
    exact ((finiteCascadeLogRecursion_measurable ν step hs n (fun j => z j.succ) hH).comp hs).sub
      ((finiteCascadeLogRecursion_measurable ν step hs (n+1) z hH).comp measurable_fst)

def decoratedTerminalTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (H : X → ℝ) : (n : ℕ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, p => ENNReal.ofReal (Real.exp (H p.1))
  | n+1, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n), ENNReal.ofReal (Real.exp q.1) *
      decoratedTerminalTotalE step H n (step (p.1,q.2.1),q.2.2) ∂markedStableCountKernel p.2

def decoratedTerminalTotal {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (H : X → ℝ) (n : ℕ) (p : X×DecoratedCascade S n) : ℝ :=
  (decoratedTerminalTotalE step H n p).toReal

def finiteCascadeFractionalIntegrable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → Prop
  | 0, _ => True
  | n+1, z => (∀ x, Integrable (fun s => Real.exp (z 0*
      finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (x,s)))) ν) ∧
        finiteCascadeFractionalIntegrable ν step H n (fun i => z i.succ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProductMarkLaw
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

def productMarkLaw {S T : Type} [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) : ProbabilityMeasure (S×T) :=
  ⟨(ν : Measure S).prod (ρ : Measure T),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def gaussianShiftStep (σ : ℕ → ℝ) (p : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  fun i => p.1 (i+1)+σ i*p.2

def standardGaussianMark : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def quadraticCascadePrecision (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => b
  | n+1, z => quadraticCascadePrecision σ b n (fun i => z i.succ)-z 0*(σ n)^2

def quadraticCascadeOffset (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeOffset σ b n (fun i => z i.succ)+
      (Real.log (quadraticCascadePrecision σ b n (fun i => z i.succ))-
        Real.log (quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

def canonicalGaussianFreeValue (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (r b : ℝ) : ℝ :=
  -Real.log b/2 + quadraticCascadeOffset σ b n z+r/(2*quadraticCascadePrecision σ b n z)

def cascadeLogFluctuationConstant (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  4*∫ η, (Real.log (cascadeTotal n η))^2 ∂cascadeLaw n z

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_PiMarkLaw
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

def piMarkLaw {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) : ProbabilityMeasure (ι → S) :=
  ⟨Measure.pi (fun i => (ν i : Measure S)),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def canonicalCoordinateStep (d : ℕ) (σ : ℕ → ℝ) :
    (Fin d → ℕ → ℝ)×(Fin d → ℝ) → (Fin d → ℕ → ℝ) :=
  fun p i => gaussianShiftStep σ (p.1 i,p.2 i)

def canonicalCoordinatePotential (d : ℕ) (b : ℝ) (x : Fin d → ℕ → ℝ) : ℝ :=
  ∑ i, (-Real.log b/2+(x i 0)^2/(2*b))

def canonicalCoordinateLog (d n : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (p : (Fin d → ℕ → ℝ)×DecoratedCascade (Fin d → ℝ) n) : ℝ :=
  Real.log (decoratedTerminalTotal (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) n p /
    decoratedTerminalTotal (canonicalCoordinateStep d σ) (fun _ => 0) n p)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGaussianQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def squareGaussianVariance : ℝ := variance (fun y : ℝ=>y^2) (gaussianReal 0 1)

def cavityQuadraticScalar (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) (y : Fin M→ℝ) : ℝ :=
  t*∑ i,a i*((y i)^2-r)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

def entropicMean (p : ℝ) (X : Ω → ℝ) : ℝ :=
  ∫ t : ℝ in (0:ℝ)..1, deriv (cgf X μ) (p*t)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianEntropic (p σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  entropicMean μ p (fun y => f (x+σ • y))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def logSphericalExp (n : ℕ) (R : ℝ) (x : Spin (n+1)) : ℝ :=
  Real.log (sphericalExp n x R)

lemma sphericalExp_le_mul (n : ℕ) (R : ℝ) (x y : Spin (n+1)) :
    sphericalExp n x R ≤ Real.exp (|R| *‖x-y‖)*sphericalExp n y R := by
  unfold sphericalExp
  rw [← integral_const_mul]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hu : ‖(u:Spin (n+1))‖=1 := by simp
  have hh := abs_real_inner_le_norm (x-y) (u:Spin (n+1))
  rw [hu,mul_one,inner_sub_left] at hh
  have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg R)
  rw [← abs_mul] at hm
  have hl := (le_abs_self (R*(inner ℝ x (u:Spin (n+1))-inner ℝ y (u:Spin (n+1))))).trans hm
  linarith

lemma logSphericalExp_lipschitz (n : ℕ) (R : ℝ) :
    LipschitzWith ⟨|R|,abs_nonneg R⟩ (logSphericalExp n R) := by
  have hle (x y : Spin (n+1)) : logSphericalExp n R x-logSphericalExp n R y ≤ |R| *‖x-y‖ := by
    have hx : 0 < sphericalExp n x R := lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n x R)
    have hy : 0 < sphericalExp n y R := lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n y R)
    have hh := Real.log_le_log hx (sphericalExp_le_mul n R x y)
    rw [Real.log_mul (Real.exp_pos _).ne' hy.ne',Real.log_exp] at hh
    change Real.log (sphericalExp n x R)-Real.log (sphericalExp n y R) ≤ _
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |logSphericalExp n R x-logSphericalExp n R y| ≤ |R| *‖x-y‖
  apply abs_le.mpr
  constructor
  · have hh := hle y x
    rw [norm_sub_rev] at hh
    linarith
  · exact hle x y

lemma integral_exp_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) (a : ℝ) : (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=
      Real.exp (a^2*‖v‖^2/2) := by
  have H := mgf_gaussianReal
    (IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)) a
  simp only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm,Real.coe_toNNReal (‖v‖^2) (sq_nonneg ‖v‖),zero_mul,zero_add] at H
  change (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=Real.exp (‖v‖^2*a^2/2) at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CavityGaussianFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def cavityQuadraticField (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (y : Fin M→Spin L) : ℝ :=
  t*∑ i,a i*((inner ℝ z (y i))^2-‖z‖^2)

def cavityLinearField (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (y : Fin M→Spin L) : ℝ :=
  t*∑ i,a i*inner ℝ z (y i)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def countableGaussianLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

instance instIsProbabilityMeasureForallNatRealCountableGaussianLaw : IsProbabilityMeasure countableGaussianLaw := by
  unfold countableGaussianLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianCoordinatePrefix (n : ℕ) (g : ℕ → ℝ) : Fin n → ℝ := fun i => g i.val

variable {S : Type*}

def gaussianPrefixField (v : ℕ → S → ℝ) (n : ℕ) (g : ℕ → ℝ) (x : S) : ℝ :=
  ∑ i : Fin n, g i.val*v i.val x

def countableGaussianField (v : ℕ → S → ℝ) (L : S → ℕ) (g : ℕ → ℝ) (x : S) : ℝ :=
  gaussianPrefixField v (L x) g x

lemma gaussianPrefixField_measurable [MeasurableSpace S] {v : ℕ → S → ℝ}
    (hv : ∀ i, Measurable (v i)) (n : ℕ) :
    Measurable (Function.uncurry (gaussianPrefixField v n)) := by
  unfold gaussianPrefixField Function.uncurry
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i.val).comp measurable_fst).mul ((hv i.val).comp measurable_snd)

lemma countableGaussianField_measurable [MeasurableSpace S] {v : ℕ → S → ℝ} {L : S → ℕ}
    (hv : ∀ i, Measurable (v i)) (hL : Measurable L) :
    Measurable (Function.uncurry (countableGaussianField v L)) := by
  have hm : Measurable (fun p : ℕ × ((ℕ → ℝ) × S) =>
      gaussianPrefixField v p.1 p.2.1 p.2.2) := by
    apply measurable_from_prod_countable_right
    intro n
    exact gaussianPrefixField_measurable hv n
  exact hm.comp ((hL.comp measurable_snd).prodMk measurable_id)

def maskedGaussianCoefficient (v : ℕ → S → ℝ) (L : S → ℕ) (i : ℕ) (x : S) : ℝ :=
  if i<L x then v i x else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianFieldAlgebra
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

def gaussianTailCoefficient (w : ℕ → S → ℝ) (n : ℕ) (i : ℕ) (x : S) : ℝ :=
  if n ≤ i then w i x else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

def decoratedLeafIntegral {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (F : X → ℝ≥0∞) :
    (n : ℕ) → X × DecoratedCascade S n → ℝ≥0∞
  | 0, p => F p.1
  | n+1, p => ∫⁻ q : ℝ × (S × DecoratedCascade S n),
      ENNReal.ofReal (Real.exp q.1) *
        decoratedLeafIntegral step F n (step (p.1,q.2.1),q.2.2)
          ∂markedStableCountKernel p.2

def decoratedFieldFactor {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (d : ℕ) (step : X × S → X) (field : X → Spin d) (k : ℕ)
    (p : X × DecoratedCascade S k) (x : Spin d) : ℝ≥0∞ :=
  decoratedLeafIntegral step (fun y => ENNReal.ofReal (Real.exp (inner ℝ (field y) x))) k p

def decoratedAngularFactor {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (field : X → Spin (n+1)) (k : ℕ)
    (p : X × DecoratedCascade S k) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Metric.sphere (0:Spin (n+1)) 1,
    decoratedFieldFactor (n+1) step field k p (r • (u:Spin (n+1))) ∂unitSphereLaw (n+1)

lemma canonicalRadialDensity_complete_square (n : ℕ) {b : ℝ} (hb : 0 < b)
    (z x : Spin (n+1)) :
    canonicalRadialDensity n b x * Real.exp (inner ℝ z x) =
      Real.exp (‖z‖^2/(2*b)) * canonicalRadialDensity n b (x - b⁻¹ • z) := by
  have he : -(b/2)*‖x‖^2 + inner ℝ z x = ‖z‖^2/(2*b) - (b/2)*‖x-b⁻¹ • z‖^2 := by
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hb),mul_pow,real_inner_comm x z]
    field_simp
    ring
  unfold canonicalRadialDensity
  calc
    _ = radialNormalizer n * Real.exp (-(b/2)*‖x‖^2 + inner ℝ z x) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he,Real.exp_sub,neg_mul,Real.exp_neg]; ring

lemma canonicalRadial_linear_integral (n : ℕ) {b : ℝ} (hb : 0 < b)
    (z : Spin (n+1)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ z x)) ∂canonicalRadialMass n b) =
      ENNReal.ofReal (Real.exp (-((n+1:ℕ):ℝ)*Real.log b/2 + ‖z‖^2/(2*b))) := by
  rw [canonicalRadialMass,lintegral_withDensity_eq_lintegral_mul _
    (canonicalRadialDensity_continuous n b).measurable.ennreal_ofReal (by fun_prop)]
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (canonicalRadialDensity_pos n b _).le,
    canonicalRadialDensity_complete_square n hb]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (canonicalRadialDensity n b x)) (b⁻¹ • z)]
  rw [← ofReal_integral_eq_lintegral_ofReal (canonicalRadialDensity_integrable n hb)
    (Eventually.of_forall fun x => (canonicalRadialDensity_pos n b x).le),
    canonicalRadialDensity_integral n hb,← ENNReal.ofReal_mul (Real.exp_pos _).le,
    Real.rpow_def_of_pos hb,← Real.exp_add]
  congr 2
  ring

def coordinateLeafField (d : ℕ) (x : Fin d → ℕ → ℝ) : Spin d :=
  WithLp.toLp 2 (fun i => x i 0)

def coordinateCascadeLaw (d k : ℕ) (z : Fin k → ℝ) (r : ℝ≥0) :
    Measure ((Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k) :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
    (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) k z)

instance coordinateCascadeLaw_probability (d k : ℕ) (z : Fin k → ℝ) (r : ℝ≥0) :
    IsProbabilityMeasure (coordinateCascadeLaw d k z r) := by
  unfold coordinateCascadeLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def coordinateAngularLog (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  Real.log ((decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p R).toReal /
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ShellBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def canonicalCoordinateBandTotalE (n k : ℕ) (σ : ℕ → ℝ) (b ε : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ≥0∞ :=
  ∫⁻ x in normSquareBand n ε,
    decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p x ∂canonicalRadialMass n b

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def normalizedCoordinateSphereLog (n k : ℕ) (σ : ℕ → ℝ)
    (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => p.1 i),p.2) / ((n+1:ℕ):ℝ)

def expectedCoordinateSphereLog (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ≥0) : ℝ :=
  ∫ p, normalizedCoordinateSphereLog n k σ p ∂coordinateCascadeLaw (n+1) k z r

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AmplitudeConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def coordinateRootScale (d k : ℕ) (r : ℝ)
    (p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k) :
    (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k := ((fun i => r*p.1 i),p.2)

def amplitudeSphereLog (n k : ℕ) (σ : ℕ → ℝ) (r : ℝ)
    (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => r*p.1 i),p.2)/(n+1:ℕ)

def amplitudeSphereValue (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ) : ℝ :=
  ∫ p, amplitudeSphereLog n k σ r p ∂coordinateCascadeLaw (n+1) k z 1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_partition_pos_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) : 0 < tiltPartition μ H t := by
  unfold tiltPartition
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi).mpr
  have he : Function.support (fun x => Real.exp (t*H x)) = univ := by
    ext x
    simp only [Function.mem_support,ne_eq,mem_univ]
    exact iff_of_true (Real.exp_pos _).ne' trivial
  rw [he,measure_univ]
  exact zero_lt_one

lemma tilt_law_probability_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) :
    IsProbabilityMeasure (tiltLaw μ H t) := by
  have hp := tilt_partition_pos_of_integrable μ hi
  constructor
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ .univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

lemma tilt_law_integral_of_integrable {H F : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) :
    (∫ x, F x ∂tiltLaw μ H t)=tiltMean μ H F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (hH.const_mul t).exp.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos_of_integrable μ hi).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianRotation
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

def gaussianVectorRotation (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  ((Real.cos t • ContinuousLinearMap.fst ℝ E E +
    Real.sin t • ContinuousLinearMap.snd ℝ E E).prod
    (-Real.sin t • ContinuousLinearMap.fst ℝ E E +
      Real.cos t • ContinuousLinearMap.snd ℝ E E))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_VectorPartition
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

def vectorPartition (W : S → ℝ) (V : S → StrongDual ℝ E) (x : E) : ℝ :=
  ∫ s, Real.exp (W s + V s x) ∂ρ

def vectorLogPartition (W : S → ℝ) (V : S → StrongDual ℝ E) (x : E) : ℝ :=
  Real.log (vectorPartition ρ W V x)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {S : Type*} [MeasurableSpace S]

def indexedFiniteCloud (a : ℕ × (ℕ → S)) : Measure S :=
  finitePointMeasure a.1 (fun i => a.2 i.val)

def indexedPoissonMeasure (a : ℕ → ℕ × (ℕ → S)) : Measure S :=
  Measure.sum (fun i => indexedFiniteCloud (a i))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedMarkedPoisson
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

@[reducible] def IndexedCascadeBase : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n))

@[reducible] def IndexedCascadeMarks (S : Type) [MeasurableSpace S] : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (ℕ → ℕ → S × IndexedCascadeMarks S n)

instance indexedCascadeBase_nonempty (n : ℕ) : Nonempty (IndexedCascadeBase n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => dsimp [IndexedCascadeBase]; infer_instance

instance indexedCascadeMarks_nonempty (S : Type) [MeasurableSpace S] [Nonempty S] (n : ℕ) :
    Nonempty (IndexedCascadeMarks S n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => dsimp [IndexedCascadeMarks]; infer_instance

def indexedCascadeBaseLaw : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (IndexedCascadeBase n)
  | 0,_ => ⟨Measure.dirac (),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  | n+1,z => ⟨Measure.infinitePi (fun i =>
      (poissonMeasure (((sfiniteSeq (stableLogIntensity (z 0)) i) univ).toNNReal)).prod
        (Measure.infinitePi (fun _ : ℕ =>
          (finiteIntensityMarks (sfiniteSeq (stableLogIntensity (z 0)) i)).prod
            (indexedCascadeBaseLaw n (fun j => z j.succ))))),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def indexedCascadeMarksLaw {S : Type} [MeasurableSpace S] (ν : ProbabilityMeasure S) :
    (n : ℕ) → ProbabilityMeasure (IndexedCascadeMarks S n)
  | 0 => ⟨Measure.dirac (),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  | n+1 => ⟨Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      (ν : Measure S).prod (indexedCascadeMarksLaw ν n))),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def indexedCascadeRealize {S : Type} [MeasurableSpace S] : (n : ℕ) →
    IndexedCascadeBase n × IndexedCascadeMarks S n → DecoratedCascade S n
  | 0,_ => ()
  | n+1,p => indexedPoissonMeasure (fun i => ((p.1 i).1,fun j =>
      (((p.1 i).2 j).1,((p.2 i j).1,
        indexedCascadeRealize n (((p.1 i).2 j).2,(p.2 i j).2)))))

instance countablePoissonIntensity_sfinite {A : Type*} [MeasurableSpace A]
    (r : ℕ → ℝ≥0) (ρ : ℕ → Measure A) [∀ i, IsProbabilityMeasure (ρ i)] :
    SFinite (countablePoissonIntensity r ρ) := by
  unfold countablePoissonIntensity
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedCascadeRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

def indexedCascadeRootMass {n : ℕ} (b : IndexedCascadeBase (n+1)) : ℝ≥0∞ :=
  markedStableTotalE (indexedPoissonMeasure b)

def IndexedCascadeGood : (n : ℕ) → IndexedCascadeBase n → Prop
  | 0,_ => True
  | n+1,b => 0 < (indexedCascadeRootMass b).toReal ∧
      ∀ i j : ℕ, IndexedCascadeGood n (((b i).2 j).2)

@[reducible] def IndexedLeaf : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (ℕ × ℕ × IndexedLeaf n)

instance indexedLeaf_countable (n : ℕ) : Countable (IndexedLeaf n) := by
  induction n with
  | zero => dsimp [IndexedLeaf]; infer_instance
  | succ n ih => dsimp [IndexedLeaf]; infer_instance

instance indexedLeaf_nonempty (n : ℕ) : Nonempty (IndexedLeaf n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => dsimp [IndexedLeaf]; infer_instance

instance indexedLeaf_measurableSingleton (n : ℕ) : MeasurableSingletonClass (IndexedLeaf n) := by
  induction n with
  | zero => dsimp [IndexedLeaf]; infer_instance
  | succ n ih => dsimp [IndexedLeaf]; infer_instance

def indexedLeafWeight : (n : ℕ) → IndexedCascadeBase n → IndexedLeaf n → ℝ≥0
  | 0,_,_ => 1
  | n+1,b,l => if l.2.1 < (b l.1).1 then
      (Real.exp (((b l.1).2 l.2.1).1)).toNNReal *
        indexedLeafWeight n (((b l.1).2 l.2.1).2) l.2.2 else 0

lemma indexedLeafWeight_measurable (n : ℕ) :
    Measurable (Function.uncurry (indexedLeafWeight n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_from_prod_countable_left
    intro l
    change Measurable (fun b : ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n) =>
      if l.2.1 < (b l.1).1 then (Real.exp (((b l.1).2 l.2.1).1)).toNNReal *
        indexedLeafWeight n (((b l.1).2 l.2.1).2) l.2.2 else 0)
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    · exact (by fun_prop : Measurable (fun b : ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n) =>
          (Real.exp (((b l.1).2 l.2.1).1)).toNNReal)).mul
        (ih.comp (show Measurable (fun b : ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n) =>
          ((((b l.1).2 l.2.1).2),l.2.2)) from by fun_prop))
    · exact measurable_const

def indexedLeafMeasure (n : ℕ) (b : IndexedCascadeBase n) : Measure (IndexedLeaf n) :=
  Measure.sum (fun l => (indexedLeafWeight n b l : ℝ≥0∞) • Measure.dirac l)

instance indexedLeafMeasure_sfinite (n : ℕ) (b : IndexedCascadeBase n) :
    SFinite (indexedLeafMeasure n b) := by
  unfold indexedLeafMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma indexedLeafMeasure_measurable (n : ℕ) : Measurable (indexedLeafMeasure n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [indexedLeafMeasure,Measure.sum_apply _ hs,Measure.smul_apply]
  apply Measurable.tsum
  intro l
  exact (((indexedLeafWeight_measurable n).comp (measurable_id.prodMk measurable_const)).coe_nnreal_ennreal).mul_const _

def indexedLeafState {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) : (n : ℕ) → X × IndexedCascadeMarks S n → IndexedLeaf n → X
  | 0,p,_ => p.1
  | n+1,p,l => indexedLeafState step n (step (p.1,(p.2 l.1 l.2.1).1),
      (p.2 l.1 l.2.1).2) l.2.2

lemma indexedLeafState_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    {step : X × S → X} (hs : Measurable step) (n : ℕ) :
    Measurable (Function.uncurry (indexedLeafState step n)) := by
  induction n with
  | zero => exact measurable_fst.fst
  | succ n ih =>
    apply measurable_from_prod_countable_left
    intro l
    change Measurable (fun p : X × (ℕ → ℕ → S × IndexedCascadeMarks S n) =>
      indexedLeafState step n (step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2) l.2.2)
    exact ih.comp (show Measurable (fun p : X × (ℕ → ℕ → S × IndexedCascadeMarks S n) =>
      ((step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2),l.2.2)) from by fun_prop)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

@[reducible] def IndexedVertex : ℕ → Type
  | 0 => Empty
  | n+1 => ℕ × ℕ × (Unit ⊕ IndexedVertex n)

instance indexedVertex_countable (n : ℕ) : Countable (IndexedVertex n) := by
  induction n with
  | zero => dsimp [IndexedVertex]; infer_instance
  | succ n ih => dsimp [IndexedVertex]; infer_instance

def indexedMarksFromVertices {S : Type} [MeasurableSpace S] : (n : ℕ) →
    (IndexedVertex n → S) → IndexedCascadeMarks S n
  | 0,_ => ()
  | n+1,f => fun i j => (f (i,j,.inl ()),
      indexedMarksFromVertices n (fun v => f (i,j,.inr v)))

def indexedLeafVertex : (n : ℕ) → IndexedLeaf n → Fin n → IndexedVertex n
  | 0,_,i => i.elim0
  | n+1,l,i => Fin.cases (l.1,l.2.1,Sum.inl ())
      (fun j => (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 j))) i

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianMarkRecursion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianLinearEntropic (b : ℝ) (A : E →L[ℝ] E) (f : E → ℝ) (x : E) : ℝ :=
  entropicMean μ b (fun y => f (x+A y))

def gaussianLinearBackward : List (ℝ×(E →L[ℝ] E)) → (E → ℝ) → E → ℝ
  | [],f => f
  | (b,A)::l,f => gaussianLinearEntropic μ b A (gaussianLinearBackward l f)

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

def gaussianLinearMarkStep (A : ℕ → E →L[ℝ] E) : (ℕ → E)×E → ℕ → E :=
  fun p j => p.1 (j+1)+A j p.2

def linearCascadeWord (A : ℕ → E →L[ℝ] E) : (k : ℕ) → (Fin k → ℝ) → List (ℝ×(E →L[ℝ] E))
  | 0,_ => []
  | k+1,z => (z 0,A k)::linearCascadeWord A k (fun i => z i.succ)

end
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianMarkLaw : ProbabilityMeasure E := ⟨stdGaussian E,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def gaussianLinearCascadeLog (A : ℕ → E →L[ℝ] E) (R : E →L[ℝ] E)
    (f : E → ℝ) (k : ℕ) (a : E×DecoratedCascade E k) : ℝ :=
  Real.log (decoratedTerminalTotal (gaussianLinearMarkStep A) (fun x => f (x 0)) k
      ((fun _ => R a.1),a.2) /
    decoratedTerminalTotal (gaussianLinearMarkStep A) (fun _ => 0) k ((fun _ => R a.1),a.2))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

def countableCoordinate {ι : Type*} [Countable ι] (i : ι) : ℕ :=
  @Encodable.encode ι (Encodable.ofCountable ι) i

section
variable {V I : Type} [Countable V] [Fintype I]

def countableGaussianVectors (g : ℕ → ℝ) (v : V) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => g (countableCoordinate (v,i)))

end

abbrev SharedVertex (n : ℕ) := Unit ⊕ IndexedVertex n

def indexedGaussianDisorder (n : ℕ) (I : Type) [Fintype I] (g : ℕ → ℝ) :
    EuclideanSpace ℝ I × IndexedCascadeMarks (EuclideanSpace ℝ I) n :=
  (countableGaussianVectors (V := SharedVertex n) (I := I) g (Sum.inl ()),
    indexedMarksFromVertices n (fun v => countableGaussianVectors (V := SharedVertex n) (I := I) g (Sum.inr v)))

def indexedLeafSharedVertex (n : ℕ) (l : IndexedLeaf n) : Fin (n+1) → SharedVertex n :=
  Fin.cases (Sum.inl ()) (fun i => Sum.inr (indexedLeafVertex n l i))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

def finiteGaussianRow (key : K → ℕ) (a : K → ℝ) (i : ℕ) : ℝ :=
  ∑ k, if key k = i then a k else 0

def finiteGaussianRowLength (key : K → ℕ) : ℕ :=
  Finset.univ.sup key + 1

end
variable {I : Type} [Fintype I]

def indexedGaussianRowKey (n : ℕ) (l : IndexedLeaf n) (p : Fin (n+1)×I) : ℕ :=
  countableCoordinate (indexedLeafSharedVertex n l p.1,p.2)

variable {S : Type} [MeasurableSpace S]

def indexedGaussianRow (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (i : ℕ) (x : S×IndexedLeaf n) : ℝ :=
  finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i

def indexedGaussianRowLength (n : ℕ) (x : S×IndexedLeaf n) : ℕ :=
  finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)

lemma indexedGaussianRow_measurable (n : ℕ) (B : Fin (n+1) → I → ℝ)
    {V : S → EuclideanSpace ℝ I} (hV : Measurable V) (i : ℕ) :
    Measurable (indexedGaussianRow n B V i) := by
  apply measurable_from_prod_countable_left
  intro l
  unfold indexedGaussianRow finiteGaussianRow
  apply Finset.measurable_sum
  intro p hp
  by_cases hp : indexedGaussianRowKey n l p = i
  · simp only [ite_eq_left hp]
    fun_prop
  · simp only [ite_eq_right hp]
    exact measurable_const

lemma indexedGaussianRowLength_measurable (n : ℕ) :
    Measurable (indexedGaussianRowLength (S := S) (I := I) n) :=
  (measurable_of_countable (fun l : IndexedLeaf n =>
    finiteGaussianRowLength (indexedGaussianRowKey (I := I) n l))).comp measurable_snd

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TensorFeatures
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSpinHAddNatOfNatSphereLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

abbrev NormalizedSpin (N : ℕ) := Metric.sphere (0 : Spin N) 1
abbrev SpinTensorIndex (N p : ℕ) := Fin p → Fin N

def spinTensorFeature (N p : ℕ) (x : NormalizedSpin N) :
    EuclideanSpace ℝ (SpinTensorIndex N p) :=
  WithLp.toLp 2 (fun i => ∏ j, x.val (i j))

def spinOverlap {N : ℕ} (x y : NormalizedSpin N) : ℝ := inner ℝ x.val y.val

lemma spinTensorFeature_continuous (N p : ℕ) : Continuous (spinTensorFeature N p) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact continuous_finsetProd _ fun j _ =>
    (EuclideanSpace.proj (i j)).continuous.comp continuous_subtype_val

lemma spinTensorFeature_inner (N p : ℕ) (x y : NormalizedSpin N) :
    inner ℝ (spinTensorFeature N p x) (spinTensorFeature N p y) =
      spinOverlap x y ^ p := by
  change (∑ i : SpinTensorIndex N p, (∏ j, y.val (i j)) * (∏ j, x.val (i j))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (i : Fin N) => y.val i*x.val i)]
  change (∏ _ : Fin p, spinOverlap x y) = spinOverlap x y ^ p
  simp

lemma spinOverlap_abs_le {N : ℕ} (x y : NormalizedSpin N) : |spinOverlap x y| ≤ 1 := by
  have hx : ‖x.val‖=1 := by simp
  have hy : ‖y.val‖=1 := by simp
  simpa [spinOverlap,hx,hy] using abs_real_inner_le_norm x.val y.val

abbrev EnrichedIndex (N J : ℕ) (p : Fin J → ℕ) :=
  Fin N ⊕ (j : Fin J) × SpinTensorIndex N (p j)
abbrev EnrichedMark (N J : ℕ) (p : Fin J → ℕ) := EuclideanSpace ℝ (EnrichedIndex N J p)

def enrichedFeature (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x : NormalizedSpin N) : EnrichedMark N J p :=
  WithLp.toLp 2 fun i => match i with
    | .inl i => a*x.val i
    | .inr ⟨j,t⟩ => c j*spinTensorFeature N (p j) x t

lemma enrichedFeature_continuous (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ) :
    Continuous (enrichedFeature N J p a c) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact continuous_const.mul ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)
  | inr i => exact continuous_const.mul ((EuclideanSpace.proj i.2).continuous.comp
      (spinTensorFeature_continuous N (p i.1)))

lemma enrichedFeature_inner (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x y : NormalizedSpin N) :
    inner ℝ (enrichedFeature N J p a c x) (enrichedFeature N J p a c y)=
      a^2*spinOverlap x y+∑ j, (c j)^2*spinOverlap x y^(p j) := by
  change (∑ i : EnrichedIndex N J p,
    (enrichedFeature N J p a c y i)*(enrichedFeature N J p a c x i)) = _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedFeature]
  have hlin : (∑ i : Fin N, a*y.val i*(a*x.val i))=a^2*spinOverlap x y := by
    change (∑ i : Fin N, a*y.val i*(a*x.val i)) = a^2*(∑ i : Fin N, y.val i*x.val i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hlin]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← spinTensorFeature_inner N (p j) x y]
  change (∑ i, c j*spinTensorFeature N (p j) y i*(c j*spinTensorFeature N (p j) x i))=
    (c j)^2*(∑ i, spinTensorFeature N (p j) y i*spinTensorFeature N (p j) x i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma enrichedFeature_norm_sq (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x : NormalizedSpin N) :
    ‖enrichedFeature N J p a c x‖^2=a^2+∑ j, (c j)^2 := by
  rw [← real_inner_self_eq_norm_sq,enrichedFeature_inner]
  have hx : spinOverlap x x=1 := by
    have h : ‖x.val‖=1 := by simp
    simp [spinOverlap,h]
  simp [hx]

lemma enrichedFeature_norm (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x : NormalizedSpin N) :
    ‖enrichedFeature N J p a c x‖=Real.sqrt (a^2+∑ j, (c j)^2) := by
  rw [← enrichedFeature_norm_sq N J p a c x,Real.sqrt_sq (norm_nonneg _)]

def perturbationScale (N : ℕ) : ℝ := (N:ℝ)^(-(1:ℝ)/16)

def perturbationAmplitude (N : ℕ) (u : Fin N → ℝ) (j : Fin N) : ℝ :=
  Real.sqrt (N:ℝ)*perturbationScale N*(2:ℝ)^(-((j.val+1:ℕ):ℤ))*u j

def sourceEnrichedFeature (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ) :
    NormalizedSpin N → EnrichedMark N N p :=
  enrichedFeature N N p (Real.sqrt (N:ℝ)) (perturbationAmplitude N u)

variable {I : Type} [Fintype I]

def diagonalMarkLinear (c : I → ℝ) : EuclideanSpace ℝ I →ₗ[ℝ] EuclideanSpace ℝ I where
  toFun x := WithLp.toLp 2 fun i => c i*x i
  map_add' x y := by ext i; change c i*(x i+y i)=c i*x i+c i*y i; ring
  map_smul' r x := by ext i; change c i*(r*x i)=r*(c i*x i); ring

def diagonalMark (c : I → ℝ) : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I :=
  (diagonalMarkLinear c).toContinuousLinearMap

@[simp] lemma diagonalMark_apply (c : I → ℝ) (x : EuclideanSpace ℝ I) (i : I) :
    diagonalMark c x i=c i*x i := rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedDiagonalField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

def hierarchyRowCoefficients (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ) : Fin (n+1) → I → ℝ :=
  Fin.cases root (fun d => step (n-1-d.val))

end

def normalizedPatternEnergy (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (x : NormalizedSpin N) : ℝ :=
  ∑ a, f (∑ i, g a i*x.val i)

lemma normalizedPatternEnergy_continuous (N M : ℕ) (f : ℝ →ᵇ ℝ) :
    Continuous (fun p : (Fin M → Fin N → ℝ) × NormalizedSpin N =>
      normalizedPatternEnergy N M f p.1 p.2) := by
  unfold normalizedPatternEnergy
  fun_prop

lemma normalizedPatternEnergy_bound (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N M f g x| ≤ (M:ℝ)*‖f‖ := by
  unfold normalizedPatternEnergy
  calc
    _ ≤ ∑ a : Fin M, |f (∑ i, g a i*x.val i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin M, ‖f‖ := Finset.sum_le_sum (fun _ _ => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm _)
    _ = _ := by simp

def enrichedTerminal (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) (a : EnrichedMark (n+1) (n+1) p) : ℝ :=
  vectorLogPartition (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f g)
    (fun x => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) a - (n+1:ℕ)*htop

def enrichedFeatureBound (N : ℕ) (u : Fin N → ℝ) : ℝ≥0 :=
  ⟨Real.sqrt ((N:ℝ)+∑ j, perturbationAmplitude N u j^2),Real.sqrt_nonneg _⟩

def enrichedCoordinateLevel {N k : ℕ} (p d : Fin N → ℕ)
    (h : Fin (k+1) → ℝ) (l : Fin (k+1)) (i : EnrichedIndex N N p) : ℝ :=
  match i with
  | .inl _ => 2*h l
  | .inr ⟨j,_⟩ => ((l.val:ℝ)/(k+1:ℕ))^(d j)

def enrichedRootMap {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) :
    EnrichedMark N N p →L[ℝ] EnrichedMark N N p :=
  diagonalMark (fun i => Real.sqrt (enrichedCoordinateLevel p d h 0 i))

def enrichedIncrementMap {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (j : ℕ) : EnrichedMark N N p →L[ℝ] EnrichedMark N N p :=
  if hj : j<k then diagonalMark (fun i => Real.sqrt
    (enrichedCoordinateLevel p d h ⟨k-j,by omega⟩ i-
     enrichedCoordinateLevel p d h ⟨k-j-1,by omega⟩ i)) else 0

def enrichedCascadeLog (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (h : Fin (k+1) → ℝ)
    (a : EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k) : ℝ :=
  let step := gaussianLinearMarkStep (enrichedIncrementMap p d h)
  let H := fun x => enrichedTerminal n M f g p u (h (Fin.last k)) (x 0)
  let x := fun _ => enrichedRootMap p d h a.1
  Real.log (decoratedTerminalTotal step H k (x,a.2)/
    decoratedTerminalTotal step (fun _ => 0) k (x,a.2))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedLeafTotal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

def indexedLeafProbability (n : ℕ) (b : IndexedCascadeBase n) : Measure (IndexedLeaf n) :=
  if 0 < ((indexedLeafMeasure n b) univ).toReal then
    ((indexedLeafMeasure n b) univ)⁻¹ • indexedLeafMeasure n b
  else Measure.dirac (Classical.choice (indexedLeaf_nonempty n))

instance indexedLeafProbability_isProbability (n : ℕ) (b : IndexedCascadeBase n) :
    IsProbabilityMeasure (indexedLeafProbability n b) := by
  constructor
  by_cases h : 0 < ((indexedLeafMeasure n b) univ).toReal
  · rw [indexedLeafProbability,ite_eq_left h,Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.toReal_pos_iff.mp h).1.ne'
      (ENNReal.toReal_pos_iff.mp h).2.ne
  · simp [indexedLeafProbability,h]

lemma indexedLeafProbability_measurable (n : ℕ) : Measurable (indexedLeafProbability n) := by
  have hm := indexedLeafMeasure_measurable n
  have ht : Measurable (fun b => (indexedLeafMeasure n b) univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp hm
  apply Measurable.ite (measurableSet_lt measurable_const ht.ennreal_toReal)
  · apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ht.inv.mul ((Measure.measurable_coe hs).comp hm)
  · exact measurable_const

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

def profileGaussianRoot {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) (i : I) : ℝ :=
  Real.sqrt (q 0 i)

def profileGaussianStep {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (j : ℕ) (i : I) : ℝ :=
  if hj : j<k then Real.sqrt (q ⟨k-j,by omega⟩ i-q ⟨k-j-1,by omega⟩ i) else 0

def sourceGaussianRow {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (u : Fin N → ℝ) :
    ℕ → NormalizedSpin N × IndexedLeaf k → ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k
    (profileGaussianRoot (enrichedCoordinateLevel p d h))
    (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceEnrichedFeature N p u)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBoltzmann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {S : Type*} [MeasurableSpace S]

def countableGaussianHamiltonian (W : S → ℝ) (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (x : S) : ℝ := W x+countableGaussianField v L g x

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def enrichedIndexedBaseMeasure (n k : ℕ) (b : IndexedCascadeBase k) :
    Measure (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (unitSphereLaw (n+1)).prod (indexedLeafProbability k b)

instance enrichedIndexedBaseMeasure_probability (n k : ℕ) (b : IndexedCascadeBase k) :
    IsProbabilityMeasure (enrichedIndexedBaseMeasure n k b) := by
  unfold enrichedIndexedBaseMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def enrichedIndexedBoundedEnergy (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (x : NormalizedSpin (n+1) × IndexedLeaf k) : ℝ :=
  normalizedPatternEnergy (n+1) M f a x.1-(n+1:ℕ)*h (Fin.last k)

def enrichedIndexedHamiltonian (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (g : ℕ → ℝ) :
    NormalizedSpin (n+1) × IndexedLeaf k → ℝ :=
  countableGaussianHamiltonian (enrichedIndexedBoundedEnergy n M k f a h)
    (sourceGaussianRow p d h u) (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) g

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

def indexedVertexDepth : (n : ℕ) → IndexedVertex n → Fin n
  | 0,v => v.elim
  | n+1,v => match v.2.2 with
    | .inl _ => 0
    | .inr w => (indexedVertexDepth n w).succ

def indexedSharedVertexDepth (n : ℕ) : SharedVertex n → Fin (n+1)
  | .inl _ => 0
  | .inr v => (indexedVertexDepth n v).succ

def indexedCommonDepth : (n : ℕ) → IndexedLeaf n → IndexedLeaf n → Fin (n+1)
  | 0,_,_ => 0
  | n+1,l,m => if l.1=m.1 ∧ l.2.1=m.2.1 then (indexedCommonDepth n l.2.2 m.2.2).succ else 0

variable {S : Type*} [MeasurableSpace S]

def gaussianPrefixCovariance (v w : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ) (x y : S) : ℝ :=
  ∑ i : Fin n, maskedGaussianCoefficient w L i.val x*maskedGaussianCoefficient v L i.val y

def countableGaussianCovariance (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) : ℝ :=
  gaussianPrefixCovariance v w L (L x) x y

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GibbsReplicaMean
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
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def gibbsReplicaMean (H : S → ℝ) (n : ℕ) (G : (Fin n → S) → ℝ) : ℝ :=
  tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) G 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LocalMaxSecondDerivNonpos
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

section

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

def affineLogRoot (H Y : S → ℝ) (t : ℝ) : ℝ :=
  Real.log (tiltPartition μ (fun x => H x+t*Y x) 1)

end

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]

def thermalVar (H Y : S → ℝ) (t : ℝ) : ℝ :=
  tiltMean μ (fun x => H x+t*Y x) (fun x => Y x*Y x) 1 -
    (tiltMean μ (fun x => H x+t*Y x) Y 1)^2

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UnboundedContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsSFiniteKernel κ] {H Y : A → S → ℝ}
variable (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))

include hH

lemma kernel_tiltPartition_measurable : Measurable (fun a => tiltPartition (κ a) (H a) 1) := by
  unfold tiltPartition
  exact (hH.const_mul 1 |>.exp.stronglyMeasurable.integral_kernel_prod_right).measurable

include hY

lemma kernel_tiltMean_measurable : Measurable (fun a => tiltMean (κ a) (H a) (Y a) 1) := by
  unfold tiltMean tiltIntegral
  exact ((hH.const_mul 1 |>.exp.mul hY).stronglyMeasurable.integral_kernel_prod_right).measurable.div
    (kernel_tiltPartition_measurable κ hH)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelReplicaGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernelReplica_measurable (n : ℕ) :
    Measurable (fun a => Measure.pi (fun _ : Fin n => κ a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi
  rintro _ ⟨s,hs,rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => κ.measurable_coe (hs i (mem_univ i))

def kernelReplica (n : ℕ) : Kernel A (Fin n → S) :=
  ⟨(fun a => Measure.pi (fun _ : Fin n => κ a)),kernelReplica_measurable κ n⟩

instance instIsMarkovKernelForallFinKernelReplica (n : ℕ) : IsMarkovKernel (kernelReplica κ n) := ⟨fun _ => by
  change IsProbabilityMeasure (Measure.pi _)
  infer_instance⟩

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def enrichedDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    Measure (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k) :=
  (stdGaussian (EnrichedMark (n+1) (n+1) p)).prod
    (decoratedCascadeLaw (gaussianMarkLaw : ProbabilityMeasure (EnrichedMark (n+1) (n+1) p)) k z)

instance instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    IsProbabilityMeasure (enrichedDisorderLaw n k p z) := by
  unfold enrichedDisorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_EnrichedPatternMean
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def enrichedExpectedLog (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (g : Fin M → Fin (n+1) → ℝ) : ℝ :=
  ∫ a, enrichedCascadeLog n M k f g p d u h a ∂enrichedDisorderLaw n k p z

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_EnrichedPatternVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def finitePatternRowsLaw (N M : ℕ) : Measure (Fin M → Fin N → ℝ) :=
  Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1

instance instIsProbabilityMeasureForallFinForallRealFinitePatternRowsLaw (N M : ℕ) : IsProbabilityMeasure (finitePatternRowsLaw N M) := by
  unfold finitePatternRowsLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def enrichedFixedCountLog (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (a : (Fin M → Fin (n+1) → ℝ) ×
        (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k)) : ℝ :=
  enrichedCascadeLog n M k f a.1 p d u h a.2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_EnrichedPoissonVariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def infinitePatternRowsLaw (N : ℕ) : Measure (ℕ → Fin N → ℝ) :=
  Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => gaussianReal 0 1

instance instIsProbabilityMeasureForallNatForallFinRealInfinitePatternRowsLaw (N : ℕ) : IsProbabilityMeasure (infinitePatternRowsLaw N) := by
  unfold infinitePatternRowsLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def patternPrefix (N M : ℕ) (g : ℕ → Fin N → ℝ) : Fin M → Fin N → ℝ :=
  fun a => g a.val

def enrichedPoissonLog (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (a : ℕ × ((ℕ → Fin (n+1) → ℝ) ×
      (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k))) : ℝ :=
  enrichedCascadeLog n a.1 k f (patternPrefix (n+1) a.1 a.2.1) p d u h a.2.2

def enrichedRowsDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :=
  (infinitePatternRowsLaw (n+1)).prod (enrichedDisorderLaw n k p z)

instance instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) :
    IsProbabilityMeasure (enrichedRowsDisorderLaw n k p z) := by
  unfold enrichedRowsDisorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedVarianceBound
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def enrichedRandomPressure (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) :=
  fun a => (1/(n+1:ℕ))*enrichedPoissonLog n k f p d u h a

def enrichedPoissonDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :=
  (poissonMeasure ((n+1:ℕ)*t)).prod (enrichedRowsDisorderLaw n k p z)

instance instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw (n k : ℕ) (p : Fin (n+1) → ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (enrichedPoissonDisorderLaw n k p z t) := by
  unfold enrichedPoissonDisorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def enrichedVarianceConstant (k : ℕ) (z : Fin k → ℝ) (f : ℝ →ᵇ ℝ) (H T : ℝ) : ℝ :=
  max (cascadeLogFluctuationConstant k z) 0+(Real.pi^2/8)*5*(2*H+1)+
    5*T*‖f‖^2+‖f‖^2

abbrev SourceIndexedDisorder (n k : ℕ) :=
  ℕ × ((ℕ → Fin (n+1) → ℝ) × (IndexedCascadeBase k × (ℕ → ℝ)))

def sourceIndexedDisorderLaw (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    Measure (SourceIndexedDisorder n k) :=
  (poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
    ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw))

instance instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (sourceIndexedDisorderLaw n k z t) := by
  unfold sourceIndexedDisorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

abbrev SourceBaseData (n k : ℕ) := ℕ × ((ℕ → Fin (n+1) → ℝ) × IndexedCascadeBase k)

def sourceBaseDataLaw (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) : Measure (SourceBaseData n k) :=
  (poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
    (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)))

instance instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw (n k : ℕ) (z : Fin k → ℝ) (t : ℝ≥0) : IsProbabilityMeasure (sourceBaseDataLaw n k z t) := by
  unfold sourceBaseDataLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def indexedLeafKernel (k : ℕ) : Kernel (IndexedCascadeBase k) (IndexedLeaf k) :=
  ⟨indexedLeafProbability k,indexedLeafProbability_measurable k⟩

instance instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel (k : ℕ) : IsMarkovKernel (indexedLeafKernel k) := ⟨fun b => indexedLeafProbability_isProbability k b⟩

def sourceSpinLeafKernel (n k : ℕ) : Kernel (SourceBaseData n k) (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (Kernel.const _ (unitSphereLaw (n+1))).prod
    ((indexedLeafKernel k).comap
      (fun a : SourceBaseData n k => a.2.2) (by fun_prop))

lemma sourceSpinLeafKernel_apply (n k : ℕ) (a : SourceBaseData n k) :
    sourceSpinLeafKernel n k a = enrichedIndexedBaseMeasure n k a.2.2 := by
  rw [sourceSpinLeafKernel,Kernel.prod_apply]
  rfl

instance instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel (n k : ℕ) : IsMarkovKernel (sourceSpinLeafKernel n k) := by
  constructor
  intro a
  rw [sourceSpinLeafKernel_apply]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Contact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev sourceFullSpinLeafKernel (n k : ℕ) : Kernel (SourceBaseData n k × (ℕ → ℝ))
    (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (sourceSpinLeafKernel n k).comap Prod.fst measurable_fst

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantitativeGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) (P : Measure A) (H : A → S → ℝ)

def kernelGGDefect (C : S → S → ℝ) (diag : ℝ) (r : ℕ) (i : Fin r)
    (G : (Fin r → S) → ℝ) : ℝ :=
  (∫ a, gibbsReplicaMean (κ a) (H a) r (fun x => G x*∑ l, C (x i) (x l)) ∂P)-
    diag*(∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P)+
    (∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P)*
      (∫ a, gibbsReplicaMean (κ a) (H a) 2 (fun x => C (x 1) (x 0)) ∂P)-
    r*(∫ a, gibbsReplicaMean (κ a) (H a) (r+1)
      (fun x => G (fun l => x l.succ)*C (x i.succ) (x 0)) ∂P)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ContactGGRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

def gibbsKernelDensity (a : A) (x : S) : ℝ≥0∞ :=
  if Integrable (fun y => Real.exp (H a y)) (κ a) then
    (ENNReal.ofReal (tiltPartition (κ a) (H a) 1))⁻¹*ENNReal.ofReal (Real.exp (H a x)) else 1

lemma gibbsKernelDensity_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (gibbsKernelDensity κ H)) := by
  apply Measurable.ite
  · exact (measurableSet_kernel_integrable (κ := κ) (f := fun a x => Real.exp (H a x)) hH.exp.stronglyMeasurable).preimage measurable_fst
  · exact (((kernel_tiltPartition_measurable κ hH).ennreal_ofReal.inv).comp measurable_fst).mul hH.exp.ennreal_ofReal
  · exact measurable_const

def gibbsProbabilityKernel : Kernel A S := Kernel.withDensity κ (gibbsKernelDensity κ H)

lemma gibbsProbabilityKernel_of_integrable (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) :
    gibbsProbabilityKernel κ H a = tiltLaw (κ a) (H a) 1 := by
  rw [gibbsProbabilityKernel,Kernel.withDensity_apply _ (gibbsKernelDensity_measurable κ H hH)]
  change (κ a).withDensity (fun x => if Integrable (fun y => Real.exp (H a y)) (κ a)
    then (ENNReal.ofReal (tiltPartition (κ a) (H a) 1))⁻¹*ENNReal.ofReal (Real.exp (H a x)) else 1) = _
  simp only [ite_eq_left hi,tiltLaw,one_mul]
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (H a x))) := hH.of_uncurry_left.exp.ennreal_ofReal
  exact withDensity_smul _ hm

lemma gibbsProbabilityKernel_of_not_integrable (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : ¬Integrable (fun x => Real.exp (H a x)) (κ a)) :
    gibbsProbabilityKernel κ H a = κ a := by
  rw [gibbsProbabilityKernel,Kernel.withDensity_apply _ (gibbsKernelDensity_measurable κ H hH)]
  change (κ a).withDensity (fun x => if Integrable (fun y => Real.exp (H a y)) (κ a)
    then (ENNReal.ofReal (tiltPartition (κ a) (H a) 1))⁻¹*ENNReal.ofReal (Real.exp (H a x)) else 1) = _
  simp only [ite_eq_right hi]
  exact withDensity_one

lemma gibbsProbabilityKernel_markov (hH : Measurable (Function.uncurry H)) :
    IsMarkovKernel (gibbsProbabilityKernel κ H) := by
  constructor
  intro a
  by_cases hi : Integrable (fun x => Real.exp (H a x)) (κ a)
  · rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
    exact tilt_law_probability_of_integrable (κ a) (by simpa only [one_mul] using hi)
  · rw [gibbsProbabilityKernel_of_not_integrable κ H hH a hi]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernelFiniteProduct_measurable (ι : Type*) [Fintype ι] :
    Measurable (fun a => Measure.pi (fun _ : ι => κ a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi
  rintro _ ⟨s,hs,rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => κ.measurable_coe (hs i (mem_univ i))

lemma kernelInfiniteReplica_measurable (ι : Type*) :
    Measurable (fun a => Measure.infinitePi (fun _ : ι => κ a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  intro s hs
  obtain ⟨I,E,hE,rfl⟩ := (mem_measurableCylinders s).mp hs
  have hm := (Measure.measurable_coe hE).comp (kernelFiniteProduct_measurable κ I)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  change (Measure.infinitePi (fun _ : ι => κ a)) (I.restrict ⁻¹' E) =
    (Measure.pi (fun _ : I => κ a)) E
  have hmI : Measurable (I.restrict : (ι → S) → I → S) := by fun_prop
  rw [← Measure.map_apply (f := I.restrict) hmI hE,Measure.infinitePi_map_restrict]

def kernelInfiniteReplica (ι : Type*) : Kernel A (ι → S) :=
  ⟨(fun a => Measure.infinitePi (fun _ : ι => κ a)),kernelInfiniteReplica_measurable κ ι⟩

instance instIsMarkovKernelForallKernelInfiniteReplica (ι : Type*) : IsMarkovKernel (kernelInfiniteReplica κ ι) := ⟨fun _ => by
  change IsProbabilityMeasure (Measure.infinitePi _)
  infer_instance⟩

end
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))

def annealedInfiniteReplicaMeasure : Measure (A × (ℕ → S)) := by
  letI : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  exact P ⊗ₘ kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ

instance instIsProbabilityMeasureProdForallNatAnnealedInfiniteReplicaMeasure : IsProbabilityMeasure (annealedInfiniteReplicaMeasure κ P H hH) := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  unfold annealedInfiniteReplicaMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma isClosed_matrix_posSemidef (r : ℕ) : IsClosed {M : Matrix (Fin r) (Fin r) ℝ | M.PosSemidef} := by
  have he : {M : Matrix (Fin r) (Fin r) ℝ | M.PosSemidef} =
      {M : Matrix (Fin r) (Fin r) ℝ | ∀ i j, M j i=M i j} ∩ ⋂ x : Fin r → ℝ, {M : Matrix (Fin r) (Fin r) ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [mem_ofPred_eq,mem_inter_iff,mem_iInter,Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.IsHermitian.ext_iff,star_trivial]
  rw [he]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (by
      unfold dotProduct Matrix.mulVec
      fun_prop)

def compactRelabel {K : Type*} (e : Equiv.Perm ℕ) (Q : CompactArray K) : CompactArray K :=
  fun i j => Q (e i) (e j)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapBlock
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

abbrev OverlapBlock (n : ℕ) := Fin n → Fin n → ℝ

def overlapBlock (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (ω : Ω) : OverlapBlock n :=
  fun i j => R ω i j

def GhirlandaGuerra (μ : Measure Ω) (R : Ω → ℕ → ℕ → ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n) (s : Set (OverlapBlock n)), MeasurableSet s →
    ∀ t : Set ℝ, MeasurableSet t →
    μ.real ((overlapBlock R n) ⁻¹' s ∩ {ω | R ω i n ∈ t}) =
      μ.real ((overlapBlock R n) ⁻¹' s) * μ.real {ω | R ω 0 1 ∈ t} / n +
      (∑ j ∈ (Finset.univ.erase i),
        μ.real ((overlapBlock R n) ⁻¹' s ∩ {ω | R ω i j ∈ t})) / n

end Positivity

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev OverlapArray := ℕ → ℕ → ℝ
def relabelArray (π : Equiv.Perm ℕ) (Q : OverlapArray) : OverlapArray :=
  fun i j => Q (π i) (π j)

def OverlapSwapInvariant (μ : Measure OverlapArray) : Prop :=
  ∀ i j : ℕ, MeasurePreserving (relabelArray (Equiv.swap i j)) μ μ

def copyIndex (r j : ℕ) (i : Fin (r + 1)) : ℕ := if i.val = r then j else i.val

def copyBlock (r j : ℕ) (Q : OverlapArray) : OverlapBlock (r + 1) :=
  fun a b => Q (copyIndex r j a) (copyIndex r j b)

def copyEvent (r : ℕ) (s : Set (OverlapBlock (r + 1))) (j : ℕ) : Set OverlapArray :=
  copyBlock r j ⁻¹' s

@[simp] lemma copyIndex_self (r : ℕ) (i : Fin (r + 1)) : copyIndex r r i = i := by
  unfold copyIndex
  split_ifs with h
  · exact h.symm
  · rfl

def duplicateEvent (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (j : ℕ) :
    Set OverlapArray :=
  copyEvent r s r ∩ copyEvent r s j ∩ {Q | Q r j < t}

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def appendLabel {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ) : Fin (n + 1) → κ :=
  Fin.lastCases k labels

@[simp] lemma appendLabel_last {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ) :
    appendLabel labels k (Fin.last n) = k := Fin.lastCases_last

@[simp] lemma appendLabel_castSucc {κ : Type*} {n : ℕ} (labels : Fin n → κ) (k : κ)
    (i : Fin n) : appendLabel labels k i.castSucc = labels i := Fin.lastCases_castSucc i

open Matrix
open scoped InnerProductSpace

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleIndex
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

abbrev PairedOverlapArray := ℕ → ℕ → ℝ × ℝ
abbrev PairedOverlapBlock (n : ℕ) := Fin n → Fin n → ℝ × ℝ

def pairedBlock (n : ℕ) (Q : PairedOverlapArray) : PairedOverlapBlock n :=
  fun i j => Q i j

def pairedRelabel (π : Equiv.Perm ℕ) (Q : PairedOverlapArray) : PairedOverlapArray :=
  fun i j => Q (π i) (π j)

def PairedSwapInvariant (μ : Measure PairedOverlapArray) : Prop :=
  ∀ i j : ℕ, MeasurePreserving (pairedRelabel (Equiv.swap i j)) μ μ

def JointGhirlandaGuerra (μ : Measure PairedOverlapArray) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n) (s : Set (PairedOverlapBlock n)), MeasurableSet s →
    ∀ t : Set (ℝ × ℝ), MeasurableSet t →
    μ.real (pairedBlock n ⁻¹' s ∩ {Q | Q i n ∈ t}) =
      μ.real (pairedBlock n ⁻¹' s) * μ.real {Q | Q 0 1 ∈ t} / n +
      (∑ j ∈ (Finset.univ.erase i),
        μ.real (pairedBlock n ⁻¹' s ∩ {Q | Q i j ∈ t})) / n

def UltrametricTriangle (x y z : ℝ) : Prop :=
  min x y ≤ z ∧ min x z ≤ y ∧ min y z ≤ x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def compactPairReal (x : CompactJointOverlap) : ℝ×ℝ := (x.1.val,x.2.val)
def compactArrayReal (Q : CompactArray CompactJointOverlap) : PairedOverlapArray :=
  fun i j => compactPairReal (Q i j)
def compactBlockReal {n : ℕ} (Q : CompactBlock CompactJointOverlap n) : PairedOverlapBlock n :=
  fun i j => compactPairReal (Q i j)

def compactRealLaw (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    Measure PairedOverlapArray := (μ : Measure _).map compactArrayReal

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGFiniteCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

section

variable {L : Type*} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

def compactCodeArray (χ : CompactJointOverlap → L) (Q : CompactArray CompactJointOverlap) :
    FiniteOverlap L := fun i j => χ (Q i j)

def compactCodeBlock {n : ℕ} (χ : CompactJointOverlap → L) (Q : CompactBlock CompactJointOverlap n) :
    FiniteBlock L n := fun i j => χ (Q i j)

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledStdGaussian (σ : ℝ) : Measure E := (stdGaussian E).map (σ • ·)

instance instIsProbabilityMeasureScaledStdGaussian (σ : ℝ) : IsProbabilityMeasure (scaledStdGaussian (E := E) σ) :=
  Measure.isProbabilityMeasure_map (μ := stdGaussian E) (f := fun x : E => σ • x) (Measurable.aemeasurable (by fun_prop))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBackward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianBackward (μ : Measure E) : List (ℝ×ℝ) → (E → ℝ) → E → ℝ
  | [], f => f
  | (p,σ)::l, f => gaussianEntropic μ p σ (gaussianBackward μ l f)

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

def cascadeHeatWord (σ : ℕ → ℝ) : (k : ℕ) → (Fin k → ℝ) → List (ℝ×ℝ)
  | 0, _ => []
  | k+1, z => (z 0,σ k)::cascadeHeatWord σ k (fun i => z i.succ)

def coordinateDepthField (d j : ℕ) (x : Fin d → ℕ → ℝ) : Spin d :=
  WithLp.toLp 2 (fun i => x i j)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GibbsOverlapArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A S K : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [CompactSpace K]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))
variable (Q : S → S → K) (hQ : Measurable (Function.uncurry Q))

def overlapArray (x : ℕ → S) : CompactArray K := fun i j => Q (x i) (x j)

include hQ in
omit [TopologicalSpace K] [BorelSpace K] [SecondCountableTopology K] [CompactSpace K] in
lemma overlapArray_measurable : Measurable (overlapArray Q) := by
  unfold overlapArray
  exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    hQ.comp (show Measurable (fun sequence : ℕ → S => (sequence row,sequence column)) from
      (measurable_pi_apply row).prodMk (measurable_pi_apply column))

def gibbsOverlapArrayLaw : ProbabilityMeasure (CompactArray K) :=
  ⟨(annealedInfiniteReplicaMeasure κ P H hH).map (fun a => overlapArray Q a.2),
    (Measure.isProbabilityMeasure_map_iff
      ((overlapArray_measurable Q hQ).comp measurable_snd).aemeasurable).2 inferInstance⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def bulkScale (N : ℕ) : ℝ := (N:ℝ)^((3:ℝ)/8)
def bulkDegree {N : ℕ} (p : Fin N) : ℕ := p.val+1
abbrev BulkMark (N : ℕ) := EnrichedMark N N bulkDegree

def bulkAmplitude (N : ℕ) (v : ℕ → ℝ) (p : Fin N) : ℝ :=
  bulkScale N * (2:ℝ)^(-((p.val+1:ℕ):ℤ))*v (p.val+1)

def bulkFeature (N : ℕ) (v : ℕ → ℝ) : NormalizedSpin N → BulkMark N :=
  enrichedFeature N N bulkDegree 0 (bulkAmplitude N v)

def bulkCovariance (N : ℕ) (v : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Fin N, ((2:ℝ)^(-((p.val+1:ℕ):ℤ)))^2 * (v (p.val+1))^2 * r^(p.val+1)

def bulkHamiltonian (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin N → ℝ) (g : BulkMark N) (x : NormalizedSpin N) : ℝ :=
  normalizedPatternEnergy N M f a x + inner ℝ (bulkFeature N v x) g

def bulkLogPartition (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (g : BulkMark (n+1)) : ℝ :=
  vectorLogPartition (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f a)
    (fun x => innerSL ℝ (bulkFeature (n+1) v x)) g

def bulkDisorderLaw (N M : ℕ) : Measure ((Fin M → Fin N → ℝ) × BulkMark N) :=
  (Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))).prod (stdGaussian (BulkMark N))

instance bulkDisorderLaw_probability (N M : ℕ) : IsProbabilityMeasure (bulkDisorderLaw N M) := by
  unfold bulkDisorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def bulkExpectedLog (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) : ℝ :=
  ∫ a, bulkLogPartition n M f v a.1 a.2 ∂bulkDisorderLaw (n+1) M

def bulkB (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x y : NormalizedSpin N) : ℝ :=
  (N:ℝ)⁻¹ * ∑ j, f.d1 (∑ i, a j i*x.val i) * f.d1 (∑ i, a j i*y.val i)

def bulkC (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x : NormalizedSpin N) : ℝ :=
  (N:ℝ)⁻¹ * ∑ j, (f.d2 (∑ i, a j i*x.val i) -
    (∑ i, a j i*x.val i)*f.d1 (∑ i, a j i*x.val i))

lemma bulkFeature_continuous (N : ℕ) (v : ℕ → ℝ) : Continuous (bulkFeature N v) :=
  enrichedFeature_continuous N N bulkDegree 0 (bulkAmplitude N v)

lemma bulkB_bound (N M : ℕ) (f : Jet3) (a : Fin M → Fin N → ℝ)
    (x y : NormalizedSpin N) : |bulkB N M f a x y| ≤ (M:ℝ)/(N:ℝ)*‖f.d1‖^2 := by
  unfold bulkB
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    _ ≤ (N:ℝ)⁻¹ * ∑ _ : Fin M, ‖f.d1‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [abs_mul, pow_two]
        exact mul_le_mul (f.d1.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _)
          (abs_nonneg _) (norm_nonneg _))
    _ = _ := by simp; ring

abbrev BulkDisorder (N M : ℕ) := (Fin M→Fin N→ℝ) × BulkMark N

def bulkFeatureBound (N : ℕ) (v : ℕ→ℝ) : ℝ := Real.sqrt (∑ p, bulkAmplitude N v p^2)

lemma bulkFeature_norm (N : ℕ) (v : ℕ→ℝ) (x : NormalizedSpin N) :
    ‖bulkFeature N v x‖=bulkFeatureBound N v := by
  rw [bulkFeature, enrichedFeature_norm]
  simp [bulkFeatureBound]

lemma bulkHamiltonian_continuous (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Continuous (fun p : BulkDisorder N M × NormalizedSpin N =>
      bulkHamiltonian N M f v p.1.1 p.1.2 p.2) := by
  unfold bulkHamiltonian
  exact ((normalizedPatternEnergy_continuous N M f).comp
    (continuous_fst.fst.prodMk continuous_snd)).add
    (((bulkFeature_continuous N v).comp continuous_snd).inner continuous_fst.snd)

lemma bulkHamiltonian_bound (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (a : BulkDisorder N M)
    (x : NormalizedSpin N) :
    |bulkHamiltonian N M f v a.1 a.2 x| ≤ M*‖f‖+bulkFeatureBound N v*‖a.2‖ := by
  apply (abs_add_le _ _).trans
  exact add_le_add (normalizedPatternEnergy_bound _ _ _ _ _) (by
    simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature N v x) a.2)

lemma bulkHamiltonian_exp_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) :
    Integrable (fun x => Real.exp (bulkHamiltonian (n+1) M f v a.1 a.2 x)) (unitSphereLaw (n+1)) := by
  apply Integrable.of_bound
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable
    (Real.exp (M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖))
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (bulkHamiltonian_bound (n+1) M f v a x))

def bulkSpinKernel (n M : ℕ) : Kernel (BulkDisorder (n+1) M) (NormalizedSpin (n+1)) :=
  Kernel.const _ (unitSphereLaw (n+1))

instance bulkSpinKernel_markov (n M : ℕ) : IsMarkovKernel (bulkSpinKernel n M) := by
  unfold bulkSpinKernel; infer_instance

def bulkOverlap {N : ℕ} (x y : NormalizedSpin N) : CompactOverlap :=
  ⟨spinOverlap x y,abs_le.mp (spinOverlap_abs_le x y)⟩

lemma bulkOverlap_measurable (N : ℕ) : Measurable (Function.uncurry (bulkOverlap (N:=N))) := by
  apply Measurable.subtype_mk
  exact measurable_fst.subtype_val.inner measurable_snd.subtype_val

def bulkGibbsArrayLaw (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    ProbabilityMeasure (CompactArray CompactOverlap) :=
  gibbsOverlapArrayLaw (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable bulkOverlap (bulkOverlap_measurable (n+1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkDirection (N : ℕ) (p : Fin N) : NormalizedSpin N→BulkMark N :=
  enrichedFeature N N bulkDegree 0 (Pi.single (M := fun _ : Fin N => ℝ) p 1)

def bulkCoefficient (N : ℕ) (p : Fin N) : ℝ := bulkScale N*(2:ℝ)^(-((p.val+1:ℕ):ℤ))

def bulkY (N : ℕ) (p : Fin N) (g : BulkMark N) (x : NormalizedSpin N) : ℝ :=
  inner ℝ (bulkDirection N p x) g

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GibbsRestoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_exp_bounds {H W : S→ℝ} (hH : Measurable H) (hW : Measurable W)
    (hi : Integrable (fun x => Real.exp (H x)) μ) {C : ℝ} (_hC : 0≤C)
    (hWb : ∀ x, |W x|≤C) :
    Real.exp (-C) ≤ tiltMean μ H (fun x => Real.exp (W x)) 1 ∧
      tiltMean μ H (fun x => Real.exp (W x)) 1 ≤ Real.exp C := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [←tilt_law_integral_of_integrable μ hH hi']
  have hI : Integrable (fun x => Real.exp (W x)) (tiltLaw μ H 1) := by
    apply Integrable.of_bound hW.exp.aestronglyMeasurable (Real.exp C)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (abs_le.mp (hWb x)).2
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-C))) hI
        (fun x => Real.exp_le_exp.mpr (abs_le.mp (hWb x)).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hI (integrable_const (Real.exp C))
        (fun x => Real.exp_le_exp.mpr (abs_le.mp (hWb x)).2)
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkFreshRestore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

def bulkSeparateLast (N M : ℕ) (a : BulkDisorder N (M+1)) :
    BulkDisorder N M × EuclideanSpace ℝ (Fin N) :=
  ((fun i => a.1 i.castSucc,a.2),WithLp.toLp 2 (a.1 (Fin.last M)))

def bulkSeparateTwo (N M : ℕ) (a : BulkDisorder N (M+2)) :
    BulkDisorder N M × (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) :=
  let b := bulkSeparateLast N (M+1) a
  let c := bulkSeparateLast N M b.1
  (c.1,(c.2,b.2))

lemma bulk_two_denominator_bounds (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (z t : EuclideanSpace ℝ (Fin (n+1))) :
    Real.exp (-(2*‖f‖)) ≤ tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (fun x => Real.exp (f (inner ℝ x.val z)+f (inner ℝ x.val t))) 1 ∧
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (fun x => Real.exp (f (inner ℝ x.val z)+f (inner ℝ x.val t))) 1 ≤ Real.exp (2*‖f‖) := by
  apply tiltMean_exp_bounds _
    ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
    ((f.measurable.comp (measurable_subtype_coe.inner measurable_const)).add
      (f.measurable.comp (measurable_subtype_coe.inner measurable_const)))
    (bulkHamiltonian_exp_integrable n M f v a) (by positivity)
  intro x
  exact (abs_add_le _ _).trans ((add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)).trans_eq
    (two_mul ‖f‖).symm)

def bulkPermutePatterns (N M : ℕ) (e : Equiv.Perm (Fin M))
    (a : BulkDisorder N M) : BulkDisorder N M := (fun i => a.1 (e i),a.2)

def bulkReplicaMean (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (F : BulkDisorder (n+1) M → (Fin r→NormalizedSpin (n+1))→ℝ) : ℝ :=
  ∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a)
    ∂bulkDisorderLaw (n+1) M

def bulkPatternFields {N M r : ℕ} (j : Fin M) (a : BulkDisorder N M)
    (x : Fin r→NormalizedSpin N) : Fin r→ℝ := fun i => ∑ t, a.1 j t*(x i).val t

lemma bulkPatternFields_measurable (N M r : ℕ) (j : Fin M) :
    Measurable (Function.uncurry (bulkPatternFields (N:=N) (r:=r) j)) := by
  have hc : Continuous (Function.uncurry (bulkPatternFields (N:=N) (r:=r) j)) := by
    unfold bulkPatternFields Function.uncurry
    fun_prop
  exact hc.measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkReplicaDominated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkPatternSize {N M : ℕ} (j : Fin M) (a : BulkDisorder N M) : ℝ := ∑ i,|a.1 j i|

def bulkTangentPattern {N M : ℕ} (f : Jet3) (G : ℝ→ᵇℝ) (j : Fin M)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 0) (x 1))*f.d1 (bulkPatternFields j a x 0)*
    (bulkPatternFields j a x 1-spinOverlap (x 0) (x 1)*bulkPatternFields j a x 0)


def freshTangent (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    (b : Spin N) (x : Fin 2→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 0) (x 1))*f.d1 (inner ℝ (x 0).val b)*
    (inner ℝ (x 1).val b-spinOverlap (x 0) (x 1)*inner ℝ (x 0).val b)

def freshTangentPair (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    (b : Spin N) (x : Fin 2→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 0) (x 1))*f.d1 (inner ℝ (x 0).val b)*f.d1 (inner ℝ (x 1).val b)*
    (1-spinOverlap (x 0) (x 1)^2)

def freshTangentTriple (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    (b : Spin N) (x : Fin 3→NormalizedSpin N) : ℝ :=
  G (spinOverlap (x 1) (x 2))*f.d1 (inner ℝ (x 1).val b)*f.d1 (inner ℝ (x 0).val b)*
    (spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def freshRadial (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) : ℝ :=
  inner ℝ (x 0).val b*f.d1 (inner ℝ (x 0).val b)
def freshSecond (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 1→NormalizedSpin N) : ℝ :=
  f.d2 (inner ℝ (x 0).val b)+f.d1 (inner ℝ (x 0).val b)^2
def freshRadialPair (N : ℕ) (f : Jet3) (b : Spin N) (x : Fin 2→NormalizedSpin N) : ℝ :=
  spinOverlap (x 0) (x 1)*f.d1 (inner ℝ (x 0).val b)*f.d1 (inner ℝ (x 1).val b)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_AmbientBulkFeature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators ContDiff
namespace SphericalPerceptronFreeEnergy

def ambientTensorFeature (N p : ℕ) (x : Spin N) : EuclideanSpace ℝ (SpinTensorIndex N p) :=
  WithLp.toLp 2 (fun i => ∏ j, x (i j))

def ambientBulkFeature (N : ℕ) (v : ℕ→ℝ) (x : Spin N) : BulkMark N :=
  WithLp.toLp 2 fun i => match i with
    | .inl _ => 0
    | .inr ⟨j,t⟩ => bulkAmplitude N v j*ambientTensorFeature N (bulkDegree j) x t

def bulkCovarianceDerivative (N : ℕ) (v : ℕ→ℝ) (r : ℝ) : ℝ :=
  ∑ j : Fin N, bulkAmplitude N v j^2*(j.val+1)*r^j.val

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DecoratedTiltTotal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def decoratedBiasedLaw (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ) (x : X) (a : ℝ) :
    Measure (DecoratedCascade S n) :=
  normalizedMeasure ((decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)).withDensity
    (fun η => ENNReal.ofReal ((decoratedWeightedTotal step n F (x,η))^a)))

def decoratedRootPotential (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(S×DecoratedCascade S n)) : ℝ :=
  F 0 (p.1,p.2.1)+Real.log
    (decoratedWeightedTotal step n (fun i => F i.succ) (step (p.1,p.2.1),p.2.2))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedBlockParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

@[reducible] def DecoratedVisitShape (X : Type) : ℕ → Type
  | 0 => ℕ × (X → ℝ≥0∞)
  | n+1 => List (DecoratedVisitShape X n)

def DecoratedVisitShape.bare {X : Type} : (n : ℕ) → DecoratedVisitShape X n → CascadeVisitShape n
  | 0, s => s.1
  | n+1, ss => ss.map (DecoratedVisitShape.bare n)

def DecoratedVisitShape.Valid {X : Type} [MeasurableSpace X] :
    (n : ℕ) → DecoratedVisitShape X n → Prop
  | 0, s => 1 ≤ s.1 ∧ Measurable s.2
  | n+1, ss => ss ≠ [] ∧ ∀ s ∈ ss, DecoratedVisitShape.Valid n s

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def decoratedCenteredRoot (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin (n+1) → ℝ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(S×DecoratedCascade S n)) : ℝ :=
  centeredLogMark ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))
    (z 0) (fun t => decoratedRootPotential step n F (p.1,t)) p.2

def decoratedShapeProbability (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → X×S → ℝ) →
      DecoratedVisitShape X n → X×DecoratedCascade S n → ℝ≥0∞
  | 0, _, _, s, p => s.2 p.1
  | n+1, z, F, ss, p => markedBlockProbability
      (ss.map (fun s => (cascadeVisitCount n (s.bare n),fun t : S×DecoratedCascade S n =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
          (step (p.1,t.1),t.2))))
      ((markedStableCountKernel p.2).map (fun t : ℝ×(S×DecoratedCascade S n) =>
        (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2))) (Fin.elim0 : Fin 0 → ℝ)

def decoratedShapeMarkValue (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → X×S → ℝ) →
      DecoratedVisitShape X n → X → ℝ≥0∞
  | 0, _, _, s, x => s.2 x
  | n+1, z, F, ss, x => (ss.map (fun s => ∫⁻ t,
      ENNReal.ofReal (Real.exp (z 0*F 0 (x,t)))*
        decoratedShapeMarkValue ν step n (fun i => z i.succ) (fun i => F i.succ)
          s (step (x,t)) ∂ν)).prod

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DecoratedShapeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

@[reducible] def PairedVisitShape (X Y : Type) : ℕ → Type
  | 0 => ℕ × ((X → ℝ≥0∞) × (Y → ℝ≥0∞))
  | n+1 => List (PairedVisitShape X Y n)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedTiltedLeaves
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def indexedShiftSum (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) →
    X×IndexedCascadeMarks S n → IndexedLeaf n → ℝ
  | 0,_,_,_ => 0
  | n+1,F,p,l => F 0 (p.1,(p.2 l.1 l.2.1).1)+
      indexedShiftSum step n (fun i => F i.succ)
        (step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2) l.2.2

lemma indexedShiftSum_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (Function.uncurry (indexedShiftSum step n F)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_from_prod_countable_left
    intro l
    change Measurable (fun p : X×(ℕ → ℕ → S×IndexedCascadeMarks S n) =>
      F 0 (p.1,(p.2 l.1 l.2.1).1)+indexedShiftSum step n (fun i => F i.succ)
        (step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2) l.2.2)
    exact ((hF 0).comp (by fun_prop)).add
      ((ih _ (fun i => hF i.succ)).comp (show Measurable
        (fun p : X×(ℕ → ℕ → S×IndexedCascadeMarks S n) =>
          ((step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2),l.2.2)) from by fun_prop))

def indexedTiltedLeafMeasure (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (x : X) (b : IndexedCascadeBase n) (m : IndexedCascadeMarks S n) :
    Measure (IndexedLeaf n) :=
  (indexedLeafMeasure n b).withDensity
    (fun l => ENNReal.ofReal (Real.exp (indexedShiftSum step n F (x,m) l)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedTiltedWeights
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.coordinateCascadeLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
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
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def indexedTiltedWeight (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (l : IndexedLeaf n) : ℝ≥0∞ :=
  (indexedLeafWeight n p.2.1 l : ℝ≥0∞)*
    ENNReal.ofReal (Real.exp (indexedShiftSum step n F (p.1,p.2.2) l))

def indexedTiltedTotal (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' l, indexedTiltedWeight step n F p l

def indexedTiltedProbability (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (l : IndexedLeaf n) : ℝ≥0∞ :=
  (indexedTiltedTotal step n F p)⁻¹ * indexedTiltedWeight step n F p l

lemma indexedTiltedWeight_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (Function.uncurry (indexedTiltedWeight step n F)) := by
  exact (((indexedLeafWeight_measurable n).comp (show Measurable
    (fun q : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×IndexedLeaf n =>
      (q.1.2.1,q.2)) from by fun_prop)).coe_nnreal_ennreal).mul
    (((indexedShiftSum_measurable hs n F hF).comp (show Measurable
      (fun q : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×IndexedLeaf n =>
        ((q.1.1,q.1.2.2),q.2)) from by fun_prop)).exp.ennreal_ofReal)

lemma indexedTiltedTotal_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (indexedTiltedTotal step n F) :=
  Measurable.tsum fun _ => (indexedTiltedWeight_measurable hs n F hF).comp
    (measurable_id.prodMk measurable_const)

lemma indexedTiltedProbability_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (Function.uncurry (indexedTiltedProbability step n F)) :=
  (((indexedTiltedTotal_measurable hs n F hF).comp measurable_fst).inv).mul
    (indexedTiltedWeight_measurable hs n F hF)

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedChildPoint (step : X×S → X) (n : ℕ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1))) (i j : ℕ) :
    X×(IndexedCascadeBase n×IndexedCascadeMarks S n) :=
  (step (p.1,(p.2.2 i j).1),(((p.2.1 i).2 j).2,(p.2.2 i j).2))

def indexedRootPoint (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin (n+1) → ℝ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1)) : ℝ×(S×DecoratedCascade S n) :=
  let t := ((p.2.2 a.1 a.2.val).1,
    indexedCascadeRealize n ((((p.2.1 a.1).2 a.2.val).2,(p.2.2 a.1 a.2.val).2)))
  ((((p.2.1 a.1).2 a.2.val).1 + decoratedCenteredRoot ν step n z F (p.1,t)),t)

def indexedBranchWeight (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (((p.2.1 a.1).2 a.2.val).1+F 0 (p.1,(p.2.2 a.1 a.2.val).1)))*
    indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val)

def indexedBranchProbability (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1)) : ℝ≥0∞ :=
  (indexedTiltedTotal step (n+1) F p)⁻¹*indexedBranchWeight step n F p a

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AtomicBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def countedBlockProbability {I S : Type*} (p : I → ℝ×S) :
    List (ℕ×(S → ℝ≥0∞)) → {m : ℕ} → (Fin m → ℝ) → ℝ≥0∞
  | [],_,_ => 1
  | nf::ns,_,z => ∑' i, if ∃ j, z j = (p i).1 then 0 else
      (((∑' k, ENNReal.ofReal (Real.exp (p k).1))⁻¹)*
        ENNReal.ofReal (Real.exp (p i).1))^nf.1 * nf.2 (p i).2 *
          countedBlockProbability p ns (Fin.cons (p i).1 z)

instance finiteSigmaMeasurableSingleton (k : ℕ → ℕ) :
    MeasurableSingletonClass (Σ j, Fin (k j)) := by
  constructor
  intro x
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' {x})
  exact (Set.toFinite _).measurableSet

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedVisit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
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

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedOneVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (h : X → ℝ≥0∞) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' l, indexedTiltedProbability step n F p l * h (indexedLeafState step n (p.1,p.2.2) l)

end

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedTwoVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (h k : X → ℝ≥0∞) (d : Fin (n+1))
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' l, indexedTiltedProbability step n F p l * ∑' m, indexedTiltedProbability step n F p m *
    if indexedCommonDepth n l m=d then h (indexedLeafState step n (p.1,p.2.2) l)*
      k (indexedLeafState step n (p.1,p.2.2) m) else 0

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def tiltedMarkKernel (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ) : Kernel X S :=
  (Kernel.const X (ν : Measure S)).withDensity
    (fun x s => ENNReal.ofReal (Real.exp (z*F (x,s))))

def tiltedStateStep (ν : ProbabilityMeasure S) (step : X×S → X)
    (z : ℝ) (F : X×S → ℝ) : Kernel X X :=
  (Kernel.id ×ₖ tiltedMarkKernel ν z F).map step

def pathOneKernel : (n : ℕ) → (Fin n → Kernel X X) → Kernel X X
  | 0, _ => Kernel.id
  | n+1, κ => pathOneKernel n (fun i => κ i.succ) ∘ₖ κ 0

def pathPairKernel : (n : ℕ) → (Fin n → Kernel X X) → Fin (n+1) → Kernel X (X×X)
  | 0, _, _ => Kernel.deterministic (fun x => (x,x)) (measurable_id.prodMk measurable_id)
  | n+1, κ, d => Fin.cases
      (pathOneKernel (n+1) κ ×ₖ pathOneKernel (n+1) κ)
      (fun j => pathPairKernel n (fun i => κ i.succ) j ∘ₖ κ 0) d

def pathMean (n : ℕ) (κ : Fin n → Kernel X X) (f : X → ℝ) (x : X) : ℝ :=
  ∫ y, f y ∂pathOneKernel n κ x

def pathCorrelation (n : ℕ) (κ : Fin n → Kernel X X) (f : X → ℝ)
    (d : Fin (n+1)) (x : X) : ℝ :=
  ∫ y, f y.1*f y.2 ∂pathPairKernel n κ d x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernelLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

section
variable {P Y I : Type} [MeasurableSpace P] [MeasurableSpace Y] [Countable I]

def atomicVisitKernel (q : I → P → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    (s : I → P → Y) (hs : ∀ i, Measurable (s i)) : Kernel P Y :=
  ⟨fun p => Measure.sum (fun i => q i p • Measure.dirac (s i p)), by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    simp only [Measure.sum_apply _ ht,Measure.smul_apply]
    exact Measurable.tsum (fun i => (hq i).mul ((Measure.measurable_coe ht).comp
      (Measure.measurable_dirac.comp (hs i))))⟩

end

omit [Nonempty S] in
lemma indexedTiltedProbability_fixed_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (x : X) (l : IndexedLeaf n) :
    Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n =>
      indexedTiltedProbability step n F (x,p) l) := by
  have hm : Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n => ((x,p),l)) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hc := (indexedTiltedProbability_measurable hs n F hF).comp hm
  dsimp only [Function.comp_def, Function.uncurry_def] at hc
  exact hc

omit [Nonempty S] in
lemma indexedLeafState_fixed_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (x : X) (l : IndexedLeaf n) :
    Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n =>
      indexedLeafState step n (x,p.2) l) := by
  have hm : Measurable (fun p : IndexedCascadeBase n×IndexedCascadeMarks S n => ((x,p.2),l)) :=
    (measurable_const.prodMk measurable_snd).prodMk measurable_const
  exact (indexedLeafState_measurable hs n).comp hm

def indexedOneStateKernel (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) :
    Kernel (IndexedCascadeBase n×IndexedCascadeMarks S n) X :=
  atomicVisitKernel (I := IndexedLeaf n)
    (P := IndexedCascadeBase n×IndexedCascadeMarks S n) (Y := X)
    (fun l p => indexedTiltedProbability step n F (x,p) l)
    (indexedTiltedProbability_fixed_measurable step hs n F hF x)
    (fun l p => indexedLeafState step n (x,p.2) l)
    (indexedLeafState_fixed_measurable step hs n x)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_AtomicPairVisitLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceBaseDataSourceBaseDataLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceIndexedDisorderSourceIndexedDisorderLaw
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

def indexedPairStateWeight (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (x : X) (d : Fin (n+1)) (a : IndexedLeaf n×IndexedLeaf n)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) : ℝ≥0∞ :=
  if indexedCommonDepth n a.1 a.2=d then
    indexedTiltedProbability step n F (x,p) a.1*indexedTiltedProbability step n F (x,p) a.2 else 0

omit [Nonempty S] in
lemma indexedPairStateWeight_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (x : X) (d : Fin (n+1)) (a : IndexedLeaf n×IndexedLeaf n) :
    Measurable (indexedPairStateWeight step n F x d a) := by
  unfold indexedPairStateWeight
  split_ifs
  · exact (indexedTiltedProbability_fixed_measurable step hs n F hF x a.1).mul
      (indexedTiltedProbability_fixed_measurable step hs n F hF x a.2)
  · exact measurable_const

def indexedPairStateKernel (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) (x : X) (d : Fin (n+1)) :
    Kernel (IndexedCascadeBase n×IndexedCascadeMarks S n) (X×X) :=
  atomicVisitKernel (I := IndexedLeaf n×IndexedLeaf n)
    (P := IndexedCascadeBase n×IndexedCascadeMarks S n) (Y := X×X)
    (indexedPairStateWeight step n F x d) (indexedPairStateWeight_measurable step hs n F hF x d)
    (fun a p => (indexedLeafState step n (x,p.2) a.1,indexedLeafState step n (x,p.2) a.2))
    (fun a => (indexedLeafState_fixed_measurable step hs n x a.1).prodMk
      (indexedLeafState_fixed_measurable step hs n x a.2))

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedMarkProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

section
variable {S T : Type} [MeasurableSpace S] [MeasurableSpace T]

def indexedMarksZip : (n : ℕ) → IndexedCascadeMarks S n × IndexedCascadeMarks T n →
    IndexedCascadeMarks (S×T) n
  | 0, _ => ()
  | n+1, p => fun i j => (((p.1 i j).1,(p.2 i j).1),
      indexedMarksZip n ((p.1 i j).2,(p.2 i j).2))

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

def indexedTerminalBaseKernel (n : ℕ) :
    Kernel (IndexedCascadeBase n×IndexedCascadeMarks S n) (IndexedLeaf n) :=
  (indexedLeafKernel n).comap Prod.fst measurable_fst
instance instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel (n : ℕ) : IsMarkovKernel (indexedTerminalBaseKernel (S:=S) n) := by
  unfold indexedTerminalBaseKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def indexedTerminalEnergy (step : X×S→X) (n : ℕ) (H : X→ℝ) (x : X)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) (l : IndexedLeaf n) : ℝ :=
  H (indexedLeafState step n (x,p.2) l)

def indexedTerminalPairMean (step : X×S→X) (n : ℕ) (H : X→ℝ) (x : X)
    (d : Fin (n+1)) (f : X→ℝ) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) : ℝ :=
  let κ := gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x)
  ∫ l : IndexedLeaf n×IndexedLeaf n,
    (if indexedCommonDepth n l.1 l.2=d then
      f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2) else 0)
      ∂(κ p).prod (κ p)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedPathDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
variable {X Y R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q]

def rootPathCorrelation (μ : Measure R) (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X)
    (f : X→ℝ) (d : Fin (n+1)) : ℝ := ∫ r, pathCorrelation n κ f d (x r) ∂μ

def rootPathMean (μ : Measure R) (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X)
    (f : X→ℝ) : ℝ := ∫ r, pathMean n κ f (x r) ∂μ

open scoped ENNReal NNReal BoundedContinuousFunction

def residualResponse (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  gaussianAverage s (expBCF 1 f * v) x / gaussianAverage s (expBCF 1 f) x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalRestorationCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

def indexedTerminalMean (step : X×S→X) (n : ℕ) (H : X→ℝ) (x : X)
    (f : X→ℝ) (p : IndexedCascadeBase n×IndexedCascadeMarks S n) : ℝ :=
  ∫ l, f (indexedLeafState step n (x,p.2) l)
    ∂gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegratedConvex
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
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

def countableGaussianVector (g : ℕ→ℝ) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => g (countableCoordinate i))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkTangentError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

def bulkTangentDirection (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (x : Fin 2→NormalizedSpin N) : BulkMark N :=
  G (spinOverlap (x 0) (x 1)) •
    fderiv ℝ (ambientBulkFeature N v) (x 0).val
      ((x 1).val-spinOverlap (x 0) (x 1) • (x 0).val)

def bulkPatternLinear {N : ℕ} (a : Fin N→ℝ) : Spin N→L[ℝ]ℝ :=
  ∑ i, a i • EuclideanSpace.proj i

def ambientBulkHamiltonian (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) (x : Spin N) : ℝ :=
  (∑ j,f.f (bulkPatternLinear (a j) x))+inner ℝ g (ambientBulkFeature N v x)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkAnnealedTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ContDiff

def bulkTangentPerturbation {N M : ℕ} (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) : ℝ :=
  inner ℝ (bulkTangentDirection N v G x) a.2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianComparison
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S] (n : ℕ)

def indexedCoefficientSquare (B : Fin (n+1)→I→ℝ) : ℝ := ∑ i, ∑ l, B l i^2

def indexedGaussianMean (μ : Measure (S×IndexedLeaf n)) (W : S×IndexedLeaf n→ℝ)
    (V : S→EuclideanSpace ℝ I) (B : Fin (n+1)→I→ℝ) : ℝ :=
  ∫ g, Real.log (tiltPartition μ (countableGaussianHamiltonian W (indexedGaussianRow n B V)
    (indexedGaussianRowLength (I := I) n) g) 1) ∂countableGaussianLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovarianceLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
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
variable {I : Type} [Fintype I] [DecidableEq I]

def doubledGaussianRows (B C : I → ℝ) (i : I) : EuclideanSpace ℝ (I ⊕ I) :=
  B i • EuclideanSpace.basisFun (I ⊕ I) ℝ (Sum.inl i) +
    C i • EuclideanSpace.basisFun (I ⊕ I) ℝ (Sum.inr i)

def diagonalGaussianRows (D : I → ℝ) (i : I) : EuclideanSpace ℝ I :=
  D i • EuclideanSpace.basisFun I ℝ i

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCovarianceDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

def duplicateFeature (V : S→EuclideanSpace ℝ I) (s : S) : EuclideanSpace ℝ (I ⊕ I) :=
  WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))

def leftCoefficients (B : Fin (n+1)→I→ℝ) (l : Fin (n+1)) : I ⊕ I→ℝ :=
  Sum.elim (B l) (fun _ => 0)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkCouplingSlope (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) : ℝ :=
  bulkCoefficient (n+1) p*tiltMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
    (bulkY (n+1) p a.2) 1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactJointMonomials
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def compactJointMonomial (p d : ℕ) : CompactJointOverlap →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x : CompactJointOverlap => (x.2:ℝ)^d*(x.1:ℝ)^p,by fun_prop⟩

@[simp] lemma compactJointMonomial_apply (p d : ℕ) (x : CompactJointOverlap) :
    compactJointMonomial p d x = (x.2:ℝ)^d*(x.1:ℝ)^p := rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedObservableTransport
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

def indexedResponse (μ : Measure (S×IndexedLeaf n))
    (K : (S×IndexedLeaf n)→(S×IndexedLeaf n)→ℝ) (H : S×IndexedLeaf n→ℝ) : ℝ :=
  tiltMean μ H (fun x => K x x) 1 - gibbsReplicaMean μ H 2 (fun x => K (x 1) (x 0))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkThermal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkThermalVar (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) : ℝ :=
  thermalVar (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2)
    (fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x) u

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkSlopeDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) : ℝ :=
  ∫ a, |bulkCouplingSlope n M f v p u a-
    ∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M| ∂bulkDisorderLaw (n+1) M

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkEnergyDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkEnergyDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) : ℝ :=
  ∫ a, tiltMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
    (fun x => |bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x-
      ∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M|) 1 ∂bulkDisorderLaw (n+1) M

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ParameterResampling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def bulkParameterUniform : Measure ℝ := volume.restrict (Ioc (1:ℝ) 2)

instance instIsProbabilityMeasureRealBulkParameterUniform : IsProbabilityMeasure bulkParameterUniform := ⟨by norm_num [bulkParameterUniform]⟩

def bulkParameterLaw : Measure (ℕ→ℝ) := Measure.infinitePi fun _ : ℕ => bulkParameterUniform

instance instIsProbabilityMeasureForallNatRealBulkParameterLaw : IsProbabilityMeasure bulkParameterLaw := by unfold bulkParameterLaw; infer_instance

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkParameterDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkDegreeDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) : ℝ :=
  bulkEnergyDeviation n M f v p (v (p.val+1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkReplicaStein
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkMoment (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ) (G : (Fin r→NormalizedSpin (n+1))→ℝ) : ℝ :=
  ∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r G ∂bulkDisorderLaw (n+1) M

def bulkNormalizedDeviation (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) : ℝ :=
  bulkDegreeDeviation n M f p v/(bulkCoefficient (n+1) p*bulkScale (n+1))

def bulkDeviationRate (A : ℝ) (f : ℝ→ᵇℝ) (p : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt 6*x^(-(3:ℝ)/8)+(24*(2:ℝ)^(-((p+1:ℕ):ℤ))+
    4*Real.sqrt (Real.pi^2/8*3^2+A*(2*‖f‖)^2)/(2:ℝ)^(-((p+1:ℕ):ℤ)))*x^(-(1:ℝ)/8)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DiagonalDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (d : ℕ→ℕ→X→ℝ)

def diagonalDeviationMass (J : ℕ→ℕ) (n : ℕ) : ℝ :=
  ∑ p∈Finset.range (J n), ∫ v, d n p v ∂μ

def diagonalDeviationThreshold (J : ℕ→ℕ) (n : ℕ) : ℝ :=
  Real.sqrt (diagonalDeviationMass μ d J n)+1/(n+1:ℝ)

def diagonalGoodSet (J : ℕ→ℕ) (n : ℕ) : Set X :=
  {v | ∀ p∈Finset.range (J n), d n p v≤diagonalDeviationThreshold μ d J n}

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkGoodParameters
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkDeviationAt (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) (v : ℕ→ℝ) : ℝ :=
  if hp : p<n+1 then bulkNormalizedDeviation n M f ⟨p,hp⟩ v else 0

def omittedBulkDeviation (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) (v : ℕ→ℝ) : ℝ :=
  bulkDeviationAt n (patternCount α (n+1)-2) f p v

def bulkGGDefect (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p r : ℕ) (j : Fin r)
    (G : (Fin r→NormalizedSpin (n+1))→ℝ) : ℝ :=
  bulkMoment n M f v r (fun x => G x*∑ l, spinOverlap (x j) (x l)^p)-bulkMoment n M f v r G+
    bulkMoment n M f v r G*bulkMoment n M f v 2 (fun x => spinOverlap (x 1) (x 0)^p)-
    r*bulkMoment n M f v (r+1) (fun x => G (fun l => x l.succ)*spinOverlap (x j.succ) (x 0)^p)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGDensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

def boundedTestIntegral (μ : Measure X) [IsProbabilityMeasure μ] : (X →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun c f => by simpa using integral_const_mul c (fun x => f x) }
    1 (fun f => by simpa using f.norm_integral_le_norm μ)

def compactGGTestCLM {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) : (K →ᵇ ℝ) →L[ℝ] ℝ := by
  classical
  let I := boundedTestIntegral (μ : Measure (CompactArray K))
  let F := f.compContinuous ⟨compactBlock n,compactBlock_continuous n⟩
  let E (a b : ℕ) := BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (⟨fun Q : CompactArray K => Q a b,by fun_prop⟩ : C(CompactArray K,K))
  let L (a b : ℕ) := I.comp ((ContinuousLinearMap.mul ℝ (CompactArray K →ᵇ ℝ) F).comp (E a b))
  exact (n:ℝ) • L i n - (I F) • (I.comp (E 0 1)) - ∑ j ∈ Finset.univ.erase i, L i j

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactScalarGG
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def compactScalarMonomial (p : ℕ) : CompactOverlap →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x : CompactOverlap => (x:ℝ)^p,by fun_prop⟩

@[simp] lemma compactScalarMonomial_apply (p : ℕ) (x : CompactOverlap) :
    compactScalarMonomial p x = (x:ℝ)^p := rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCompactGG
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkJointDeviation (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) (v : ℕ→ℝ) : ℝ :=
  bulkDeviationAt n (patternCount α (n+1)) f p v + omittedBulkDeviation α f n p v

def bulkJointGoodSet (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) : Set (ℕ→ℝ) :=
  diagonalGoodSet bulkParameterLaw (bulkJointDeviation α f) J n ∩ {v | ∀ p, v p∈Icc (1:ℝ) 2}

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMarkedKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma freshMarked_extension_exists {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    ∃ F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ,
      ‖F‖=‖gaussianCovarianceKernel Ψ‖ ∧
      ∀ C : CovarianceMatrix (Fin r), F C.val=gaussianCovarianceKernel Ψ C := by
  let : NormalSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (NormalSpace (Fin r→Fin r→ℝ))
  obtain ⟨F,hF,he⟩ := (gaussianCovarianceKernel Ψ).exists_extension_norm_eq_of_isClosedEmbedding
    (isClosed_matrix_posSemidef r).isClosedEmbedding_subtypeVal
  exact ⟨F,hF,fun C => congrFun he C⟩

def freshMarkedMatrixKernel {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ := Classical.choose (freshMarked_extension_exists Ψ)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def freshMarkedCompactBlockKernel {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    CompactBlock CompactOverlap r→ᵇℝ :=
  (freshMarkedMatrixKernel Ψ).compContinuous ⟨fun Q => fun i j => (Q i j).val,by fun_prop⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_RestorationReplicaBlocks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def restorationBlockTest (r : ℕ) (F : CompactBlock CompactOverlap r→ᵇℝ) :
    (k : ℕ) → CompactBlock CompactOverlap (r+k)→ᵇℝ
  | 0 => F
  | k+1 => (restorationBlockTest r F k).compContinuous
      ⟨fun Q i j => Q i.succ j.succ,by fun_prop⟩

def restorationMarkTest (r : ℕ) (f : ℝ→ᵇℝ) (Ψ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    (k : ℕ) → EuclideanSpace ℝ (Fin (r+k))→ᵇℝ
  | 0 => gaussianReplicaTest (expBCF 1 f)*Ψ
  | k+1 => ((expBCF 1 f).compContinuous ⟨fun x => x 0,by fun_prop⟩)*
      (restorationMarkTest r f Ψ k).compContinuous
        ⟨fun x => WithLp.toLp 2 (fun i => x i.succ),by fun_prop⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRestoredObservables
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev TwoFreshDisorder (N M : ℕ) := BulkDisorder N M ×
  (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))

def bulkMarkedTest (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))
    (x : Fin r → NormalizedSpin N) : ℝ :=
  F (fun i j => bulkOverlap (x i) (x j))*
    Ψ (gaussianRows (fun i => (x i).val) z.1)*Φ (gaussianRows (fun i => (x i).val) z.2)

def bulkFreshNumerator (n M r : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (p : TwoFreshDisorder (n+1) M) : ℝ :=
  gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2) r
    (bulkMarkedTest (n+1) r F (restorationMarkTest r f Ψ 0) (restorationMarkTest r f Φ 0) p.2)

def bulkFreshDenominator (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (p : TwoFreshDisorder (n+1) M) : ℝ :=
  tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
    (fun x => Real.exp (f (inner ℝ x.val p.2.1)+f (inner ℝ x.val p.2.2))) 1

lemma bulkFreshDenominator_mem (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ) (p : TwoFreshDisorder (n+1) M) :
    bulkFreshDenominator n M f v p ∈ Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) := by
  change Real.exp (-(2*‖f‖)) ≤ tiltMean (unitSphereLaw (n+1))
    (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
    (fun x => Real.exp (f (inner ℝ x.val p.2.1)+f (inner ℝ x.val p.2.2))) 1 ∧
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v p.1.1 p.1.2)
    (fun x => Real.exp (f (inner ℝ x.val p.2.1)+f (inner ℝ x.val p.2.2))) 1 ≤ Real.exp (2*‖f‖)
  exact bulk_two_denominator_bounds n M f v p.1 p.2.1 p.2.2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRestorationLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

def twoFreshDisorderLaw (N M : ℕ) : Measure (TwoFreshDisorder N M) :=
  (bulkDisorderLaw N M).prod ((stdGaussian (EuclideanSpace ℝ (Fin N))).prod
    (stdGaussian (EuclideanSpace ℝ (Fin N))))
instance instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw (N M : ℕ) : IsProbabilityMeasure (twoFreshDisorderLaw N M) := by
  unfold twoFreshDisorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def bulkFreshCompactDenominator (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (p : TwoFreshDisorder (n+1) M) : Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) :=
  ⟨bulkFreshDenominator n M f v p,bulkFreshDenominator_mem n M f v p⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw
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

def realTail (μ : Measure Time) (x : ℝ) : ℝ :=
  ∫ s, 1 - max x (s : ℝ) ∂μ

def realCDF (μ : Measure Time) (x : ℝ) : ℝ := μ.real {s : Time | (s : ℝ) ≤ x}

lemma continuous_time_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {f : Time → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma realTail_integrable (μ : Measure Time) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun s : Time => 1 - max x (s : ℝ)) μ :=
  continuous_time_integrable μ (by fun_prop)

lemma abs_realTail_sub_le (μ : Measure Time) [IsProbabilityMeasure μ] (x y : ℝ) :
    |realTail μ x - realTail μ y| ≤ |x - y| := by
  rw [realTail, realTail, ← integral_sub (realTail_integrable μ x) (realTail_integrable μ y)]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun s : Time => (1 - max x (s : ℝ)) - (1 - max y (s : ℝ)))
    (C := |x - y|) (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, show (1 - max x (s : ℝ)) - (1 - max y (s : ℝ)) =
        -(max x (s : ℝ) - max y (s : ℝ)) by ring, abs_neg]
      simpa using abs_max_sub_max_le_max x (s : ℝ) y (s : ℝ))
  simpa using hh

lemma realTail_continuous (μ : Measure Time) [IsProbabilityMeasure μ] :
    Continuous (realTail μ) := by
  have h : LipschitzWith 1 (realTail μ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [Real.dist_eq] using abs_realTail_sub_le μ x y
  exact h.continuous

def cappedDensity (μ : Measure Time) (B x : ℝ) : ℝ :=
  (max (1 - B) (realTail μ x))⁻¹ ^ 2

def cappedA (μ : Measure Time) (B r : ℝ) : ℝ :=
  ∫ t in 0..r, cappedDensity μ B t

lemma cappedDensity_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) : Continuous (cappedDensity μ B) := by
  unfold cappedDensity
  apply Continuous.pow
  exact (continuous_const.max (realTail_continuous μ)).inv₀ (fun x =>
    ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hB) (le_max_left _ _)))

lemma cappedA_hasDerivAt (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) (r : ℝ) :
    HasDerivAt (cappedA μ B) (cappedDensity μ B r) r := by
  have hc := cappedDensity_continuous μ hB
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma cappedA_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) : Continuous (cappedA μ B) :=
  continuous_iff_continuousAt.mpr (fun r => (cappedA_hasDerivAt μ hB r).continuousAt)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_WeightedCDF
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw
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

@[simp] lemma cappedA_zero (μ : Measure Time) (B : ℝ) : cappedA μ B 0 = 0 := by
  simp [cappedA]

def boundedCDF (μ : Measure Time) (r : Time) : ℝ := μ.real (Iic r)

lemma boundedCDF_eq (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    boundedCDF μ r = cdf (μ.map fun s : Time => (s : ℝ)) r := by
  rw [cdf_eq_real, map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
  rfl

lemma boundedCDF_monotone (μ : Measure Time) [IsProbabilityMeasure μ] :
    Monotone (boundedCDF μ) := by
  intro r s hrs
  exact measureReal_mono (Iic_subset_Iic.mpr hrs)

lemma boundedCDF_top (μ : Measure Time) [IsProbabilityMeasure μ] :
    boundedCDF μ 1 = 1 := by
  have h : Iic (1 : Time) = univ := by
    ext r
    simp only [mem_Iic, mem_univ, iff_true]
    exact r.property.2
  simp [boundedCDF, h]

lemma boundedCDF_right_continuous (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    ContinuousWithinAt (boundedCDF μ) (Ici r) r := by
  have hc := (cdf (μ.map fun s : Time => (s : ℝ))).right_continuous (r : ℝ)
  have hmap : MapsTo (Subtype.val : Time → ℝ) (Ici r) (Ici (r : ℝ)) := fun _ hs => hs
  have hcomp := hc.comp continuous_subtype_val.continuousWithinAt hmap
  simpa only [Function.comp_def, ← boundedCDF_eq] using hcomp

def boundedQuantile (μ : Measure Time) (u : Time) : Time :=
  sInf {r : Time | (u : ℝ) ≤ boundedCDF μ r}

lemma boundedQuantile_le_iff (μ : Measure Time) [IsProbabilityMeasure μ] (u r : Time) :
    boundedQuantile μ u ≤ r ↔ (u : ℝ) ≤ boundedCDF μ r := by
  let A : Set Time := {r | (u : ℝ) ≤ boundedCDF μ r}
  have hA : A.Nonempty := ⟨1, by simpa [A, boundedCDF_top] using u.property.2⟩
  have hcont : ContinuousWithinAt (boundedCDF μ) A (sInf A) :=
    (boundedCDF_right_continuous μ _).mono (fun x hx => sInf_le hx)
  have hmin : (u : ℝ) ≤ boundedCDF μ (sInf A) := by
    rw [MonotoneOn.map_csInf_of_continuousWithinAt hcont ((boundedCDF_monotone μ).monotoneOn A) hA]
    apply le_csInf (hA.image _)
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  constructor
  · intro h
    exact hmin.trans (boundedCDF_monotone μ h)
  · exact fun h => sInf_le h

lemma boundedQuantile_monotone (μ : Measure Time) [IsProbabilityMeasure μ] :
    Monotone (boundedQuantile μ) := by
  intro u v huv
  rw [boundedQuantile_le_iff]
  exact (show (u : ℝ) ≤ v from huv).trans ((boundedQuantile_le_iff μ v _).mp le_rfl)

lemma boundedQuantile_measurable (μ : Measure Time) [IsProbabilityMeasure μ] :
    Measurable (boundedQuantile μ) := (boundedQuantile_monotone μ).measurable

instance instIsProbabilityMeasurePatternsPatternLaw (α : ℝ) (N : ℕ) : IsProbabilityMeasure (patternLaw α N) := by
  unfold patternLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianAffineCoordinate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {I : Type} [Fintype I] [DecidableEq I]

def eraseMarkCoordinate (i : I) (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (Function.update (fun j => x j) i 0)

def diagonalWord (l : List (ℝ×(I→ℝ))) : List (ℝ×(EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)) :=
  l.map (fun a => (a.1,diagonalMark a.2))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_PureLabel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

section DiagonalWord
variable {I : Type} [Fintype I]

def diagonalCascadeWord (A : ℕ→I→ℝ) : (k : ℕ)→(Fin k→ℝ)→List (ℝ×(I→ℝ))
  | 0,_ => []
  | k+1,z => (z 0,A k)::diagonalCascadeWord A k (fun i => z i.succ)

end DiagonalWord

def enrichedIncrementFactors {N k : ℕ} (p d : Fin N→ℕ) (h : Fin (k+1)→ℝ)
    (j : ℕ) : EnrichedIndex N N p→ℝ :=
  if hj : j<k then fun i => Real.sqrt
    (enrichedCoordinateLevel p d h ⟨k-j,by omega⟩ i-
     enrichedCoordinateLevel p d h ⟨k-j-1,by omega⟩ i) else fun _ => 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def weightedStepTrial {I : Type*} [Fintype I] (w : I → ℝ) (q : I → Time)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : Trial where
  toFun := fun t => ∑ i, if q i ≤ t then w i else 0
  monotone := by
    intro s t hst
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i ≤ s
    · simp only [ite_eq_left hi,ite_eq_left (hi.trans hst),le_refl]
    · rw [ite_eq_right hi]
      split_ifs <;> first | exact hw i | rfl
  measurable := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
  nonneg := by
    intro t
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  le_one := by
    intro t
    rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | rfl | exact hw i

def stepCumulative {k : ℕ} (w : Fin (k+1) → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin (k+1), if j ≤ i.castSucc then w j else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepDual
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def stepFieldIncrement (k : ℕ) (h : Fin (k+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < k then
    Real.sqrt (2*(h (Fin.rev ⟨j,hj⟩).succ-h (Fin.rev ⟨j,hj⟩).castSucc)) else 0

def finiteSphericalFieldValue (n k : ℕ) (w h : Fin (k+1) → ℝ) : ℝ :=
  expectedCoordinateSphereLog n k (stepFieldIncrement k h) (stepCumulative w)
    (Real.toNNReal (2*h 0))-h (Fin.last k)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_SynchronizedLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceLabelLevel (k : ℕ) (l : Fin (k+1)) : unitInterval :=
  ⟨(l.val:ℝ)/(k+1:ℕ),by constructor; positivity; exact (div_le_one (by positivity)).mpr (by exact_mod_cast l.isLt.le)⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def compactPositivePair (x : CompactJointOverlap) : Time×Time :=
  (⟨max 0 x.1.val,le_max_left _ _,max_le (by norm_num) x.1.property.2⟩,x.2)

lemma compactPositivePair_measurable : Measurable compactPositivePair := by
  unfold compactPositivePair
  fun_prop

def compactPositivePairLaw (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) : Measure (Time×Time) :=
  (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => compactPositivePair (Q 0 1))

instance compactPositivePairLaw_probability (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure (compactPositivePairLaw ν) :=
  (Measure.isProbabilityMeasure_map_iff ((compactPositivePair_measurable.comp (show Measurable (fun Q : CompactArray CompactJointOverlap => Q 0 1) from by fun_prop)).aemeasurable)).2 inferInstance


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshReplicaKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

lemma freshKernel_extension_exists (f : ℝ →ᵇ ℝ) (r : ℕ) :
    ∃ F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ,
      ‖F‖=‖gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin r) f)‖ ∧
      ∀ C : CovarianceMatrix (Fin r), F C.val=gaussianCovarianceKernel (gaussianReplicaTest f) C := by
  let : NormalSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (NormalSpace (Fin r→Fin r→ℝ))
  obtain ⟨F,hF,he⟩ := (gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin r) f)).exists_extension_norm_eq_of_isClosedEmbedding
    (isClosed_matrix_posSemidef r).isClosedEmbedding_subtypeVal
  exact ⟨F,hF,fun C => congrFun he C⟩

def freshReplicaMatrixKernel (f : ℝ →ᵇ ℝ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ :=
  Classical.choose (freshKernel_extension_exists f r)

def freshReplicaArrayKernel (f : ℝ →ᵇ ℝ) (r : ℕ) : CompactArray CompactJointOverlap →ᵇ ℝ :=
  (freshReplicaMatrixKernel f r).compContinuous
    ⟨fun Q => fun i j : Fin r => (Q i j).1.val,by fun_prop⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StationaryExistence
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def stepTailSum {k : ℕ} (v : Fin k → ℝ) (i : Fin (k+1)) : ℝ :=
  ∑ j : Fin k, if i ≤ j.castSucc then v j else 0

def finitePrecisionShift {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  stepTailSum (fun i => 2*z i*(h i.succ-h i.castSucc))

def finitePrecisionTail {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (b : ℝ) (i : Fin (k+1)) : ℝ := (b-finitePrecisionShift z h i)⁻¹

def finiteOverlapIncrement {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ)
    (b : ℝ) (i : Fin k) : ℝ :=
  2*(h i.succ-h i.castSucc)*finitePrecisionTail z h b i.castSucc*finitePrecisionTail z h b i.succ

def finiteStationarityMass {k : ℕ} (z : Fin k → ℝ) (h : Fin (k+1) → ℝ) (b : ℝ) : ℝ :=
  2*h 0*(finitePrecisionTail z h b 0)^2+(∑ i, finiteOverlapIncrement z h b i)+
    finitePrecisionTail z h b (Fin.last k)

def finiteSphericalDualObjective {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (q : Fin (k+1) → Time) : ℝ :=
  (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ)

def finiteSphericalDualValues {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) : Set ℝ :=
  finiteSphericalDualObjective w h hw hw1 ''
    {q : Fin (k+1) → Time | Monotone q ∧ (q (Fin.last k):ℝ) < 1}

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatGrid
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianGrid (N : ℕ) (p v : Fin N → ℝ) (f : E → ℝ) : E → ℝ :=
  gaussianBackward (stdGaussian E) (List.ofFn fun i => (p i,Real.sqrt (v i))) f

end

def gridVariance {N : ℕ} (l : List (Fin N×ℝ)) (i : Fin N) : ℝ :=
  (l.map fun c => if c.1=i then c.2 else 0).sum

end

def amplitudeCovarianceLevels (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) (i : Fin (k+1)) : ℝ :=
  (r^2+stepTailSum (fun j : Fin k => (σ (k-1-j.val))^2) 0-
    stepTailSum (fun j : Fin k => (σ (k-1-j.val))^2) i)/2

def amplitudeSphereDual {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (σ : ℕ → ℝ) (r : ℝ) : ℝ :=
  sInf (finiteSphericalDualValues w (amplitudeCovarianceLevels k σ r) hw hw1)+
    amplitudeCovarianceLevels k σ r (Fin.last k)

def finiteAmplitudeIncrement (k : ℕ) (a : Fin (k+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < k then a (⟨j,hj⟩ : Fin k).castSucc else 0

def finiteAmplitudeSphereValue (n k : ℕ) (w : Fin (k+1) → ℝ) (a : Fin (k+1) → ℝ) : ℝ :=
  amplitudeSphereValue n k (finiteAmplitudeIncrement k a) (stepCumulative w) (a (Fin.last k))

def finiteAmplitudeSphereDual {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) : ℝ :=
  amplitudeSphereDual w hw hw1 (finiteAmplitudeIncrement k a) (a (Fin.last k))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ConvexUniform
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  if _hi : i.val < k then stepFieldIncrement k h i.val else Real.sqrt (2*h 0)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldWord
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def fieldVariances (k : ℕ) (h : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cases (2*h 0) (fun i => 2*(h i.succ-h i.castSucc))

def fieldExponents {k : ℕ} (w : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cases 0 (stepCumulative w)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteFieldModel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma integral_finite_label {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (a : Time → I) (ha : Measurable a) (F : I → ℝ) :
    (∫ u, F (a u) ∂timeLaw)=∑ i, timeLaw.real (a ⁻¹' {i})*F i := by
  classical
  have he (u : Time) : F (a u)=∑ i, (if a u=i then F i else 0) := by simp
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    change (∫ u, (a ⁻¹' {i}).indicator (fun _ => F i) u ∂timeLaw)=_
    rw [integral_indicator (ha (measurableSet_singleton i)),integral_const]
    simp only [Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
  · intro i _
    exact (integrable_const (F i)).indicator (ha (measurableSet_singleton i))

structure FiniteFieldModel (f : Time → ℝ) where
  depth : ℕ
  value : Fin (depth+1) → ℝ
  label : Time → Fin (depth+1)
  measurable_label : Measurable label
  positive : ∀ i, 0 < timeLaw.real (label ⁻¹' {i})
  monotone_value : Monotone value
  agrees : (fun u => value (label u)) =ᵐ[timeLaw] f

def FiniteFieldModel.weight {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) : ℝ :=
  timeLaw.real (M.label ⁻¹' {i})

lemma FiniteFieldModel.weight_pos {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) :
    0 < M.weight i := M.positive i

lemma FiniteFieldModel.weight_sum {f : Time → ℝ} (M : FiniteFieldModel f) : ∑ i, M.weight i=1 := by
  have h := integral_finite_label M.label M.measurable_label (fun _ => 1)
  simpa [FiniteFieldModel.weight] using h.symm

lemma FiniteFieldModel.values_mem {f : Time → ℝ} (M : FiniteFieldModel f)
    {H : ℝ} (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H) (i : Fin (M.depth+1)) :
    M.value i ∈ Icc (0:ℝ) H := by
  have hi : timeLaw (M.label ⁻¹' {i}) ≠ 0 := by
    intro hi
    have hp := M.positive i
    change 0 < (timeLaw (M.label ⁻¹' {i})).toReal at hp
    rw [hi] at hp
    simp at hp
  have hne : ∃ u, M.label u=i ∧ M.value (M.label u) ∈ Icc (0:ℝ) H := by
    by_contra! hn
    have hzero : ∀ᵐ u ∂timeLaw, u ∉ M.label ⁻¹' {i} := by
      filter_upwards [M.agrees,hf] with u hu hv
      intro hm
      exact hn u hm (hu ▸ hv)
    exact hi (by simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hzero)
  obtain ⟨u,hu,hv⟩ := hne
  simpa [hu] using hv

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformQuantileCells
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def uniformQuantileGrid (n : ℕ) (i : Fin (n+2)) : Time :=
  ⟨(i:ℝ)/(n+1),div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity : (0:ℝ)<n+1)).mpr (by exact_mod_cast (Nat.le_of_lt_succ i.isLt))⟩

def uniformQuantileCell (n : ℕ) (u : Time) : Fin (n+1) :=
  ⟨min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n, Nat.lt_succ_of_le (min_le_right _ _)⟩

def compactSpinTime (x : CompactOverlap) : Time :=
  ⟨(x.val+1)/2,by linarith [x.2.1],by linarith [x.2.2]⟩

def compactSpinCode (n : ℕ) (x : CompactJointOverlap) : Fin (n+1) :=
  uniformQuantileCell n (compactSpinTime x.1)

def compactSpinDecode (n : ℕ) (i : Fin (n+1)) : ℝ :=
  2*(uniformQuantileGrid n i.castSucc:ℝ)-1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGGUniqueness
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def CompactSpinGeometry (Q : CompactArray CompactJointOverlap) : Prop :=
  (∀ i j, (Q i j).1.val=(Q j i).1.val) ∧ (∀ i, (Q i i).1.val=1) ∧
    ∀ i j k, min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val

def compactSpinTop : CompactOverlap := ⟨1,by norm_num⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshThermalLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

abbrev FreshPartitionRange (f : ℝ →ᵇ ℝ) := Icc (Real.exp (-‖f‖)) (Real.exp ‖f‖)

lemma freshPartition_lower_le_upper (f : ℝ →ᵇ ℝ) : Real.exp (-‖f‖)≤Real.exp ‖f‖ :=
  Real.exp_le_exp.mpr (neg_le_self (norm_nonneg f))

def freshPartitionClip (f : ℝ →ᵇ ℝ) (x : ℝ) : FreshPartitionRange f :=
  ⟨max (Real.exp (-‖f‖)) (min (Real.exp ‖f‖) x),le_max_left _ _,
    max_le (freshPartition_lower_le_upper f) (min_le_left _ _)⟩

lemma freshPartitionClip_measurable (f : ℝ →ᵇ ℝ) : Measurable (freshPartitionClip f) := by
  apply Measurable.subtype_mk
  exact measurable_const.max (measurable_const.min measurable_id)

variable {A S E : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))
variable (v : S→E) (hv : Measurable v) (f : ℝ →ᵇ ℝ)

def freshThermalPartition (a : A×E) : ℝ :=
  tiltMean (κ a.1) (H a.1) (fun x => Real.exp (f (inner ℝ (v x) a.2))) 1

include hH hv in
lemma freshThermalPartition_measurable : Measurable (freshThermalPartition κ H v f) := by
  let κ' : Kernel (A×E) S := κ.comap (fun a : A×E => a.1) measurable_fst
  have hH' : Measurable (fun a : (A×E)×S => H a.1.1 a.2) :=
    hH.comp (measurable_fst.fst.prodMk measurable_snd)
  have hF : Measurable (fun a : (A×E)×S => Real.exp (f (inner ℝ (v a.2) a.1.2))) :=
    (f.measurable.comp ((hv.comp measurable_snd).inner measurable_fst.snd)).exp
  exact kernel_tiltMean_measurable κ' hH' hF

def freshThermalLaw : ProbabilityMeasure (FreshPartitionRange f) :=
  ⟨(P.prod (stdGaussian E)).map (fun a => freshPartitionClip f (freshThermalPartition κ H v f a)), by
    exact (Measure.isProbabilityMeasure_map_iff ((freshPartitionClip_measurable f).comp
      (freshThermalPartition_measurable κ H hH v hv f)).aemeasurable).2 inferInstance⟩

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlledPrefix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
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

def controlledPrefix (m : Trial) (v : Time → BrownianPath → ℝ) (t : Time) (ω : BrownianPath) : ℝ :=
  brownianEval ⟨t.val,t.property.1⟩ ω + ∫ r in Set.Iic t, m r * v r ω ∂timeLaw

def timeSpan (s t : Time) : ℝ≥0 := Real.toNNReal ((t : ℝ)-(s : ℝ))

def intervalControlCost (m : Trial) (v : Time → BrownianPath → ℝ) (s t : Time) (ω : BrownianPath) : ℝ :=
  ∫ r in Set.Ioc s t, m r * (v r ω)^2 ∂timeLaw

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
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

def backwardScore (P : Measure BrownianPath) (m : Trial) (v : Time → BrownianPath → ℝ)
    (a b : Time) (d : ℝ≥0) (g : Jet3) (t : Time) : ℝ :=
  (∫ ω, heatLog (timeSpan t b) d g.f (controlledPrefix m v t ω) ∂P) -
    (∫ ω, intervalControlCost m v a t ω ∂P)/2

inductive HeatChain (m : Trial) (g : Jet3) : Time → Time → Jet3 → Prop
  | nil (a : Time) : HeatChain m g a a g
  | cons {a t b : Time} {h : Jet3} (d : ℝ≥0) (hat : a < t) (htb : t ≤ b)
      (hm : ∀ r ∈ Set.Ioc a t, m r = (d : ℝ)) (tail : HeatChain m g t b h) :
      HeatChain m g a b (h.heatLog (timeSpan a t) d)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def finiteStepControlJet (g : Jet3) : (n : ℕ)→(Fin (n+1)→Time)→(Fin n→ℝ≥0)→Jet3
  | 0,_,_ => g
  | n+1,q,d => (finiteStepControlJet g n (fun i => q i.succ) (fun i => d i.succ)).heatLog
      (timeSpan (q 0) (q 1)) (d 0)

def leftWeightedStepTrial {I : Type*} [Fintype I] (w : I→ℝ) (q : I→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) : Trial where
  toFun := fun t => ∑ i, if q i<t then w i else 0
  monotone := by
    intro s t hst
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i < s
    · simp only [ite_eq_left hi,ite_eq_left (hi.trans_le hst),le_refl]
    · rw [ite_eq_right hi]
      split_ifs <;> first | exact hw i | rfl
  measurable := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const
  nonneg := by
    intro t
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hw i | rfl
  le_one := by
    intro t
    rw [← hw1]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | rfl | exact hw i

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CountableFreshMoment
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

variable {S : Type} [MeasurableSpace S] {k : ℕ}

def labelProfileRow (q : Fin (k+1)→ℝ) : ℕ→S×IndexedLeaf k→ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k
    (profileGaussianRoot (fun l (_ : Fin 1) => q l))
    (profileGaussianStep (fun l (_ : Fin 1) => q l)))
    (fun _ : S => WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))

def labelProfileField (q : Fin (k+1)→ℝ) (g : ℕ→ℝ) : S×IndexedLeaf k→ℝ :=
  countableGaussianField (labelProfileRow q) (indexedGaussianRowLength (I := Fin 1) k) g

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshDiagonalNoise
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal BoundedContinuousFunction ENNReal

section

variable {n r : ℕ}

def freshNoiseRows (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) (i : Fin r) :
    EuclideanSpace ℝ (Fin n ⊕ Fin r) :=
  WithLp.toLp 2 (Sum.elim (fun j => v i j) (fun j => if j=i then Real.sqrt s else 0))

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def labelProfileInterpolant {k : ℕ} (q : Fin (k+1)→ℝ) : Time →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => (Lagrange.interpolate Finset.univ (fun l => (sourceLabelLevel k l).val) q).eval u.val,
      by fun_prop⟩

def labelFreshBlockKernel {k : ℕ} (q : Fin (k+1)→ℝ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    CompactBlock CompactJointOverlap r →ᵇ ℝ :=
  (freshReplicaMatrixKernel f r).compContinuous
    ⟨fun Q => fun i j => if i=j then 1 else labelProfileInterpolant q (Q i j).2,
      by
        classical
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        by_cases hij : i=j
        · simp only [ite_eq_left hij]
          exact continuous_const
        · simp only [ite_eq_right hij]
          fun_prop⟩

def labelFreshArrayKernel {k : ℕ} (q : Fin (k+1)→ℝ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    CompactArray CompactJointOverlap →ᵇ ℝ :=
  (labelFreshBlockKernel q f r).compContinuous ⟨compactBlock r,compactBlock_continuous r⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelThermalLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {A S E : Type*} [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace E]
variable (κ : Kernel A S) [IsMarkovKernel κ]
variable (P : Measure A) [IsProbabilityMeasure P] (G : Measure E) [IsProbabilityMeasure G]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))
variable (F : E→S→ℝ) (hF : Measurable (Function.uncurry F))
variable (f : ℝ →ᵇ ℝ) (hFb : ∀ g x, |F g x|≤‖f‖)

def boundedThermalPartition (a : A×E) : ℝ :=
  tiltMean (κ a.1) (H a.1) (fun x => Real.exp (F a.2 x)) 1

include hH hF in
lemma boundedThermalPartition_measurable : Measurable (boundedThermalPartition κ H F) := by
  let κ' : Kernel (A×E) S := κ.comap Prod.fst measurable_fst
  exact kernel_tiltMean_measurable κ'
    (hH.comp (measurable_fst.fst.prodMk measurable_snd))
    ((hF.comp (measurable_fst.snd.prodMk measurable_snd)).exp)

def boundedThermalLaw : ProbabilityMeasure (FreshPartitionRange f) :=
  ⟨(P.prod G).map (fun a => freshPartitionClip f (boundedThermalPartition κ H F a)),
    (Measure.isProbabilityMeasure_map_iff ((freshPartitionClip_measurable f).comp
      (boundedThermalPartition_measurable κ H hH F hF)).aemeasurable).2 inferInstance⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileField_measurable {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) :
    Measurable (Function.uncurry (labelProfileField (S := S) q)) :=
  countableGaussianField_measurable (indexedGaussianRow_measurable _ _ measurable_const)
    (indexedGaussianRowLength_measurable k)

def labelLogResponse {S : Type} {k : ℕ} (q : Fin (k+1)→ℝ)
    (hq1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) : ℝ :=
  heatLog ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ 1 f (labelProfileField q g x)

lemma labelLogResponse_measurable {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelLogResponse (S := S) q hq1 f)) :=
  (heatLog_continuous _ _ f).measurable.comp (labelProfileField_measurable q)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceFreshReferenceData (n k : ℕ) (p : Fin (n+1)→ℕ) :=
  (EuclideanSpace ℝ (Fin 1)×EnrichedMark (n+1) (n+1) p)×
    (IndexedCascadeBase k×(IndexedCascadeMarks (EuclideanSpace ℝ (Fin 1)) k×
      IndexedCascadeMarks (EnrichedMark (n+1) (n+1) p) k))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReferenceValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def labelProfileTerminal (g : Jet3) (s : ℝ≥0) (v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  heatLog s 1 g.f (inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceLabelData (n k : ℕ) :=
  ℕ × ((ℕ→Fin (n+1)→ℝ) × (IndexedCascadeBase k × ((ℕ→ℝ)×(ℕ→ℝ))))

def labelProfileValue (k : ℕ) (z : Fin k→ℝ) (q : Fin (k+1)→ℝ)
    (hq1 : q (Fin.last k)≤1) (g : Jet3) : ℝ :=
  ∫ x, gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (linearCascadeWord (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => q l) j)) k z)
    (labelProfileTerminal g ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩)
    (diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l)) x)
    ∂stdGaussian (EuclideanSpace ℝ (Fin 1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldRounding
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

structure BoundedField (H : ℝ) where
  toFun : Time → ℝ
  monotone : Monotone toFun
  nonneg : ∀ u, 0 ≤ toFun u
  le_bound : ∀ u, toFun u ≤ H

instance instCoeFunBoundedFieldForallElemRealTime {H : ℝ} : CoeFun (BoundedField H) (fun _ => Time → ℝ) := ⟨BoundedField.toFun⟩

lemma BoundedField.measurable {H : ℝ} (f : BoundedField H) : Measurable f := f.monotone.measurable

def roundLower (N : ℕ) (x : ℝ) : ℝ := (⌊(N+1:ℕ)*x⌋₊:ℝ)/(N+1:ℕ)

lemma roundLower_nonneg (N : ℕ) (x : ℝ) : 0 ≤ roundLower N x := by unfold roundLower; positivity

lemma roundLower_monotone (N : ℕ) : Monotone (roundLower N) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (by positivity))

lemma roundLower_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : roundLower N x ≤ x := by
  unfold roundLower
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg (by positivity) hx)

def BoundedField.round {H : ℝ} (f : BoundedField H) (N : ℕ) : BoundedField H where
  toFun := fun u => roundLower N (f u)
  monotone := (roundLower_monotone N).comp f.monotone
  nonneg := fun u => roundLower_nonneg N (f u)
  le_bound := fun u => (roundLower_le N (f.nonneg u)).trans (f.le_bound u)

lemma BoundedField.round_finite {H : ℝ} (f : BoundedField H) (N : ℕ) :
    (Set.range (f.round N)).Finite := by
  let T := (Finset.range (⌊(N+1:ℕ)*H⌋₊+1)).image (fun k : ℕ => (k:ℝ)/(N+1:ℕ))
  apply T.finite_toSet.subset
  rintro x ⟨u,rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨⌊(N+1:ℕ)*f u⌋₊,?_,rfl⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left (f.le_bound u) (by positivity)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_QuantileControlContinuity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cdfIndicator (a t : Time) : ℝ := if a≤t then 1 else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_StepControlTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def linearStepIntervals : (n : ℕ) → (Fin (n+1)→ℝ) → (Fin (n+1)→ℝ) →
    (Fin n→ℝ≥0) → List HeatIntervalParam
  | 0,_,_,_ => []
  | n+1,q,r,d =>
    { duration := fun t => (1-t)*(q 1-q 0)+t*(r 1-r 0)
      rate := (r 1-q 1)-(r 0-q 0)
      coefficient := d 0 } ::
      linearStepIntervals n (fun i => q i.succ) (fun i => r i.succ) (fun i => d i.succ)

def blendControlNodes {n : ℕ} (q e : Fin (n+1)→Time) (t : Time) (i : Fin (n+1)) : Time :=
  ⟨(1-(t:ℝ))*(q i:ℝ)+(t:ℝ)*(e i:ℝ),
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (q i).2.1) (mul_nonneg t.2.1 (e i).2.1),by
    nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr (q i).2.2),
      mul_nonneg t.2.1 (sub_nonneg.mpr (e i).2.2)]⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileUpperTail
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma uniformQuantileWeights_nonneg (n : ℕ) : ∀ _i : Fin (n+1), (0:ℝ) ≤ 1/(n+1:ℝ) := by
  intro i
  positivity
lemma uniformQuantileWeights_sum (n : ℕ) : (∑ _i : Fin (n+1), (1/(n+1:ℝ)))=1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_CompactArrayMap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

def compactMapArray (e : K→L) (Q : CompactArray K) : CompactArray L := fun i j => e (Q i j)
def compactMapBlock (e : K→L) (n : ℕ) (Q : CompactBlock K n) : CompactBlock L n := fun i j => e (Q i j)

lemma compactMapArray_continuous {e : K→L} (he : Continuous e) : Continuous (compactMapArray e) := by
  unfold compactMapArray
  fun_prop

def compactDiagonalMapArray (e d : K→L) (Q : CompactArray K) : CompactArray L :=
  fun i j => if i=j then d (Q i j) else e (Q i j)
def compactDiagonalMapBlock (e d : K→L) (n : ℕ) (Q : CompactBlock K n) : CompactBlock L n :=
  fun i j => if i=j then d (Q i j) else e (Q i j)

lemma compactDiagonalMapArray_continuous {e d : K→L} (he : Continuous e) (hd : Continuous d) :
    Continuous (compactDiagonalMapArray e d) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold compactDiagonalMapArray
  split_ifs <;> fun_prop


variable [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
  [SecondCountableTopology K] [SecondCountableTopology L]

def compactMapLaw (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K)) :
    ProbabilityMeasure (CompactArray L) :=
  ⟨(μ : Measure (CompactArray K)).map (compactMapArray e),
    (Measure.isProbabilityMeasure_map_iff (compactMapArray_continuous he).measurable.aemeasurable).2
      (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def compactDiagonalMapLaw (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K)) : ProbabilityMeasure (CompactArray L) :=
  ⟨(μ : Measure (CompactArray K)).map (compactDiagonalMapArray e d),
    (Measure.isProbabilityMeasure_map_iff
      (compactDiagonalMapArray_continuous he hd).measurable.aemeasurable).2 inferInstance⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def CompactLabelGeometry (k : ℕ) (Q : CompactArray CompactJointOverlap) : Prop :=
  (∀ i j, (Q i j).2.val=(Q j i).2.val) ∧
  (∀ i, (Q i i).2.val=(k:ℝ)/(k+1:ℕ)) ∧
  ∀ i j l, min (Q i j).2.val (Q i l).2.val ≤ (Q j l).2.val

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def CompactLabelNodes (k : ℕ) (Q : CompactArray CompactJointOverlap) : Prop :=
  ∀ i j, (Q i j).2∈Set.range (sourceLabelLevel k)

def labelProfileSpin {k : ℕ} (q : Fin (k+1)→Time) (x : Time) : CompactOverlap :=
  ⟨min 1 (max 0 (labelProfileInterpolant (fun i => (q i:ℝ)) x)),
    le_min (by norm_num) ((by norm_num : (-1:ℝ)≤0).trans (le_max_left _ _)),min_le_left _ _⟩
lemma labelProfileSpin_continuous {k : ℕ} (q : Fin (k+1)→Time) : Continuous (labelProfileSpin q) := by
  unfold labelProfileSpin
  fun_prop

def labelProfileMap {k : ℕ} (q : Fin (k+1)→Time) (x : CompactJointOverlap) : CompactJointOverlap :=
  (labelProfileSpin q x.2,x.2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReferenceFull
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def labelProfileDiagonal (x : CompactJointOverlap) : CompactJointOverlap :=
  (⟨1,by norm_num,le_rfl⟩,x.2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_FreshControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

instance compactPositivePairLaw_fst_isProbability
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
  (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_TwoVisitWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def depthMassIncrement : (n : ℕ) → (Fin n→ℝ) → ℝ → Fin (n+1) → ℝ
  | 0,_,a,_ => 1-a
  | n+1,z,a,d => Fin.cases (z 0-a) (fun i => depthMassIncrement n (fun j => z j.succ) (z 0) i) d

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableMarkedDiagonal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def gaussianMixedTest {r : ℕ} (f : Fin r→ℝ →ᵇ ℝ) : EuclideanSpace ℝ (Fin r) →ᵇ ℝ :=
  ∏ i : Fin r, (f i).compContinuous ⟨fun x => x i,by fun_prop⟩

@[simp] lemma gaussianMixedTest_apply {r : ℕ} (f : Fin r→ℝ →ᵇ ℝ)
    (x : EuclideanSpace ℝ (Fin r)) : gaussianMixedTest f x=∏ i, f i (x i) := by
  simp [gaussianMixedTest]

variable {S : Type} [MeasurableSpace S] {k r : ℕ}

def labelMarkedBlockKernel (q : Fin (k+1)→ℝ) (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    CompactBlock CompactJointOverlap r →ᵇ ℝ :=
  (freshMarkedMatrixKernel Ψ).compContinuous
    ⟨fun Q => fun i j => if i=j then 1 else labelProfileInterpolant q (Q i j).2,by
      classical
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      by_cases hij : i=j
      · simp only [ite_eq_left hij]; exact continuous_const
      · simp only [ite_eq_right hij]; fun_prop⟩

def labelMixedValue (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ)
    (z : ℕ→ℝ) (xs : Fin r→S×IndexedLeaf k) : ℝ :=
  ∏ i, gaussianAverageBCF s (f i) (labelProfileField q z (xs i))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S : Type} [MeasurableSpace S] {k : ℕ}

def replicaFrontLift {r : ℕ} (F : (Fin r→S)→ℝ) : (j : ℕ)→(Fin (r+j)→S)→ℝ
  | 0 => F
  | j+1 => fun x => replicaFrontLift F j (fun i => x i.succ)

def labelRestoredFunctions {r : ℕ} (f : ℝ →ᵇ ℝ) (v : Fin r→ℝ →ᵇ ℝ) :
    (j : ℕ)→Fin (r+j)→ℝ →ᵇ ℝ
  | 0 => fun i => expBCF 1 f*v i
  | j+1 => Fin.cons (expBCF 1 f) (labelRestoredFunctions f v j)

def labelRestorationWeight (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) : ℝ :=
  gaussianAverageBCF s (expBCF 1 f) (labelProfileField q z.1 x) *
    gaussianAverageBCF s (expBCF 1 f) (labelProfileField q z.2 x)

def labelRestorationTest {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) (F : (Fin r→S×IndexedLeaf k)→ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : Fin r→S×IndexedLeaf k) : ℝ :=
  F x * labelMixedValue q s (fun i => expBCF 1 f*v i) z.1 x *
    labelMixedValue q s (fun i => expBCF 1 f*w i) z.2 x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationKernel
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

def labelKernelDenominator (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : ℝ :=
  tiltMean (κ a.1) (H a.1) (labelRestorationWeight q s f a.2) 1

def labelKernelNumerator (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : ℝ :=
  gibbsReplicaMean (κ a.1) (H a.1) r (labelRestorationTest q s f v w F a.2)

def labelKernelRestoredRatio (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : ℝ :=
  labelKernelNumerator κ H q s f v w F a / (labelKernelDenominator κ H q s f a)^r

abbrev RestorationRange (f : ℝ →ᵇ ℝ) := Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖))

def restorationClip (f : ℝ →ᵇ ℝ) (x : ℝ) : RestorationRange f :=
  ⟨max (Real.exp (-(2*‖f‖))) (min (Real.exp (2*‖f‖)) x),le_max_left _ _,
    max_le (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg f])) (min_le_left _ _)⟩

def labelKernelCompactDenominator (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : RestorationRange f :=
  restorationClip f (labelKernelDenominator κ H q s f a)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments2
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

def jointRestorationBlockTest (r : ℕ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    (j : ℕ) → CompactBlock CompactJointOverlap (r+j) →ᵇ ℝ
  | 0 => F
  | j+1 => (jointRestorationBlockTest r F j).compContinuous
      ⟨fun Q i l => Q i.succ l.succ,by fun_prop⟩

def labelRestorationBlockMoment {k r : ℕ} (q : Fin (k+1) → ℝ) (f : ℝ →ᵇ ℝ)
    (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ) (j : ℕ) :
    CompactBlock CompactJointOverlap (r+j) →ᵇ ℝ :=
  jointRestorationBlockTest r F j * labelMarkedBlockKernel q (gaussianMixedTest (labelRestoredFunctions f v j)) *
    labelMarkedBlockKernel q (gaussianMixedTest (labelRestoredFunctions f w j))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_CountableTerminalRestoration
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

abbrev TripleGaussianState := ((ℕ→EuclideanSpace ℝ I)×(ℕ→EuclideanSpace ℝ J))×(ℕ→EuclideanSpace ℝ K)
abbrev TripleGaussianMark := (EuclideanSpace ℝ I×EuclideanSpace ℝ J)×EuclideanSpace ℝ K
abbrev TripleGaussianData (k : ℕ) :=
  TripleGaussianMark I J K × (IndexedCascadeBase k×
    (IndexedCascadeMarks (EuclideanSpace ℝ I×EuclideanSpace ℝ J) k×IndexedCascadeMarks (EuclideanSpace ℝ K) k))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TripleGaussianReplica
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

def gaussianLeafValue (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) (g : ℕ→ℝ) (l : IndexedLeaf k) : EuclideanSpace ℝ I :=
  indexedLeafState (gaussianLinearMarkStep A) k
    ((fun _ => R (indexedGaussianDisorder k I g).1),(indexedGaussianDisorder k I g).2) l 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev labelGaussianStep {k : ℕ} (q : Fin (k+1)→ℝ) :=
  fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => q l) j)
abbrev labelGaussianRoot {k : ℕ} (q : Fin (k+1)→ℝ) :=
  diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l))
def labelEvaluation (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) x

def labelResidualObservable (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) : EuclideanSpace ℝ (Fin 1)→ℝ :=
  fun x => residualResponse s f v (labelEvaluation x)

variable {S K : Type} [MeasurableSpace S] [Fintype K]

def labelPairCoefficient (k : ℕ) (z : Fin k→ℝ) (q : Fin (k+1)→ℝ)
    (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) (d : Fin (k+1)) : ℝ :=
  rootPathCorrelation (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) k
    (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
      (gaussianLinearMarkStep (labelGaussianStep q)) (z i)
      (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
        (gaussianLinearMarkStep (labelGaussianStep q)) k z (fun x => labelProfileTerminal g s (x 0)) i))
    (fun x => labelResidualObservable s g.f v (x 0)) d

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestoredValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceLabelPairData (n k : ℕ) :=
  ℕ × ((ℕ→Fin (n+1)→ℝ) × (IndexedCascadeBase k × (((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))))

def labelDepthTest {S : Type} (k : ℕ) (d : Fin (k+1)) (x : Fin 2 → S×IndexedLeaf k) : ℝ :=
  if indexedCommonDepth k (x 0).2 (x 1).2=d then 1 else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def labelProfilePairTest {k : ℕ} (q : Fin (k+1)→Time) (F : CompactOverlap →ᵇ ℝ) :
    CompactBlock CompactJointOverlap 2 →ᵇ ℝ :=
  F.compContinuous ⟨fun Q => labelProfileSpin q (Q 1 0).2,
    (labelProfileSpin_continuous q).comp (by fun_prop)⟩

def compactPairTest (F : CompactOverlap →ᵇ ℝ) : CompactBlock CompactOverlap 2 →ᵇ ℝ :=
  F.compContinuous ⟨fun Q => Q 1 0,by fun_prop⟩

def labelProfileGram {k r : ℕ} (q : Fin (k+1)→Time) (Q : CompactBlock CompactJointOverlap r) :
    Matrix (Fin r) (Fin r) ℝ := fun i l => if i=l then 1 else (labelProfileSpin q (Q i l).2).val

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactRestorationWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

abbrev WeightedRestorationRange (f : ℝ →ᵇ ℝ) (C : ℝ) := Icc (-C) C × RestorationRange f

def compactWeightedLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (C : ℝ)
    (A : Ω→ℝ) (hA : Measurable A) (Z : Ω→RestorationRange f) (hZ : Measurable Z)
    (hb : ∀ x, |A x|≤C) : ProbabilityMeasure (WeightedRestorationRange f C) :=
  ⟨μ.map (fun x => (⟨A x,abs_le.mp (hb x)⟩,Z x)),
    (Measure.isProbabilityMeasure_map_iff ((hA.subtype_mk).prodMk hZ).aemeasurable).2 inferInstance⟩

def labelSingleCoefficient (k : ℕ) (z : Fin k→ℝ) (q : Fin (k+1)→ℝ)
    (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) : ℝ :=
  rootPathMean (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) k
    (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
      (gaussianLinearMarkStep (labelGaussianStep q)) (z i)
      (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
        (gaussianLinearMarkStep (labelGaussianStep q)) k z (fun x => labelProfileTerminal g s (x 0)) i))
    (fun x => labelResidualObservable s g.f v (x 0))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkLimitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

def bulkJointEmbedding (q : CompactOverlap) : CompactJointOverlap := (q,0)
lemma bulkJointEmbedding_continuous : Continuous bulkJointEmbedding := by
  unfold bulkJointEmbedding; fun_prop

def bulkJointLaw (μ : ProbabilityMeasure (CompactArray CompactOverlap)) :
    ProbabilityMeasure (CompactArray CompactJointOverlap) :=
  compactMapLaw bulkJointEmbedding bulkJointEmbedding_continuous μ

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedPairCoefficients
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

theorem exists_finiteFieldModel_strict (f : Time → ℝ) (hf : Measurable f)
    (hfin : (Set.range f).Finite) : ∃ M : FiniteFieldModel f, StrictMono M.value := by
  classical
  let S := hfin.toFinset
  let T := S.filter (fun r => 0 < timeLaw.real (f ⁻¹' {r}))
  have hae : ∀ᵐ u ∂timeLaw, f u ∈ T := by
    have hnull : ∀ r ∈ S, ∀ᵐ u ∂timeLaw, f u=r → 0 < timeLaw.real (f ⁻¹' {r}) := by
      intro r _hr
      by_cases hp : 0 < timeLaw.real (f ⁻¹' {r})
      · exact ae_of_all _ (fun _ _ => hp)
      · have hz : timeLaw (f ⁻¹' {r})=0 := by
          have hz : (timeLaw (f ⁻¹' {r})).toReal=0 := le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
          have hp := (ENNReal.toReal_eq_zero_iff _).mp hz
          rcases hp with hp | hp
          · exact hp
          · exact (measure_ne_top _ _ hp).elim
        have hnot : ∀ᵐ u ∂timeLaw, f u ≠ r := by
          apply ae_iff.mpr
          simpa only [Set.preimage,Set.mem_singleton_iff,not_not] using hz
        filter_upwards [hnot] with u hu
        exact fun h => (hu h).elim
    have hall := (S.eventually_all).mpr hnull
    filter_upwards [hall] with u hu
    have hmem : f u ∈ S := hfin.mem_toFinset.mpr (mem_range_self u)
    exact Finset.mem_filter.mpr ⟨hmem,hu (f u) hmem rfl⟩
  have hT : T.Nonempty := by
    obtain ⟨u,hu⟩ := hae.exists
    exact ⟨f u,hu⟩
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hT)
  let e := T.orderIsoOfFin hd
  let v : Fin (d+1) → ℝ := fun i => e i
  have hv : StrictMono v := fun i j hij => e.strictMono hij
  have hve : MeasurableEmbedding v := ⟨hv.injective,measurable_of_finite _,fun _ _ => (Set.toFinite _).measurableSet⟩
  let a : Time → Fin (d+1) := fun u => hve.invFun (f u)
  have hag : (fun u => v (a u)) =ᵐ[timeLaw] f := by
    filter_upwards [hae] with u hu
    have hx : f u=v (e.symm ⟨f u,hu⟩) := congrArg Subtype.val (e.apply_symm_apply ⟨f u,hu⟩) |>.symm
    dsimp only [a]
    rw [hx,hve.leftInverse_invFun]
  refine ⟨⟨d,v,a,hve.measurable_invFun.comp hf,?_,hv.monotone,hag⟩,hv⟩
  intro i
  have he : a ⁻¹' {i}=ᵐ[timeLaw] f ⁻¹' {v i} := by
    filter_upwards [hag] with u hu
    apply propext
    change (a u=i) ↔ f u=v i
    rw [← hu]
    exact hv.injective.eq_iff.symm
  change 0 < (timeLaw (a ⁻¹' {i})).toReal
  rw [measure_congr he]
  exact (Finset.mem_filter.mp (e i).2).2

def finiteMonotoneExtension {k : ℕ} (q a : Fin (k+1)→ℝ) (r : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => if q i ≤ r then a i else a 0)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedMarkedSelection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def unitQuantileField (q : Time→Time) (hq : Monotone q) : BoundedField 1 :=
  ⟨fun u => q u,fun _ _ h => hq h,fun u => (q u).prop.1,fun u => (q u).prop.2⟩

def strictRoundModel {H : ℝ} (q : BoundedField H) (n : ℕ) : FiniteFieldModel (q.round n) :=
  (exists_finiteFieldModel_strict (q.round n) (q.round n).measurable (q.round_finite n)).choose

def roundTimeValue (q : BoundedField 1) (n : ℕ) : Fin ((strictRoundModel q n).depth+1)→Time :=
  fun i => ⟨(strictRoundModel q n).value i,(strictRoundModel q n).values_mem
    (ae_of_all _ fun u => ⟨(q.round n).nonneg u,(q.round n).le_bound u⟩) i⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedPairLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def pairFieldMark (w : ℝ→ᵇℝ) (z : Fin 2→ℝ) : ℝ := ∏ i,w (z i)
lemma pairFieldMark_measurable (w : ℝ→ᵇℝ) : Measurable (pairFieldMark w) := by
  unfold pairFieldMark
  fun_prop
lemma pairFieldMark_bound (w : ℝ→ᵇℝ) (z : Fin 2→ℝ) : |pairFieldMark w z|≤‖w‖^2 := by
  simp only [pairFieldMark,Fin.prod_univ_two,abs_mul,pow_two]
  exact mul_le_mul (w.norm_coe_le_norm _) (w.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)

def bulkPairAverage (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 2→NormalizedSpin (n+1)) : ℝ :=
  ((n+1:ℕ):ℝ)⁻¹*∑ i,pairFieldMark w (bulkPatternFields i a x)

lemma bulkPairAverage_measurable (n M : ℕ) (w : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (bulkPairAverage n M w)) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ => (pairFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)

lemma bulkPairAverage_bound (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 2→NormalizedSpin (n+1)) : |bulkPairAverage n M w a x|≤M/(n+1:ℕ)*‖w‖^2 := by
  unfold bulkPairAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(((n+1:ℕ):ℝ)⁻¹))]
  have h : |∑ i : Fin M,pairFieldMark w (bulkPatternFields i a x)|≤M*‖w‖^2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => pairFieldMark_bound w _).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

def bulkPairOverlapTest (n : ℕ) (F : CompactOverlap→ᵇℝ) (x : Fin 2→NormalizedSpin (n+1)) : ℝ :=
  F (bulkOverlap (x 1) (x 0))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkPairLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev BulkPairRange (K : ℝ) := CompactOverlap × Icc (-K) K

def bulkFiniteReplicaLaw (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measure (BulkDisorder (n+1) M × (Fin r→NormalizedSpin (n+1))) := by
  letI := gibbsProbabilityKernel_markov (bulkSpinKernel n M)
    (fun a => bulkHamiltonian (n+1) M f v a.1 a.2) (bulkHamiltonian_continuous _ _ _ _).measurable
  exact (bulkDisorderLaw (n+1) M) ⊗ₘ kernelReplica
    (gibbsProbabilityKernel (bulkSpinKernel n M)
      (fun a => bulkHamiltonian (n+1) M f v a.1 a.2)) r

instance bulkFiniteReplicaLaw_probability (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    IsProbabilityMeasure (bulkFiniteReplicaLaw n M r f v) := by
  let := gibbsProbabilityKernel_markov (bulkSpinKernel n M)
    (fun a => bulkHamiltonian (n+1) M f v a.1 a.2) (bulkHamiltonian_continuous _ _ _ _).measurable
  unfold bulkFiniteReplicaLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def bulkCompactPair (n M : ℕ) (w : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K)
    (p : BulkDisorder (n+1) M × (Fin 2→NormalizedSpin (n+1))) : BulkPairRange K :=
  (bulkOverlap (p.2 1) (p.2 0),⟨bulkPairAverage n M w p.1 p.2,
    abs_le.mp ((bulkPairAverage_bound n M w p.1 p.2).trans hK)⟩)

lemma bulkCompactPair_measurable (n M : ℕ) (w : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) : Measurable (bulkCompactPair n M w K hK) := by
  have hp : Measurable (fun p : BulkDisorder (n+1) M × (Fin 2→NormalizedSpin (n+1)) =>
      (p.2 1,p.2 0)) :=
    ((measurable_pi_apply 1).comp measurable_snd).prodMk
      ((measurable_pi_apply 0).comp measurable_snd)
  exact ((bulkOverlap_measurable (n+1)).comp hp).prodMk
    (bulkPairAverage_measurable n M w |>.subtype_mk)

def bulkPairLaw (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) : ProbabilityMeasure (BulkPairRange K) :=
  ⟨(bulkFiniteReplicaLaw n M 2 f v).map (bulkCompactPair n M w K hK),
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact (bulkCompactPair_measurable n M w K hK).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩


def compactPairMarginal (ν : ProbabilityMeasure (CompactArray CompactOverlap)) :
    ProbabilityMeasure CompactOverlap :=
  ν.map (f := fun Q : CompactArray CompactOverlap => Q 0 1) (by fun_prop : Measurable (fun Q : CompactArray CompactOverlap => Q 0 1)).aemeasurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkB_measurable (N M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder N M×(NormalizedSpin N×NormalizedSpin N) =>
      bulkB N M f p.1.1 p.2.1 p.2.2) := by
  unfold bulkB
  fun_prop

def bulkMarkedEntry (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (a : BulkDisorder (n+1) M)
    (x y : NormalizedSpin (n+1)) : BulkPairRange K :=
  (bulkOverlap x y,⟨bulkB (n+1) M f a.1 x y,abs_le.mp ((bulkB_bound _ _ _ _ _ _).trans hK)⟩)

def bulkMarkedArray (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K)
    (p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1))) : CompactArray (BulkPairRange K) :=
  fun i j => bulkMarkedEntry n M f K hK p.1 (p.2 i) (p.2 j)

lemma bulkMarkedArray_measurable (n M : ℕ) (f : Jet3) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) : Measurable (bulkMarkedArray n M f K hK) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hm : Measurable (fun p : BulkDisorder (n+1) M×(ℕ→NormalizedSpin (n+1)) => (p.2 i,p.2 j)) := by fun_prop
  exact ((bulkOverlap_measurable _).comp hm).prodMk
    (((bulkB_measurable _ _ _).comp (measurable_fst.prodMk hm)).subtype_mk)

def bulkGibbsHamiltonian (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    BulkDisorder (n+1) M→NormalizedSpin (n+1)→ℝ :=
  fun a => bulkHamiltonian (n+1) M f v a.1 a.2

lemma bulkGibbsHamiltonian_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measurable (Function.uncurry (bulkGibbsHamiltonian n M f v)) :=
  (bulkHamiltonian_continuous (n+1) M f v).measurable

def bulkMarkedArrayLaw (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) : ProbabilityMeasure (CompactArray (BulkPairRange K)) :=
  ⟨(annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
      (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)).map
        (bulkMarkedArray n M f K hK),
    (Measure.isProbabilityMeasure_map_iff (bulkMarkedArray_measurable _ _ _ _ _).aemeasurable).2 inferInstance⟩

def markedTangentR (K : ℝ) (G : ℝ→ᵇℝ) : CompactBlock (BulkPairRange K) 2→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => (Q 0 1).1.val*G (Q 0 1).1.val,by fun_prop⟩
def markedTangentPair (K : ℝ) (G : ℝ→ᵇℝ) : CompactBlock (BulkPairRange K) 2→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun Q => G (Q 0 1).1.val*(Q 0 1).2.val*(1-(Q 0 1).1.val^2),by fun_prop⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def singleFieldMark (w : ℝ→ᵇℝ) (z : Fin 1→ℝ) : ℝ := w (z 0)

def bulkSingleAverage (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 1→NormalizedSpin (n+1)) : ℝ :=
  ((n+1:ℕ):ℝ)⁻¹*∑ i,singleFieldMark w (bulkPatternFields i a x)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleEmpiricalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

abbrev bulkAnnealedReplicaLaw (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :=
  annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f v) (bulkGibbsHamiltonian_measurable n M f v)

def Jet3.dilationMark (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) : ℝ→ᵇℝ :=
  g.d2-ofCompactSupport (fun z => z*g.d1 z)
    (continuous_id.mul g.d1.continuous) hg.mul_left

@[simp] lemma Jet3.dilationMark_apply (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) (z : ℝ) :
    g.dilationMark hg z=g.d2 z-z*g.d1 z := rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators BoundedContinuousFunction Topology

def bulkRadialRow (n M : ℕ) (f : Jet3) (j : Fin M) (a : BulkDisorder (n+1) M) := freshRadial (n+1) f (WithLp.toLp 2 (a.1 j))
def bulkSecondRow (n M : ℕ) (f : Jet3) (j : Fin M) (a : BulkDisorder (n+1) M) := freshSecond (n+1) f (WithLp.toLp 2 (a.1 j))
def bulkRadialPairRow (n M : ℕ) (f : Jet3) (j : Fin M) (a : BulkDisorder (n+1) M) := freshRadialPair (n+1) f (WithLp.toLp 2 (a.1 j))

def Jet3.radialMark (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) : ℝ→ᵇℝ :=
  ofCompactSupport (fun z => z*f.d1 z) (continuous_id.mul f.d1.continuous) hf.mul_left

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRadialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction BigOperators Matrix

lemma isClosed_covarianceMatrix {I : Type*} [Fintype I] [DecidableEq I] :
    IsClosed {M : Matrix I I ℝ | M.PosSemidef} := by
  have he : {M : Matrix I I ℝ | M.PosSemidef} =
      {M : Matrix I I ℝ | ∀ i j, M j i=M i j} ∩ ⋂ x : I → ℝ,
        {M : Matrix I I ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [mem_ofPred_eq,mem_inter_iff,mem_iInter,Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.IsHermitian.ext_iff,star_trivial]
  rw [he]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun x => isClosed_le continuous_const (by
      unfold dotProduct Matrix.mulVec
      fun_prop)

lemma cavity_extension_exists {I : Type*} [Fintype I] [DecidableEq I]
    (Ψ : EuclideanSpace ℝ I →ᵇ ℝ) :
    ∃ F : Matrix I I ℝ →ᵇ ℝ,
      ‖F‖=‖gaussianCovarianceKernel Ψ‖ ∧
      ∀ C : CovarianceMatrix I, F C.val=gaussianCovarianceKernel Ψ C := by
  let : NormalSpace (Matrix I I ℝ) := inferInstanceAs (NormalSpace (I→I→ℝ))
  obtain ⟨F,hF,he⟩ := (gaussianCovarianceKernel Ψ).exists_extension_norm_eq_of_isClosedEmbedding
    isClosed_covarianceMatrix.isClosedEmbedding_subtypeVal
  exact ⟨F,hF,fun C => congrFun he C⟩

def cavityMatrixKernel {I : Type*} [Fintype I] [DecidableEq I]
    (Ψ : EuclideanSpace ℝ I →ᵇ ℝ) : Matrix I I ℝ →ᵇ ℝ :=
  Classical.choose (cavity_extension_exists Ψ)

lemma sphericalExp_continuous (n : ℕ) (R : ℝ) : Continuous (fun x => sphericalExp n x R) := by
  have h : (fun x => sphericalExp n x R) = fun x => Real.exp (logSphericalExp n R x) := by
    ext x
    exact (Real.exp_log ((by norm_num : (0:ℝ)<1).trans_le (one_le_sphericalExp n x R))).symm
  rw [h]
  exact (logSphericalExp_lipschitz n R).continuous.rexp

def cappedSphericalExp (n : ℕ) (R Λ : ℝ) (hΛ : 1≤Λ) : Spin (n+1) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (sphericalExp n x R) Λ,(sphericalExp_continuous n R).min continuous_const⟩
    (2*Λ) (by
      intro x y
      have hx : 1 ≤ min (sphericalExp n x R) Λ := le_min (one_le_sphericalExp n x R) hΛ
      have hy : 1 ≤ min (sphericalExp n y R) Λ := le_min (one_le_sphericalExp n y R) hΛ
      change |min (sphericalExp n x R) Λ-min (sphericalExp n y R) Λ|≤2*Λ
      exact abs_le.mpr ⟨by linarith [min_le_right (sphericalExp n y R) Λ],
        by linarith [min_le_right (sphericalExp n x R) Λ]⟩)

abbrev CavityReplicaIndex (n d r : ℕ) := (Fin (n+1) ⊕ Fin d) × Fin r

def cavityVectorProjection (n d r : ℕ) (j : Fin r) :
    C(EuclideanSpace ℝ (CavityReplicaIndex n d r),Spin (n+1)) :=
  ⟨fun z => WithLp.toLp 2 (fun i => z (Sum.inl i,j)),by fun_prop⟩

def cavityReplicaTest (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    EuclideanSpace ℝ (CavityReplicaIndex n d r) →ᵇ ℝ :=
  ∏ j : Fin r,
    (cappedSphericalExp n (Real.sqrt (n+1:ℕ)) Λ hΛ).compContinuous (cavityVectorProjection n d r j) *
      ∏ t : Fin d,(expBCF 1 f).compContinuous ⟨fun z => z (Sum.inr t,j),by fun_prop⟩

def cavityBlockCovariance (n d r : ℕ) {K : ℝ} (Q : CompactArray (BulkPairRange K)) :
    Matrix (CavityReplicaIndex n d r) (CavityReplicaIndex n d r) ℝ :=
  fun i j => if i.1=j.1 then
    Sum.elim (fun _ => (Q i.2 j.2).2.val) (fun _ => (Q i.2 j.2).1.val) i.1 else 0

lemma cavityBlockCovariance_continuous (n d r : ℕ) (K : ℝ) :
    Continuous (cavityBlockCovariance n d r (K:=K)) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold cavityBlockCovariance
  split_ifs
  · cases i.1 <;> dsimp only [Sum.elim] <;> fun_prop
  · exact continuous_const

def cavityArrayKernel (n d r : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) :
    CompactArray (BulkPairRange K) →ᵇ ℝ :=
  (cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ)).compContinuous
    ⟨cavityBlockCovariance n d r,cavityBlockCovariance_continuous n d r K⟩

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGaussianReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Matrix

section

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def cavityTestReplica (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    EuclideanSpace ℝ (J×Fin r)→ᵇℝ :=
  ∏ i : Fin r, Ψ.compContinuous ⟨fun z=>WithLp.toLp 2 (fun j=>z (j,i)),by fun_prop⟩

def cavitySingleTest (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    EuclideanSpace ℝ (Fin (n+1)⊕Fin d)→ᵇℝ :=
  (cappedSphericalExp n (Real.sqrt (n+1:ℕ)) Λ hΛ).compContinuous
      ⟨fun z=>WithLp.toLp 2 (fun i=>z (Sum.inl i)),by fun_prop⟩ *
    ∏ i : Fin d,(expBCF 1 f).compContinuous ⟨fun z=>z (Sum.inr i),by fun_prop⟩

lemma cavitySingleTest_apply (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    cavitySingleTest n d f Λ hΛ z =
      min (sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i))) (Real.sqrt (n+1:ℕ))) Λ *
        ∏ i : Fin d,Real.exp (f (z (Sum.inr i))) := by
  simp [cavitySingleTest,cappedSphericalExp,expBCF]

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

abbrev CavityBulkNoiseIndex (n d m M : ℕ) :=
  (Fin (n+1) ⊕ Fin d) × (Fin M ⊕ Fin (m+1))

def cavityBulkBase (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (j : Fin (n+1)⊕Fin d) (k : Fin M⊕Fin (m+1)) : ℝ :=
  match j,k with
  | Sum.inl _,Sum.inl t => (Real.sqrt (m+1:ℕ))⁻¹*f.d1 (inner ℝ x.val (WithLp.toLp 2 (a.1 t)))
  | Sum.inr _,Sum.inr t => x.val t
  | _,_ => 0

def cavityBulkFeature (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (j : Fin (n+1)⊕Fin d) :
    EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M) :=
  WithLp.toLp 2 (fun p=>if p.1=j then cavityBulkBase n d m M f a x j p.2 else 0)

lemma cavityBulkFeature_measurable (n d m M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder (m+1) M×NormalizedSpin (m+1)=>
      cavityBulkFeature n d m M f p.1 p.2) := by
  apply Measurable.of_eval
  intro j
  unfold cavityBulkFeature
  apply (MeasurableEquiv.toLp 2 (CavityBulkNoiseIndex n d m M→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro p
  split_ifs
  · cases j <;> cases p.2 <;> dsimp [cavityBulkBase] <;> fun_prop
  · exact measurable_const

def cavityBulkPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
    (fun x=>cavitySingleTest n d f.f Λ hΛ (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) 1

lemma cavity_rows_joint_measurable {A J E : Type*} [MeasurableSpace A]
    [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {v : A→J→E} {y : A→E}
    (hv : Measurable v) (hy : Measurable y) :
    Measurable (fun a=>gaussianRows (v a) (y a)) := by
  change Measurable (fun a=>WithLp.toLp 2 (fun j=>inner ℝ (v a j) (y a)))
  apply (MeasurableEquiv.toLp 2 (J→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp hv).inner hy

lemma cavity_partition_joint_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H : A→S→ℝ) (hH : Measurable (Function.uncurry H)) (Ψ : EuclideanSpace ℝ J→ᵇℝ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H:=fun p x=>H p.1 x)
    (Y:=fun p x=>Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact Ψ.measurable.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd)

lemma cavityBulkPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkPartition n d m M f v Λ hΛ) := by
  exact cavity_partition_joint_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (bulkGibbsHamiltonian_measurable m M f.f v)
    (cavitySingleTest n d f.f Λ hΛ)

def cavityBulkMoment (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) : ℝ :=
  ∫ a,∫ y,(cavityBulkPartition n d m M f v Λ hΛ (a,y))^r
    ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∂bulkDisorderLaw (m+1) M

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavitySingleTest_bounds (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    Real.exp (-(d:ℝ)*‖f‖) ≤ cavitySingleTest n d f Λ hΛ z ∧
      cavitySingleTest n d f Λ hΛ z≤Λ*Real.exp ((d:ℝ)*‖f‖) := by
  rw [cavitySingleTest_apply,←Real.exp_sum]
  have hs : |∑ t : Fin d,f (z (Sum.inr t))|≤(d:ℝ)*‖f‖ := by
    calc
      _≤∑ t : Fin d,|f (z (Sum.inr t))| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _ : Fin d,‖f‖ := Finset.sum_le_sum fun t ht=>f.norm_coe_le_norm _
      _=_ := by simp
  have hF := le_min (one_le_sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i)))
    (Real.sqrt (n+1:ℕ))) hΛ
  constructor
  · calc
      _≤Real.exp (∑ t : Fin d,f (z (Sum.inr t))) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hs).1])
      _≤_ := by nlinarith [Real.exp_pos (∑ t : Fin d,f (z (Sum.inr t)))]
  · exact mul_le_mul (min_le_right _ _) (Real.exp_le_exp.mpr (abs_le.mp hs).2)
      (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)

abbrev CavityPartitionRange (d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) :=
  Icc (Real.exp (-(d:ℝ)*‖f‖)) (Λ*Real.exp ((d:ℝ)*‖f‖))

lemma cavityBulkPartition_mem (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    cavityBulkPartition n d m M f v Λ hΛ p∈CavityPartitionRange d f.f Λ := by
  let H:=bulkGibbsHamiltonian m M f.f v p.1
  have hmH : Measurable H := (bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left
  have he : Integrable (fun x=>Real.exp (1*H x)) (unitSphereLaw (m+1)) := by
    simpa only [one_mul,H,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v p.1
  let := tilt_law_probability_of_integrable (unitSphereLaw (m+1)) he
  let μ:=tiltLaw (unitSphereLaw (m+1)) H 1
  have hv : Measurable (cavityBulkFeature n d m M f p.1) :=
    (cavityBulkFeature_measurable n d m M f).of_uncurry_left
  have hm : Measurable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) := by
    apply (cavitySingleTest n d f.f Λ hΛ).measurable.comp
    exact cavity_rows_joint_measurable hv measurable_const
  have hi : Integrable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Λ*Real.exp ((d:ℝ)*‖f.f‖))
    filter_upwards [] with x
    have hb:=cavitySingleTest_bounds n d f.f Λ hΛ (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)
    rw [Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le hb.1)]
    exact hb.2
  unfold cavityBulkPartition
  rw [←tilt_law_integral_of_integrable (unitSphereLaw (m+1)) hmH he]
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-(d:ℝ)*‖f.f‖))) hi
        (fun x=>(cavitySingleTest_bounds n d f.f Λ hΛ _).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hi (integrable_const (Λ*Real.exp ((d:ℝ)*‖f.f‖)))
        (fun x=>(cavitySingleTest_bounds n d f.f Λ hΛ _).2)

def cavityBulkPartitionLaw (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    ProbabilityMeasure (CavityPartitionRange d f.f Λ) :=
  ⟨((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))).map
    (fun p=>⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩),
    (Measure.isProbabilityMeasure_map_iff
      ((cavityBulkPartition_measurable n d m M f v Λ hΛ).subtype_mk).aemeasurable).2 inferInstance⟩

def cavityPartitionLogTest (d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) : CavityPartitionRange d f Λ→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x=>Real.log x.val,
    continuous_subtype_val.log (fun x=>ne_of_gt ((Real.exp_pos _).trans_le x.prop.1))⟩

def cavityBulkLog (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) : ℝ :=
  ∫ a,∫ y,Real.log (cavityBulkPartition n d m M f v Λ hΛ (a,y))
    ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∂bulkDisorderLaw (m+1) M

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityBulkCompPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
    (fun x=>Real.exp ((n+1:ℕ)/2*bulkC (m+1) M f p.1.1 x)*
      cavitySingleTest n d f.f Λ hΛ (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) 1

def cavityCompensatorConstant (n d : ℕ) (f : ℝ→ᵇℝ) (Λ K : ℝ) : ℝ :=
  (Real.exp ((n+1:ℕ)/2*K)*(Λ*Real.exp ((d:ℝ)*‖f‖))/
    (Real.exp (-((n+1:ℕ)/2*K))*Real.exp (-(d:ℝ)*‖f‖)))*((n+1:ℕ)/2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CavityFiniteRPC
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev CavityRPCState (n d : ℕ) := (Fin (n+1)→ℕ→ℝ)×(Fin d→ℕ→ℝ)
abbrev CavityRPCMark (n d : ℕ) := (Fin (n+1)→ℝ)×(Fin d→ℝ)
def cavityRPCMarkLaw (n d : ℕ) : ProbabilityMeasure (CavityRPCMark n d) :=
  productMarkLaw (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
def cavityRPCStep (n d : ℕ) (σ τ : ℕ→ℝ) : CavityRPCState n d×CavityRPCMark n d→CavityRPCState n d :=
  fun p=>(canonicalCoordinateStep (n+1) σ (p.1.1,p.2.1),
    canonicalCoordinateStep d τ (p.1.2,p.2.2))
def cavityRPCTerminal (n d : ℕ) (F : ℝ→ᵇℝ) (x : CavityRPCState n d) : ℝ :=
  logSphericalExp n (Real.sqrt (n+1:ℕ)) (coordinateLeafField (n+1) x.1)+∑ i,F (x.2 i 0)


def cavityScalarRootValue (k : ℕ) (τ : ℕ→ℝ) (z : Fin k→ℝ) (t : ℝ) (F : ℝ→ᵇℝ) : ℝ :=
  ∫ b, finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
    (fun x=>F (x 0)) (fun _=>t*b) ∂(standardGaussianMark : Measure ℝ)

def cavityRPCRootState (n d : ℕ) (r t : ℝ) (b : CavityRPCMark n d) : CavityRPCState n d :=
  (fun i _=>r*b.1 i,fun i _=>t*b.2 i)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCovarianceComparison
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

variable {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]

def cavityGaussianRotation (V W : S→EuclideanSpace ℝ I) (t : ℝ) (s : S) : EuclideanSpace ℝ I :=
  Real.cos t •V s+Real.sin t •W s

def cavityGaussianRotationVelocity (V W : S→EuclideanSpace ℝ I) (t : ℝ) (s : S) : EuclideanSpace ℝ I :=
  (-Real.sin t) •V s+Real.cos t •W s

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityPerturbationCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def cavityBulkCovarianceError (n L : ℕ) (C D : ℝ) : ℝ :=
  C^2*D*(bulkScale (n+1+L)^2/(n+1:ℕ))+
    bulkScale (n+1+L)^2*((L:ℝ)*C^2*(1/2:ℝ)^(n+1+1))+
    |bulkScale (n+1+L)^2-bulkScale (n+1)^2| * C^2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianPolar
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma canonicalRadial_exp_integrable (n : ℕ) (z : Spin (n+1)) :
    Integrable (fun x => Real.exp (inner ℝ z x)) (canonicalRadialMass n 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp
  rw [canonicalRadial_linear_integral n (by norm_num)]
  exact ENNReal.ofReal_ne_top

lemma canonicalRadial_exp_integral (n : ℕ) (z : Spin (n+1)) :
    (∫ x, Real.exp (inner ℝ z x) ∂canonicalRadialMass n 1)=Real.exp (‖z‖^2/2) := by
  have h := canonicalRadial_linear_integral n (b:=1) (by norm_num) z
  rw [←ofReal_integral_eq_lintegral_ofReal (canonicalRadial_exp_integrable n z)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)] at h
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => (Real.exp_pos _).le) (Real.exp_pos _).le).mp
  simpa using h

lemma canonicalRadialMass_eq_stdGaussian (n : ℕ) :
    canonicalRadialMass n 1=stdGaussian (Spin (n+1)) := by
  apply Measure.ext_of_charFun
  funext z
  have hm : mgf (fun x => inner ℝ z x) (canonicalRadialMass n 1)=
      mgf (fun x => inner ℝ z x) (stdGaussian (Spin (n+1))) := by
    funext t
    change (∫ x, Real.exp (t*inner ℝ z x) ∂canonicalRadialMass n 1)=
      (∫ x, Real.exp (t*inner ℝ z x) ∂stdGaussian (Spin (n+1)))
    rw [integral_exp_inner_stdGaussian]
    have h := canonicalRadial_exp_integral n (t • z)
    simp only [real_inner_smul_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
    exact h
  have hs : integrableExpSet (fun x => inner ℝ z x) (canonicalRadialMass n 1)=univ := by
    apply eq_univ_of_forall
    intro t
    change Integrable (fun x => Real.exp (t*inner ℝ z x)) _
    simpa only [real_inner_smul_left] using canonicalRadial_exp_integrable n (t • z)
  have h := eqOn_complexMGF_of_mgf hm (show (Complex.I:ℂ)∈{w | w.re∈interior
    (integrableExpSet (fun x => inner ℝ z x) (canonicalRadialMass n 1))} by simp [hs])
  simpa only [complexMGF,charFun_apply,real_inner_comm z, mul_comm Complex.I] using h

def gaussianRadialWeight (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (radialNormalizer n * Real.exp (-(1/2:ℝ)*r^2))

def gaussianRadiusLaw (n : ℕ) : Measure (Ioi (0:ℝ)) :=
  (haarRadiusMeasure (volume : Measure (Spin (n+1)))).withDensity
    (fun r => gaussianRadialWeight n r)

lemma stdGaussian_polar_lintegral (n : ℕ) (f : Spin (n+1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂stdGaussian (Spin (n+1)))=
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:Spin (n+1)) 1,
        f (r.val • u.val) ∂unitSphereLaw (n+1) ∂gaussianRadiusLaw n := by
  rw [←canonicalRadialMass_eq_stdGaussian,canonicalRadialMass,
    lintegral_withDensity_eq_lintegral_mul _
      (canonicalRadialDensity_continuous n 1).measurable.ennreal_ofReal hf]
  change (∫⁻ x, gaussianRadialWeight n ‖x‖ * f x)=_
  rw [polar_weighted_lintegral volume f hf (gaussianRadialWeight n) (by unfold gaussianRadialWeight; fun_prop)]
  rw [gaussianRadiusLaw,lintegral_withDensity_eq_lintegral_mul _ (by unfold gaussianRadialWeight; fun_prop)]
  · rfl
  · exact Measurable.lintegral_prod_right (hf.comp (measurable_fst.subtype_val.smul measurable_snd.subtype_val))

instance gaussianRadiusLaw_probability (n : ℕ) : IsProbabilityMeasure (gaussianRadiusLaw n) := by
  constructor
  have h := stdGaussian_polar_lintegral n (fun _ => 1) measurable_const
  simpa using h.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBlock
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

def gaussianBlockSplit (N L : ℕ) (x : Spin (N+L)) : Spin N × Spin L :=
  (WithLp.toLp 2 (fun i => x (Fin.castAdd L i)),WithLp.toLp 2 (fun j => x (Fin.natAdd N j)))

lemma gaussianBlockSplit_norm_sq (N L : ℕ) (x : Spin (N+L)) :
    ‖x‖^2=‖(gaussianBlockSplit N L x).1‖^2+‖(gaussianBlockSplit N L x).2‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,gaussianBlockSplit,Real.norm_eq_abs,sq_abs]
  exact Fin.sum_univ_add _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def gaussianBlockJoin (N L : ℕ) (p : Spin N×Spin L) : Spin (N+L) :=
  WithLp.toLp 2 (Fin.addCases (fun i=>p.1 i) (fun j=>p.2 j))

lemma gaussianBlockSplit_join (N L : ℕ) (p : Spin N×Spin L) :
    gaussianBlockSplit N L (gaussianBlockJoin N L p)=p := by
  apply Prod.ext <;> ext i <;> simp [gaussianBlockSplit,gaussianBlockJoin]

lemma gaussianBlockJoin_norm_sq (N L : ℕ) (p : Spin N×Spin L) :
    ‖gaussianBlockJoin N L p‖^2=‖p.1‖^2+‖p.2‖^2 := by
  simpa only [gaussianBlockSplit_join] using gaussianBlockSplit_norm_sq N L (gaussianBlockJoin N L p)

def cavityRho (N L : ℕ) (z : Spin L) : ℝ := Real.sqrt (1-‖z‖^2/(N+L:ℕ))

def cavityNormalizedVec (N L : ℕ) (x : NormalizedSpin N) (z : Spin L) : Spin (N+L) :=
  gaussianBlockJoin N L (cavityRho N L z •x.val,(Real.sqrt (N+L:ℕ))⁻¹ •z)

lemma cavityNormalizedVec_norm (N L : ℕ) (x : NormalizedSpin N) (z : Spin L)
    (hD : 0<(N+L:ℕ)) (hz : ‖z‖^2≤(N+L:ℕ)) :
    ‖cavityNormalizedVec N L x z‖=1 := by
  have hDp : (0:ℝ)<(N+L:ℕ) := by exact_mod_cast hD
  have hx : ‖x.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.prop
  have hr : 0≤1-‖z‖^2/(N+L:ℕ) := sub_nonneg.mpr ((div_le_one hDp).mpr hz)
  have hsq : ‖cavityNormalizedVec N L x z‖^2=1 := by
    rw [cavityNormalizedVec,gaussianBlockJoin_norm_sq]
    simp only [norm_smul,Real.norm_eq_abs,hx,mul_one,mul_pow,sq_abs,cavityRho,
      Real.sq_sqrt hr,inv_pow,Real.sq_sqrt hDp.le]
    rw [←div_eq_inv_mul]
    ring
  nlinarith [norm_nonneg (cavityNormalizedVec N L x z)]

section Sum
variable {I J : Type} [Fintype I] [Fintype J]
def gaussianSumSplit (x : EuclideanSpace ℝ (I⊕J)) : EuclideanSpace ℝ I×EuclideanSpace ℝ J :=
  (WithLp.toLp 2 (fun i=>x (.inl i)),WithLp.toLp 2 (fun j=>x (.inr j)))
def gaussianInl (x : EuclideanSpace ℝ I) : EuclideanSpace ℝ (I⊕J) :=
  WithLp.toLp 2 (Sum.elim (fun i=>x i) (fun _=>0))
def gaussianInr (x : EuclideanSpace ℝ J) : EuclideanSpace ℝ (I⊕J) :=
  WithLp.toLp 2 (Sum.elim (fun _=>0) (fun j=>x j))
end Sum

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityDisintegration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

def cavityBlockNormalize (N L : ℕ) (p : Spin N×Spin L) : Spin N×Spin L :=
  let a := (Real.sqrt (‖p.1‖^2+‖p.2‖^2))⁻¹
  (a •p.1,a •p.2)

def cavityRadialBlock (n L : ℕ) (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) : Spin (n+1)×Spin L :=
  let a := (Real.sqrt (p.1.1.val^2+‖p.2‖^2))⁻¹
  ((a*p.1.1.val) •p.1.2.val,a •p.2)

def cavityCoupledScale (n L : ℕ) (g : ℕ→ℝ) (z : Spin L) : ℝ :=
  Real.sqrt ((n+1+L:ℕ):ℝ) / Real.sqrt ((∑ i∈Finset.range (n+1),(g i)^2)+‖z‖^2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

def cavitySphereLaw (n L : ℕ) : ProbabilityMeasure (Spin L) := by
  let : IsProbabilityMeasure (unitSphereLaw (n+1+L)) := by
    have he : n+1+L=(n+L)+1 := by omega
    rw [he]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact ⟨(unitSphereLaw (n+1+L)).map (fun u=>Real.sqrt (n+1+L:ℕ) •
    (gaussianBlockSplit (n+1) L u.val).2), (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def cavityCoupledBlock (n L : ℕ) (p : (ℕ→ℝ)×Spin L) : Spin L :=
  cavityCoupledScale n L p.1 p.2 •p.2

def cavityGaussianLaw (L : ℕ) : ProbabilityMeasure (Spin L) := ⟨stdGaussian (Spin L),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def cavityShell (L : ℕ) : Set (Spin L) := {z | (L:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤L+1}

def cavityShellMass (k : ℕ) : ℝ := (stdGaussian (Spin (k+1))).real (cavityShell (k+1))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellPerturbation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal BoundedContinuousFunction

abbrev CavityShellSpin (n L : ℕ) := NormalizedSpin (n+1) × {z : Spin L // z∈cavityShell L}

def cavityShellFeature (n L : ℕ) (v : ℕ→ℝ) (s : CavityShellSpin n L) : BulkMark (n+1+L) :=
  ambientBulkFeature (n+1+L) v (cavityNormalizedVec (n+1) L s.1 s.2.val)

def cavityShellProbability (n L : ℕ) : Measure {z : Spin L // z∈cavityShell L} :=
  (cond (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)).comap Subtype.val

def cavityShellBaseLaw (n L : ℕ) : Measure (CavityShellSpin n L) :=
  (unitSphereLaw (n+1)).prod (cavityShellProbability n L)

def cavityShellSpinEmbedding (n L : ℕ) (s : CavityShellSpin n L) : NormalizedSpin (n+1+L) :=
  ⟨cavityNormalizedVec (n+1) L s.1 s.2.val,by
    have hz : ‖s.2.val‖^2≤(n+1+L:ℕ) := s.2.prop.2.trans (by
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n])
    simpa only [Metric.mem_sphere,dist_zero_right] using
      cavityNormalizedVec_norm _ _ s.1 s.2.val (by omega) hz⟩

def cavityShellPatternEnergy (n L M : ℕ) (f : ℝ→ᵇℝ) (a : Fin M→Fin (n+1+L)→ℝ)
    (s : CavityShellSpin n L) : ℝ :=
  normalizedPatternEnergy (n+1+L) M f a (cavityShellSpinEmbedding n L s)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavitySphericalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def cavityVectorField (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (y : Fin M→Spin L) : Spin L :=
  t • ∑ i,a i • y i

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DilationExpansion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def weightedDerivative (w : ℝ→ᵇℝ) (hw : HasCompactSupport (w : ℝ→ℝ)) (k : ℕ) : ℝ→ᵇℝ :=
  ofCompactSupport (fun z => z^k*w z) ((continuous_id.pow k).mul w.continuous) hw.mul_left

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityTaylorFinite
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators

def cavityTaylorError (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (N L q v : ℝ) : ℝ :=
  let t:=Real.log (Real.sqrt (1-q/(N+L)))
  let u:=v/Real.sqrt (N+L)
  (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*t^2/2+
      ‖weightedDerivative g.d2 h2 1‖*|t| * |u|+
      ‖weightedDerivative g.d3 h3 1‖*|t| * u^2/2+‖g.d3‖*|u| ^3/6+
      |t+q/(2*N)| * ‖weightedDerivative g.d1 h1 1‖+
      |v/Real.sqrt (N+L)-v/Real.sqrt N| * ‖g.d1‖+
      |(v/Real.sqrt (N+L))^2/2-v^2/(2*N)| * ‖g.d2‖

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityUniformRemainder
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def cavityRemainderCoefficients (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (L D : ℝ) : Fin 4→ℝ := ![
  (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*D^2/2+
    (D^2+D*L/2)*‖weightedDerivative g.d1 h1 1‖,
  ‖weightedDerivative g.d2 h2 1‖*D*Real.sqrt D+Real.sqrt D*L*‖g.d1‖,
  ‖weightedDerivative g.d3 h3 1‖*D^2/2+D*L*‖g.d2‖/2,
  ‖g.d3‖*(Real.sqrt D)^3/6]

def cavityRemainderMajorant (c : Fin 4→ℝ) (N u : ℝ) : ℝ :=
  c 0/N^2+c 1*u/(N*Real.sqrt N)+c 2*u^2/N^2+c 3*u^3/(N*Real.sqrt N)


def cavityNormMoment (L p : ℕ) : ℝ := ∫ y : Spin L,‖y‖^p ∂stdGaussian (Spin L)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

def cavityJoinedPatterns (N L M : ℕ) (a : Fin M→Fin N→ℝ) (y : Fin M→Spin L) :
    Fin M→Fin (N+L)→ℝ := fun i=>Fin.addCases (a i) (fun j=>y i j)

def cavityShellTaylorModel (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (y : Fin M→Spin L) (s : CavityShellSpin n L) : ℝ :=
  normalizedPatternEnergy (n+1) M f.f a s.1+
    (cavityLinearField M L (fun i=>f.d1 (∑ j,a i j*s.1.val j))
      (Real.sqrt (n+1:ℕ))⁻¹ s.2.val y+
      ‖s.2.val‖^2/2*bulkC (n+1) M f a s.1+
      cavityQuadraticField M L (fun i=>f.d2 (∑ j,a i j*s.1.val j))
        (1/(2*(n+1:ℕ))) s.2.val y)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBlockProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

def cavityRadialUnit (_n L : ℕ) (p : Ioi (0:ℝ)×Spin L) : Spin L :=
  (Real.sqrt (p.1.val^2+‖p.2‖^2))⁻¹ •p.2

lemma cavityRadialUnit_measurable (n L : ℕ) : Measurable (cavityRadialUnit n L) := by
  unfold cavityRadialUnit
  fun_prop

def cavityUnitEmbed (n L : ℕ) (p : Metric.sphere (0:Spin (n+1)) 1×Spin L) : Spin (n+1)×Spin L :=
  (Real.sqrt (1-‖p.2‖^2) •p.1.val,p.2)

def cavityUnitLaw (n L : ℕ) : ProbabilityMeasure (Spin L) :=
  ⟨((gaussianRadiusLaw n).prod (stdGaussian (Spin L))).map (cavityRadialUnit n L),
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact (cavityRadialUnit_measurable n L).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def cavitySphereBlockEmbed (n L : ℕ) (p : Metric.sphere (0:Spin (n+1)) 1×Spin L) : Spin (n+1)×Spin L :=
  cavityUnitEmbed n L (p.1,(Real.sqrt (n+1+L:ℕ))⁻¹ •p.2)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellPolar
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

abbrev PositiveRadius : Type := ↥(Ioi (0:ℝ))

def cavityPolarRadius (n k : ℕ) (p : PositiveRadius×PositiveRadius) : PositiveRadius :=
  ⟨Real.sqrt (n+1+(k+1):ℕ) * (Real.sqrt (p.1.val^2+p.2.val^2))⁻¹*p.2.val,by
    change 0 < Real.sqrt (n+1+(k+1):ℕ) * (Real.sqrt (p.1.val^2+p.2.val^2))⁻¹*p.2.val
    have hr : 0<p.1.val := p.1.prop
    have hq : 0<p.2.val := p.2.prop
    positivity⟩

lemma cavityPolarRadius_measurable (n k : ℕ) : Measurable (cavityPolarRadius n k) := by
  unfold cavityPolarRadius
  fun_prop

def cavityRadiusLaw (n k : ℕ) : ProbabilityMeasure PositiveRadius :=
  ⟨((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)).map (cavityPolarRadius n k),
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact (cavityPolarRadius_measurable n k).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def cavityRadiusShell (k : ℕ) : Set PositiveRadius :=
  {r | (k+1:ℕ) ≤ r.val^2 ∧ r.val^2≤(k+1:ℕ)+1}

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityConditionalIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityOldIncrement (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (W : NormalizedSpin (n+1)→ℝ) (y : Fin M→Spin L) (p : CavityShellSpin n L) : ℝ :=
  cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M a y) p-
    normalizedPatternEnergy (n+1) M f.f a p.1+W p.1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityNormalizedIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

def cavityOldJoinedHamiltonian (n L M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (W : NormalizedSpin (n+1)→ℝ)
    (y : Fin M→Spin L) (p : CavityShellSpin n L) : ℝ :=
  cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M a.1 y) p+
    inner ℝ (bulkFeature (n+1) v p.1) a.2+W p.1

def cavityCountableField {S J : Type*} [Fintype J] (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (g : ℕ→ℝ) (x : S) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j=>countableGaussianField v L g (x,j))

lemma cavityCountableField_measurable {S J : Type*} [MeasurableSpace S]
    [Fintype J] [MeasurableSpace J] (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (hv : ∀ i,Measurable (v i)) (hL : Measurable L) :
    Measurable (fun p : (ℕ→ℝ)×S=>cavityCountableField v L p.1 p.2) := by
  apply (MeasurableEquiv.toLp 2 (J→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro j
  exact (countableGaussianField_measurable hv hL).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityDiagonalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

section

variable {I : Type} [Fintype I] [DecidableEq I]

def cavityDiagonalAverage (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) : EuclideanSpace ℝ I→ᵇℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x=>∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I),by
      apply continuous_of_dominated (bound:=fun _=>‖Ψ‖)
      · intro x
        have hm : Measurable (fun z : EuclideanSpace ℝ I=>Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i))) := by fun_prop
        exact (Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun z=>Ψ.norm_coe_le_norm _)).aestronglyMeasurable
      · intro x
        exact ae_of_all _ fun z=>Ψ.norm_coe_le_norm _
      · exact integrable_const _
      · exact ae_of_all _ fun z=>by fun_prop⟩
    (2*‖Ψ‖) (by
      intro x y
      have hx : ‖∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I)‖≤‖Ψ‖ :=
        by simpa using (norm_integral_le_of_norm_le_const (μ:=stdGaussian (EuclideanSpace ℝ I))
          (ae_of_all _ fun z=>Ψ.norm_coe_le_norm (WithLp.toLp 2 (fun i=>x i+σ i*z i))))
      have hy : ‖∫ z,Ψ (WithLp.toLp 2 (fun i=>y i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I)‖≤‖Ψ‖ :=
        by simpa using (norm_integral_le_of_norm_le_const (μ:=stdGaussian (EuclideanSpace ℝ I))
          (ae_of_all _ fun z=>Ψ.norm_coe_le_norm (WithLp.toLp 2 (fun i=>y i+σ i*z i))))
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by dsimp only [ContinuousMap.coe_mk]; linarith))

def cavityNoiseRows {n : ℕ} (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ) (i : I) :
    EuclideanSpace ℝ (Fin n⊕I) :=
  WithLp.toLp 2 (Sum.elim (fun j=>v i j) (fun j=>if j=i then σ i else 0))

end

variable {J : Type} [Fintype J] [DecidableEq J]

def cavityReplicaSplit (r : ℕ) (z : EuclideanSpace ℝ (J×Fin r)) :
    Fin r→EuclideanSpace ℝ J := fun i=>WithLp.toLp 2 (fun j=>z (j,i))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CavityCappedRPC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityDiagonalAverage_bounds {I : Type} [Fintype I] [DecidableEq I]
    (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) {a b : ℝ}
    (ha : ∀ z,a≤Ψ z) (hb : ∀ z,Ψ z≤b) (x : EuclideanSpace ℝ I) :
    a ≤ cavityDiagonalAverage σ Ψ x ∧ cavityDiagonalAverage σ Ψ x≤b := by
  have hm : Measurable (fun z : EuclideanSpace ℝ I=>Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i))) := by fun_prop
  have hi : Integrable (fun z : EuclideanSpace ℝ I=>Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)))
      (stdGaussian (EuclideanSpace ℝ I)) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun z=>Ψ.norm_coe_le_norm _)
  change a≤∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I) ∧
    (∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I))≤b
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const a) hi (fun z=>ha _)
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const b) (fun z=>hb _)

lemma cavityResidualCapped_bounds (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (x : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    Real.exp (-(d:ℝ)*‖f‖) ≤ cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x ∧
      cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x≤Λ*Real.exp ((d:ℝ)*‖f‖) :=
  cavityDiagonalAverage_bounds σ _ (fun z=>(cavitySingleTest_bounds n d f Λ hΛ z).1)
    (fun z=>(cavitySingleTest_bounds n d f Λ hΛ z).2) x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedTangentCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff NNReal

def nonnegativeSpinTime (q : CompactOverlap) : Time :=
  ⟨max q.val 0,le_max_right _ _,max_le q.property.2 zero_le_one⟩
lemma nonnegativeSpinTime_continuous : Continuous nonnegativeSpinTime := by
  unfold nonnegativeSpinTime
  fun_prop

def markedTimeLaw (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    ProbabilityMeasure (CompactArray Time) :=
  compactMapLaw (fun p : BulkPairRange K=>nonnegativeSpinTime p.1)
    (nonnegativeSpinTime_continuous.comp continuous_fst) μ

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_ContinuousCavityProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def continuousCavityProfile (μ : Measure Time) (B : ℝ) {K d : ℝ}
    (hd0 : 0 ≤ d) (hdK : d ≤ K) (r : Time) : BulkPairRange K :=
  (⟨r.val, (by linarith [r.prop.1]), r.prop.2⟩,
    ⟨min d (max 0 (cappedA μ B r)), by
      constructor
      · have hm := le_min hd0 (le_max_left 0 (cappedA μ B r))
        linarith
      · exact (min_le_left _ _).trans hdK⟩)

def cavityTrueDiagonal {K d : ℝ} (hd0 : 0 ≤ d) (hdK : d ≤ K) : BulkPairRange K :=
  (⟨1,by norm_num⟩,⟨d,by constructor <;> linarith⟩)

lemma continuousCavityProfile_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B K d : ℝ} (hB : B < 1) (hd0 : 0 ≤ d) (hdK : d ≤ K) :
    Continuous (continuousCavityProfile μ B hd0 hdK) := by
  have hc : Continuous (fun r : Time => cappedA μ B r.val) :=
    (cappedA_continuous μ hB).comp continuous_subtype_val
  exact (continuous_subtype_val.subtype_mk _).prodMk
    ((continuous_const.min (continuous_const.max hc)).subtype_mk _)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_RootPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def RootPartitionMatch {I A B : Type*} {J : I → Type*}
    (xs : (Σ i, J i) → A × B) : Prop :=
  ∀ u v, (xs u).1 = (xs v).1 ↔ u.1 = v.1

def rootPartitionEncode {I A B : Type*} {J : I → Type*}
    (a : I ↪ A) (bs : (Σ i, J i) → B) : (Σ i, J i) → A × B :=
  fun x => (a x.1, bs x)

lemma rootPartitionEncode_matches {I A B : Type*} {J : I → Type*}
    (a : I ↪ A) (bs : (Σ i, J i) → B) :
    RootPartitionMatch (rootPartitionEncode a bs) := by
  intro u v
  exact a.injective.eq_iff

def rootPartitionEquiv {I A B : Type*} {J : I → Type*}
    [∀ i, Nonempty (J i)] :
    ((I ↪ A) × ((Σ i, J i) → B)) ≃
      {xs : (Σ i, J i) → A × B // RootPartitionMatch xs} := by
  classical
  let f : ((I ↪ A) × ((Σ i, J i) → B)) →
      {xs : (Σ i, J i) → A × B // RootPartitionMatch xs} :=
    fun ab => ⟨rootPartitionEncode ab.1 ab.2, rootPartitionEncode_matches ab.1 ab.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro ab cd h
    have he := congrArg Subtype.val h
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun xs => (xs ⟨i, Classical.choice inferInstance⟩).1) he
    · funext x
      exact congrArg (fun xs => (xs x).2) he
  · rintro ⟨xs, hx⟩
    let a : I ↪ A := ⟨(fun i => (xs ⟨i, Classical.choice inferInstance⟩).1), by
      intro i j hij
      exact (hx ⟨i, Classical.choice inferInstance⟩ ⟨j, Classical.choice inferInstance⟩).mp hij⟩
    refine ⟨(a, fun x => (xs x).2), Subtype.ext ?_⟩
    funext x
    apply Prod.ext
    · change (xs ⟨x.1, Classical.choice inferInstance⟩).1 = (xs x).1
      exact (hx _ _).mpr rfl
    · rfl

@[simp] lemma rootPartitionEquiv_apply {I A B : Type*} {J : I → Type*}
    [∀ i, Nonempty (J i)] (a : I ↪ A) (bs : (Σ i, J i) → B) :
    (rootPartitionEquiv (a,bs)).val = rootPartitionEncode a bs := rfl

def excludedBlockSum {A B : Type*} (label : A → B) :
    List (A → ℝ≥0∞) → {m : ℕ} → (Fin m → B) → ℝ≥0∞
  | [], _, _ => 1
  | f::fs, _, v => ∑' a, if ∃ j, v j = label a then 0 else
      f a * excludedBlockSum label fs (Fin.cons (label a) v)

def DistinctAssignmentGood {A B : Type*} (label : A → B)
    {n m : ℕ} (a : Fin n → A) (v : Fin m → B) : Prop :=
  Function.Injective (label ∘ a) ∧ ∀ i j, v j ≠ label (a i)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DepthLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

def indexedInfiniteLeafMeasure (k : ℕ) (z : Fin k → ℝ) :
    Measure (IndexedCascadeBase k × (ℕ → IndexedLeaf k)) :=
  (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) ⊗ₘ
    kernelInfiniteReplica (indexedLeafKernel k) ℕ

instance indexedInfiniteLeafMeasure_probability (k : ℕ) (z : Fin k → ℝ) :
    IsProbabilityMeasure (indexedInfiniteLeafMeasure k z) := by
  unfold indexedInfiniteLeafMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def indexedDepthArray (k : ℕ) (xs : ℕ → IndexedLeaf k) : FiniteOverlap (Fin (k+1)) :=
  fun i j => indexedCommonDepth k (xs i) (xs j)

lemma indexedDepthArray_measurable (k : ℕ) : Measurable (indexedDepthArray k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun xs : ℕ → IndexedLeaf k => indexedCommonDepth k (xs i) (xs j))
  have hf : Measurable (fun p : IndexedLeaf k × IndexedLeaf k => indexedCommonDepth k p.1 p.2) :=
    measurable_of_countable _
  have hg : Measurable (fun xs : ℕ → IndexedLeaf k => (xs i,xs j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact hf.comp hg

def indexedDepthLaw (k : ℕ) (z : Fin k → ℝ) : ProbabilityMeasure (FiniteOverlap (Fin (k+1))) :=
  ⟨(indexedInfiniteLeafMeasure k z).map (fun a => indexedDepthArray k a.2),
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact ((indexedDepthArray_measurable k).comp measurable_snd).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def CascadeShapeReplicas : (n : ℕ) → CascadeVisitShape n → Type
  | 0, r => Fin r
  | n + 1, ss => Σ i : Fin ss.length, CascadeShapeReplicas n ss[i]

instance cascadeShapeReplicas_fintype (n : ℕ) (s : CascadeVisitShape n) :
    Fintype (CascadeShapeReplicas n s) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin s))
  | succ n ih =>
    letI (i : Fin s.length) := ih s[i]
    exact inferInstanceAs (Fintype (Σ i : Fin s.length, CascadeShapeReplicas n s[i]))

def cascadeShapeLeaves : (n : ℕ) → (s : CascadeVisitShape n) →
    CascadeShapeReplicas n s → IndexedLeaf n
  | 0, _, _ => ()
  | n + 1, ss, i => (i.1.val, 0, cascadeShapeLeaves n ss[i.1] i.2)

def cascadeShapeReplicasOfFnEquiv (n m : ℕ) (s : Fin m → CascadeVisitShape n) :
    (Σ i : Fin m, CascadeShapeReplicas n (s i)) ≃
      CascadeShapeReplicas (n + 1) (List.ofFn s) := by
  change (Σ i : Fin m, CascadeShapeReplicas n (s i)) ≃
    (Σ i : Fin (List.ofFn s).length, CascadeShapeReplicas n (List.ofFn s)[i])
  refine Equiv.sigmaCongr (finCongr (List.length_ofFn).symm) (fun i => ?_)
  exact Equiv.cast (by simp)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ShapeProbability
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

def CascadeShapeMatches : (n : ℕ) → (s : CascadeVisitShape n) →
    (CascadeShapeReplicas n s → IndexedLeaf n) → Prop
  | 0, _, _ => True
  | n+1, ss, xs =>
      RootPartitionMatch (fun u => (((xs u).1, (xs u).2.1), (xs u).2.2)) ∧
        ∀ i : Fin ss.length, CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2.2)

def indexedActiveRootEmbedding (n : ℕ) (b : IndexedCascadeBase (n+1)) :
    (Σ i, Fin ((b i).1)) ↪ ℕ × ℕ where
  toFun a := (a.1, a.2.val)
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    obtain ⟨hik, hjl⟩ := Prod.mk.inj he
    change i = k at hik
    subst k
    have hj : j = l := Fin.ext hjl
    subst l
    rfl

def indexedActiveLeafEmbedding (n : ℕ) (b : IndexedCascadeBase (n+1)) :
    ((Σ i, Fin ((b i).1)) × IndexedLeaf n) ↪ IndexedLeaf (n+1) where
  toFun t := (t.1.1, t.1.2.val, t.2)
  inj' := by
    intro u v he
    apply Prod.ext
    · apply (indexedActiveRootEmbedding n b).injective
      exact congrArg (fun t : IndexedLeaf (n+1) => (t.1,t.2.1)) he
    · exact congrArg (fun t : IndexedLeaf (n+1) => t.2.2) he

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedShapeVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (s : CascadeVisitShape n) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    (∏ i, indexedTiltedProbability step n F p (xs i)) *
      if CascadeShapeMatches n s xs then 1 else 0

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Shape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

def trivialDecoratedShape (X : Type) : (n : ℕ) → CascadeVisitShape n → DecoratedVisitShape X n
  | 0, s => (s,fun _ => 1)
  | n+1, ss => ss.map (trivialDecoratedShape X n)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DecoratedFocus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def decoratedFocusedProbability (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → X×S → ℝ) → ℕ →
      CascadeVisitShape n → X×DecoratedCascade S n → ℝ≥0∞
  | n, z, F, 0, s, p => decoratedShapeProbability ν step n z F (trivialDecoratedShape X n s) p
  | 0, _, _, _+1, _, _ => 0
  | _+1, _, _, _+1, [], _ => 0
  | n+1, z, F, d+1, s::ss, p => markedBlockProbability
      ((cascadeVisitCount n s+1, fun t : S×DecoratedCascade S n =>
        decoratedFocusedProbability ν step n (fun i => z i.succ) (fun i => F i.succ) d s
          (step (p.1,t.1),t.2)) ::
      ss.map (fun t => (cascadeVisitCount n t,fun u : S×DecoratedCascade S n =>
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
          (trivialDecoratedShape X n t) (step (p.1,u.1),u.2))))
      ((markedStableCountKernel p.2).map (fun t : ℝ×(S×DecoratedCascade S n) =>
        (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2))) (Fin.elim0 : Fin 0 → ℝ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ShapeSampleLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical ENNReal NNReal BigOperators Topology

def indexedSampleShape (n : ℕ) (s : CascadeVisitShape n) (b : IndexedCascadeBase n) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    (∏ i, (indexedLeafProbability n b) {xs i}) *
      if CascadeShapeMatches n s xs then 1 else 0

def cascadeShapeFocus : (n : ℕ) → (s : CascadeVisitShape n) → s.Valid n →
    CascadeShapeReplicas n s
  | 0, s, hs => ⟨0,hs⟩
  | n+1, ss, hs =>
    let hlen := List.length_pos_iff.mpr hs.1
    ⟨⟨0,hlen⟩, cascadeShapeFocus n ss[0] (hs.2 _ (List.getElem_mem hlen))⟩

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedClassMass (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (d : ℕ) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (l : IndexedLeaf n) : ℝ≥0∞ :=
  ∑' m : IndexedLeaf n, indexedTiltedProbability step n F p m *
    if d ≤ (indexedCommonDepth n l m).val then 1 else 0

def indexedFocusedVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    ((∏ i, indexedTiltedProbability step n F p (xs i)) *
      if CascadeShapeMatches n s xs then 1 else 0) *
        indexedClassMass step n F d p (xs (cascadeShapeFocus n s hs))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FocusedSampleLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

def indexedSampleFocused (n d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n)
    (b : IndexedCascadeBase n) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    ((∏ i, (indexedLeafProbability n b) {xs i}) *
      if CascadeShapeMatches n s xs then 1 else 0) *
        ∑' l : IndexedLeaf n, (indexedLeafProbability n b) {l} *
          if d ≤ (indexedCommonDepth n (xs (cascadeShapeFocus n s hs)) l).val then 1 else 0

def cascadeFocusCount (n d : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n) : ℝ :=
  ∑ i : CascadeShapeReplicas n s,
    if d ≤ (indexedCommonDepth n (cascadeShapeLeaves n s (cascadeShapeFocus n s hs))
      (cascadeShapeLeaves n s i)).val then 1 else 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BlockFocus
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

def indexedBlockSample {I : Type} [Fintype I] (k : ℕ)
    (A : I → I → Fin (k+1)) (b : IndexedCascadeBase k) : ℝ≥0∞ :=
  ∑' xs : I → IndexedLeaf k, (∏ i, (indexedLeafProbability k b) {xs i}) *
    if (fun i j => indexedCommonDepth k (xs i) (xs j)) = A then 1 else 0

def indexedBlockFocused {I : Type} [Fintype I] (k d : ℕ)
    (A : I → I → Fin (k+1)) (i₀ : I) (b : IndexedCascadeBase k) : ℝ≥0∞ :=
  ∑' xs : I → IndexedLeaf k, ((∏ i, (indexedLeafProbability k b) {xs i}) *
    if (fun i j => indexedCommonDepth k (xs i) (xs j)) = A then 1 else 0) *
      ∑' l : IndexedLeaf k, (indexedLeafProbability k b) {l} *
        if d ≤ (indexedCommonDepth k (xs i₀) l).val then 1 else 0

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelMoment
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

variable {J : Type} [Fintype J] [DecidableEq J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {k : ℕ}

def cavityLabelBasis (j : J) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun i=>if i=j then (1:ℝ) else 0)

def cavityLabelRow (q : Fin (k+1)→J→ℝ) (i : ℕ) (x : IndexedLeaf k×J) : ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q))
    cavityLabelBasis i (x.2,x.1)

def cavityLabelLength (k : ℕ) (x : IndexedLeaf k×J) : ℕ :=
  indexedGaussianRowLength (I:=J) k (x.2,x.1)

lemma cavityLabelRow_measurable (q : Fin (k+1)→J→ℝ) (i : ℕ) :
    Measurable (cavityLabelRow q i) :=
  (indexedGaussianRow_measurable k _ (measurable_of_countable cavityLabelBasis) i).comp
    (measurable_snd.prodMk measurable_fst)

omit [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma cavityLabelLength_measurable [Fintype J] [DecidableEq J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (k : ℕ) : Measurable (cavityLabelLength (J:=J) k) :=
  (indexedGaussianRowLength_measurable k).comp (measurable_snd.prodMk measurable_fst)


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

instance cavityIndexMeasurableSingleton (n d : ℕ) : MeasurableSingletonClass (Fin (n+1)⊕Fin d) where
  measurableSet_singleton x := by
    cases x with
    | inl x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inl_image (β:=Fin d)
    | inr x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inr_image (α:=Fin (n+1))

def cavityLabelPartition (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) : ℝ :=
  ∫ l,cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
    (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l)
    ∂indexedLeafProbability k p.1

lemma cavityLabelPartition_measurable (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityLabelPartition n d k f Λ hΛ σ q) := by
  let κ : Kernel (IndexedCascadeBase k×(ℕ→ℝ)) (IndexedLeaf k):=
    (indexedLeafKernel k).comap Prod.fst measurable_fst
  have hf : Measurable (fun p : (ℕ→ℝ)×IndexedLeaf k=>
      cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1 p.2) :=
    cavityCountableField_measurable (cavityLabelRow q) (cavityLabelLength k)
      (cavityLabelRow_measurable q) (cavityLabelLength_measurable k)
  have hp : Measurable (fun p : (IndexedCascadeBase k×(ℕ→ℝ))×IndexedLeaf k=>(p.1.2,p.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hg:=hf.comp hp
  have hm : Measurable (fun p : (IndexedCascadeBase k×(ℕ→ℝ))×IndexedLeaf k=>
      cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
        (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1.2 p.2)) :=
    (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)).measurable.comp hg
  exact (hm.stronglyMeasurable.integral_kernel_prod_right (κ:=κ)
    (f:=fun p l=>cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
      (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l))).measurable

lemma cavityLabelPartition_mem (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) :
    cavityLabelPartition n d k f Λ hΛ σ q p∈CavityPartitionRange d f Λ := by
  let Ψ:=cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
  have hm : Measurable (fun l=>Ψ (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l)) :=
    measurable_of_countable _
  have hi : Integrable (fun l=>Ψ (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l))
      (indexedLeafProbability k p.1) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun l=>Ψ.norm_coe_le_norm _)
  unfold cavityLabelPartition
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const (Real.exp (-(d:ℝ)*‖f‖))) hi
        (fun l=>(cavityResidualCapped_bounds n d f Λ hΛ σ _).1)
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const (Λ*Real.exp ((d:ℝ)*‖f‖)))
        (fun l=>(cavityResidualCapped_bounds n d f Λ hΛ σ _).2)

def cavityLabelPartitionLaw (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (z : Fin k→ℝ) :
    ProbabilityMeasure (CavityPartitionRange d f Λ) :=
  ⟨((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw).map
    (fun p=>⟨cavityLabelPartition n d k f Λ hΛ σ q p,cavityLabelPartition_mem n d k f Λ hΛ σ q p⟩),
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | exact (cavityLabelPartition_measurable n d k f Λ hΛ σ q).subtype_mk.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩


def cavityIndexedRootPartition (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)×
      (IndexedCascadeBase k×IndexedCascadeMarks (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) k)) : ℝ :=
  ∫ l,cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
    (indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
      ((fun _=>diagonalMark (profileGaussianRoot q) p.1),p.2.2) l 0)
    ∂indexedLeafProbability k p.2.1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

 def cavityLabelMarkedArray {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) (xs : ℕ→IndexedLeaf k) : CompactArray (BulkPairRange K) :=
  fun i j=>if i=j then D else p (indexedCommonDepth k (xs j) (xs i))

lemma cavityLabelMarkedArray_measurable {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) : Measurable (cavityLabelMarkedArray p D) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold cavityLabelMarkedArray
  split_ifs
  · exact measurable_const
  · have hf : Measurable (fun x : IndexedLeaf k×IndexedLeaf k=>p (indexedCommonDepth k x.1 x.2)) :=
      measurable_of_countable _
    have hg : Measurable (fun xs : ℕ→IndexedLeaf k=>(xs j,xs i)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply i)
    exact hf.comp hg

lemma cavityLabelZero_measurable (k : ℕ) :
    Measurable (Function.uncurry (fun _ : IndexedCascadeBase k=>fun _ : IndexedLeaf k=>(0:ℝ))) :=
  measurable_const

def cavityLabelMarkedLaw {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) (z : Fin k→ℝ) : ProbabilityMeasure (CompactArray (BulkPairRange K)) := by
  let μ : Measure (IndexedCascadeBase k×(ℕ→IndexedLeaf k)) :=
    annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k)
  have : IsProbabilityMeasure μ := by
    have : IsMarkovKernel (gibbsProbabilityKernel (indexedLeafKernel k) (fun _ _=>0)) :=
      gibbsProbabilityKernel_markov (indexedLeafKernel k) (fun _ _=>0) (cavityLabelZero_measurable k)
    dsimp [μ]
    unfold annealedInfiniteReplicaMeasure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (fun a : IndexedCascadeBase k×(ℕ→IndexedLeaf k)=>cavityLabelMarkedArray p D a.2) :=
    (cavityLabelMarkedArray_measurable p D).comp measurable_snd
  exact ⟨μ.map (fun a=>cavityLabelMarkedArray p D a.2),
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance⟩

def cavityPairProfile (n d : ℕ) {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K) :
    Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ :=
  fun l=>Sum.elim (fun _=>(p l).2.val) (fun _=>(p l).1.val)

def cavityPairDiagonal (n d : ℕ) {K : ℝ} (D : BulkPairRange K) :
    (Fin (n+1)⊕Fin d)→ℝ := Sum.elim (fun _=>D.2.val) (fun _=>D.1.val)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_OrderedCode
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

variable {K L : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

def finiteCodeArray (χ : K → L) (Q : CompactArray K) :
    FiniteOverlap L := fun i j => χ (Q i j)

def finiteCodeBlock {n : ℕ} (χ : K → L) (Q : CompactBlock K n) :
    FiniteBlock L n := fun i j => χ (Q i j)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RoundedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

def depthMarkedDecode {K : Type*} {k : ℕ} (p : Fin (k+1) → K) (D : K)
    (R : FiniteOverlap (Fin (k+1))) : CompactArray K :=
  fun i j => if i = j then D else p (R i j)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_MarkedGraphLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev markedTimePair (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) : Measure Time :=
  (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q => Q 0 1)

instance markedTimePair_isProbability (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    IsProbabilityMeasure (markedTimePair K μ) :=
  (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCountableIsotropic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

section

variable {S : Type} [MeasurableSpace S]

def cavityCompletedCountableVector (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S)
    (p : (ℕ→ℝ)×Spin (n+1)) : Spin (n+1) :=
  WithLp.toLp 2 (fun i=>countableGaussianField v L p.1 (xs i)+σ i*p.2 i)

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityResidualUncap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy



def cavityLabelCompletedMark (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : (ℕ→ℝ)×(IndexedLeaf k×EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) :
    EuclideanSpace ℝ (Fin (n+1)⊕Fin d) :=
  WithLp.toLp 2 (fun i=>cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1 p.2.1 i+σ i*p.2.2 i)

def cavityLabelSpherical (n d k : ℕ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :=
  fun p=>sphericalExp n ((gaussianSumSplit (cavityLabelCompletedMark n d k σ q p)).1) (Real.sqrt (n+1:ℕ))

def cavityLabelWeight (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :=
  fun p=>∑ i : Fin d,f (cavityLabelCompletedMark n d k σ q p (Sum.inr i))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityLabelAnnealed
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityLabelFullPartition (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) : ℝ :=
  ∫ x,Real.exp (cavityLabelWeight n d k f σ q (p.2,x))*cavityLabelSpherical n d k σ q (p.2,x)
    ∂(indexedLeafProbability k p.1).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityResidualFormula
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityFullSingle (n d : ℕ) (f : ℝ→ᵇℝ)
    (v : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) : ℝ :=
  sphericalExp n (gaussianSumSplit v).1 (Real.sqrt (n+1:ℕ))*Real.exp (∑ i,f (v (Sum.inr i)))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedFractionalLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

def indexedRootTerminalPartition {X S Y : Type} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace Y]
    (step : X×S→X) (H : X→ℝ) (root : Y→X) (k : ℕ)
    (p : Y×(IndexedCascadeBase k×IndexedCascadeMarks S k)) : ℝ :=
  ∫ l,Real.exp (H (indexedLeafState step k (root p.1,p.2.2) l)) ∂indexedLeafProbability k p.2.1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGaussianTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal

def cavityGaussianMark (n d : ℕ) (y : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) : CavityRPCMark n d :=
  (fun i=>y (Sum.inl i),fun i=>y (Sum.inr i))

def cavityGaussianState (n d : ℕ) (x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) : CavityRPCState n d :=
  (fun i j=>x j (Sum.inl i),fun i j=>x j (Sum.inr i))

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

def roundedCavityPair (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ)
    {K a : ℝ} (ha0 : 0 ≤ a) (haK : a ≤ K) (j : ℕ) :
    Fin ((strictRoundModel (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j).depth+1) → BulkPairRange K :=
  fun i => continuousCavityProfile η B ha0 haK
    (roundTimeValue (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j i)

def roundedCavityLog (n d : ℕ) (f : ℝ →ᵇ ℝ) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) {K a : ℝ}
    (ha0 : 0 ≤ a) (haK : a ≤ K) (j : ℕ) : ℝ :=
  let F := unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let k := (strictRoundModel F j).depth
  let p := roundedCavityPair η B ha0 haK j
  let D := cavityTrueDiagonal ha0 haK
  ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
    (gaussianLinearMarkStep (fun l=>diagonalMark (profileGaussianStep (cavityPairProfile n d p) l))) k
    (stepCumulative (strictRoundModel F j).weight)
    (fun t=>Real.log (cavityDiagonalAverage
      (fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i))
      (cavitySingleTest n d f Λ hΛ) (t 0)))
    (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d p)) y)
    ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CappedAContinuity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cappedAError (μ ν : Measure Time) (B : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1,|cappedDensity μ B t-cappedDensity ν B t|

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

def cavityProfileMoment (η : Measure Time) (B : ℝ) : ℝ :=
  ∫ r : Time,(r:ℝ)*cappedA η B r/2 ∂η

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCavityData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

structure BulkCavityData (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (α K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) where
  a : ℝ
  c : ℝ
  a_nonneg : 0≤a
  a_le_K : a≤K
  a_le : a≤α*‖g.d1‖^2
  c_bound : |c|≤α*‖g.dilationMark hg‖
  a_L2 : Tendsto (fun j=>bulkReplicaMean (s j) (M (s j)+2) g.f (v (s j)) 1
    (fun b x=>(bulkB (s j+1) (M (s j)+2) g b.1 (x 0) (x 0)-a)^2)) atTop (𝓝 0)
  c_L2 : Tendsto (fun j=>bulkReplicaMean (s j) (M (s j)+2) g.f (v (s j)) 1
    (fun b x=>(bulkC (s j+1) (M (s j)+2) g b.1 (x 0)-c)^2)) atTop (𝓝 0)
  support : ∀ᵐ r : Time ∂markedTimePair K μ,(r:ℝ)≤(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  field_bound : ∀ᵐ r : Time ∂markedTimePair K μ,
    cappedA (markedTimePair K μ) ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)) r≤a
  radial : (c+a)/2=cavityProfileMoment (markedTimePair K μ) ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2))
  capped : ∀ n d (Λ : ℝ) (hΛ : 1≤Λ),
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)+2) g (v (s j)) Λ hΛ-
      roundedCavityLog n d g.f Λ hΛ (markedTimePair K μ)
        ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)) a_nonneg a_le_K j) atTop (𝓝 0)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityMeanCap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

def cavityBulkFullCompPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
    (fun x=>Real.exp ((n+1:ℕ)/2*bulkC (m+1) M f p.1.1 x+
      ∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f p.1 x (Sum.inr t)) p.2))*
      sphericalExp n (gaussianRows (fun i=>cavityBulkFeature n d m M f p.1 x (Sum.inl i)) p.2)
        (Real.sqrt (n+1:ℕ))) 1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityAnnealedUncap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityBulkUncapError (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  Real.log (cavityBulkFullCompPartition n d m M f v p)-
    Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityExpectedCompensator
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkCDefect (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c : ℝ)
    (a : BulkDisorder (m+1) M) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a)
    (fun x=>|bulkC (m+1) M f a.1 x-c|) 1

def cavityBulkCompError (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) (c : ℝ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)-
    ((n+1:ℕ)/2*c+Real.log (cavityBulkPartition n d m M f v Λ hΛ p))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianCoordinateProjection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace SphericalPerceptronFreeEnergy

def cavityBulkNoiseSplit (n d m M : ℕ)
    (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ) :=
  (fun t=>WithLp.toLp 2 (fun i=>y (Sum.inl i,Sum.inl t)),
    fun t i=>y (Sum.inr t,Sum.inr i))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkUncappedLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

def cavityBulkFullLog (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) : ℝ :=
  ∫ p,Real.log (cavityBulkFullCompPartition n d m M f v p)
    ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))

def cavityBulkNoiseJoin (n d m M : ℕ)
    (p : (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ)) :
    EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M) :=
  WithLp.toLp 2 (fun j=> match j with
    | (Sum.inl i,Sum.inl t)=>p.1 t i
    | (Sum.inr t,Sum.inr i)=>p.2 t i
    | _=>0)

def cavitySplitPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : BulkDisorder (m+1) M×((Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ))) : ℝ :=
  ∫ x,Real.exp (normalizedPatternEnergy (m+1) d f.f p.2.2 x+
    (n+1:ℕ)*bulkC (m+1) M f p.1.1 x/2)*
    sphericalExp n (cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,p.1.1 t i*x.val i))
      (Real.sqrt (m+1:ℕ))⁻¹ p.2.1) (Real.sqrt (n+1:ℕ))
    ∂tiltLaw (unitSphereLaw (m+1)) (bulkHamiltonian (m+1) M f.f v p.1.1 p.1.2) 1

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCounts
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityOmittedCount (α : ℝ) (n : ℕ) : ℕ := patternCount α (n+1)-2

def cavityFreshCount (α : ℝ) (n L : ℕ) : ℕ := patternCount α (n+1+L)-patternCount α (n+1)


structure CavityGoodParameters (α : ℝ) (f : ℝ→ᵇℝ) where
  J : ℕ→ℕ
  monotone : Monotone J
  le : ∀ n,J n≤n
  tendsto : Tendsto J atTop atTop
  measurable : ∀ n,MeasurableSet (bulkJointGoodSet α f J n)
  mass : Tendsto (fun n=>bulkParameterLaw.real (bulkJointGoodSet α f J n)ᶜ) atTop (𝓝 0)
  deviation : ∀ v : ℕ→ℕ→ℝ,(∀ᶠ n in atTop,v n∈bulkJointGoodSet α f J n)→
    ∀ p,Tendsto (fun n=>bulkDeviationAt n (patternCount α (n+1)) f p (v n)) atTop (𝓝 0) ∧
      Tendsto (fun n=>omittedBulkDeviation α f n p (v n)) atTop (𝓝 0)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFreshReplacement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityFreshMajorant (N L d : ℕ) (f : Jet3)
    (a : Fin d→Fin N→ℝ) (y : Fin d→Spin L) : ℝ :=
  ‖f.d1‖*∑ i,(((L:ℝ)+1)/(N+L:ℕ)*‖WithLp.toLp 2 (a i)‖+
    ((L:ℝ)+1)/Real.sqrt (N+L:ℕ)*‖y i‖)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityProductLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityRowsAppend (N M d : ℕ) (a : Fin M→Fin N→ℝ) (b : Fin d→Fin N→ℝ) :
    Fin (M+d)→Fin N→ℝ := fun i=>Sum.elim a b (finSumFinEquiv.symm i)

def cavityShellLowLog (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (p : (Fin M→Fin (n+1+L)→ℝ)×BulkMark (n+1)) : ℝ :=
  Real.log (tiltPartition (cavityShellBaseLaw n L)
    (fun x=>cavityShellPatternEnergy n L M f p.1 x+inner ℝ (bulkFeature (n+1) v x.1) p.2) 1)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityIncrementLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev CavityIncrementRandom (n L M d : ℕ) :=
  BulkDisorder (n+1) M×(Fin d→Fin (n+1)→ℝ)×(Fin M→Spin L)×(Fin d→Spin L)

def cavityIncrementLaw (n L M d : ℕ) : Measure (CavityIncrementRandom n L M d) :=
  (bulkDisorderLaw (n+1) M).prod ((finitePatternRowsLaw (n+1) d).prod
    ((Measure.pi fun _ : Fin M=>stdGaussian (Spin L)).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))))

instance instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw (n L M d : ℕ) : IsProbabilityMeasure (cavityIncrementLaw n L M d) := by
  unfold cavityIncrementLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def cavityIncrementFullRows (n L M d : ℕ) (p : CavityIncrementRandom n L M d) :
    Fin (M+d)→Fin (n+1+L)→ℝ :=
  cavityRowsAppend (n+1+L) M d (cavityJoinedPatterns (n+1) L M p.1.1 p.2.2.1)
    (cavityJoinedPatterns (n+1) L d p.2.1 p.2.2.2)

abbrev CavityProxyRandom (n L M d : ℕ) := BulkDisorder (n+1) M×(Fin d→Fin (n+1)→ℝ)×(Fin M→Spin L)
def cavityProxyLaw (n L M d : ℕ) : Measure (CavityProxyRandom n L M d) :=
  (bulkDisorderLaw (n+1) M).prod ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
instance instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw (n L M d : ℕ) : IsProbabilityMeasure (cavityProxyLaw n L M d) := by
  unfold cavityProxyLaw; infer_instance

def cavityProxyProjection (n L M d : ℕ) (p : CavityIncrementRandom n L M d) : CavityProxyRandom n L M d :=
  (p.1,p.2.1,p.2.2.1)

def cavityProxyHamiltonian (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : CavityProxyRandom n L M d) (s : CavityShellSpin n L) : ℝ :=
  cavityOldJoinedHamiltonian n L M f v p.1 (normalizedPatternEnergy (n+1) d f.f p.2.1) p.2.2 s

def cavityProxyLog (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ) (p : CavityProxyRandom n L M d) : ℝ :=
  Real.log (∫ s,Real.exp (cavityProxyHamiltonian n L M d f v p s) ∂cavityShellBaseLaw n L)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityOldExpectation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityOldError (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) : ℝ :=
  let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
  K/2+
    Real.exp (2*(d*‖f.f‖+((k+1:ℕ)+1)*K/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
      Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)+
    (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
      (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFiniteIncrement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityUniformError (n k M D : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (C KC : ℝ) : ℝ :=
  Real.pi*cavityBulkCovarianceError n (k+1) C (3*((k+1:ℕ)+1))+
  Real.exp (2*(D*‖f.f‖+((k+1:ℕ)+1)*KC/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
    Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)+
  (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
    (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
    ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))+
  ‖f.d1‖*D*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGoodFreshLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction


def cavityOriginalIncrement (α : ℝ) (f : ℝ→ᵇℝ) (n k : ℕ) (v : ℕ→ℝ) : ℝ :=
  bulkExpectedLog (n+(k+1)) (patternCount α (n+(k+1)+1)) f v-
    bulkExpectedLog n (patternCount α (n+1)) f v

def cavityAveragedLog (α : ℝ) (f : ℝ→ᵇℝ) (n : ℕ) : ℝ :=
  ∫ v,bulkExpectedLog n (patternCount α (n+1)) f v ∂bulkParameterLaw


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternFree
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def enrichedSpinProjection (N : ℕ) (p : Fin N→ℕ) : EnrichedMark N N p →L[ℝ] Spin N :=
  ({ toFun := fun a => WithLp.toLp 2 (fun i => a (.inl i))
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : EnrichedMark N N p →ₗ[ℝ] Spin N).toContinuousLinearMap

@[simp] lemma enrichedSpinProjection_apply (N : ℕ) (p : Fin N→ℕ)
    (a : EnrichedMark N N p) (i : Fin N) : enrichedSpinProjection N p a i=a (.inl i) := rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactEnvelope
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

def Jet3.addConstant (g : Jet3) (c : ℝ) : Jet3 where
  f:=g.f+BoundedContinuousFunction.const ℝ c
  d1:=g.d1
  d2:=g.d2
  d3:=g.d3
  has1 x:=by
    change HasDerivAt (fun y => g.f y + c) (g.d1 x) x
    exact (g.has1 x).add_const c
  has2:=g.has2
  has3:=g.has3

def Jet3.negative (g : Jet3) : Jet3 where
  f:=-g.f
  d1:=-g.d1
  d2:=-g.d2
  d3:=-g.d3
  has1 x:=by simpa using (g.has1 x).neg
  has2 x:=by simpa using (g.has2 x).neg
  has3 x:=by simpa using (g.has3 x).neg

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

abbrev SourceContactParameter (n k : ℕ) := ℝ≥0 × (Fin (k+1)→ℝ) × (Fin (n+1)→ℝ)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FixedCount
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev SourceCountData (n k : ℕ) := (ℕ→Fin (n+1)→ℝ) × (IndexedCascadeBase k × (ℕ→ℝ))

def sourceCountLaw (n k : ℕ) (z : Fin k→ℝ) : Measure (SourceCountData n k) :=
  (infinitePatternRowsLaw (n+1)).prod
    ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
instance instIsProbabilityMeasureSourceCountDataSourceCountLaw (n k : ℕ) (z : Fin k→ℝ) : IsProbabilityMeasure (sourceCountLaw n k z) := by
  unfold sourceCountLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def sourceCountEmbedding (n M k : ℕ) (a : SourceCountData n k) : SourceBaseData n k × (ℕ→ℝ) :=
  ((M,(a.1,a.2.1)),a.2.2)

lemma sourceCountEmbedding_measurable (n M k : ℕ) : Measurable (sourceCountEmbedding n M k) := by
  unfold sourceCountEmbedding
  fun_prop

def sourceCountKernel (n k : ℕ) : Kernel (SourceCountData n k) (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (sourceFullSpinLeafKernel n k).comap (sourceCountEmbedding n 0 k) (sourceCountEmbedding_measurable n 0 k)
instance instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel (n k : ℕ) : IsMarkovKernel (sourceCountKernel n k) := by
  unfold sourceCountKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LevelTrialApprox
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def trialLevelQuantile (m : Trial) (n : ℕ) (i : Fin (n+1)) : Time :=
  sInf {t : Time | (i:ℝ)/(n+1:ℝ)< m t}

def levelStepTrial (m : Trial) (n : ℕ) : Trial :=
  weightedStepTrial (fun _ : Fin (n+1) => 1/(n+1:ℝ)) (trialLevelQuantile m n)
    (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n)

end SphericalPerceptronFreeEnergy
end

end OAI
end


