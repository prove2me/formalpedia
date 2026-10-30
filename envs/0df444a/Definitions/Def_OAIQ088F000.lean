-- Prove2me | Definitions.Def_OAIQ088F000
-- name    : OAIQ088F000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:39:39.969559+00:00
-- url     : https://prove2.me/theorems/98ca5276-2a23-4257-aa8b-791e5ba9c42d
-- title:
--   Definitions bundle OAIQ088F000 of the split of OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 479 declarations of OpenAI's Lean: 278 definitions, 19 inductive types or structures and 182 theorems. The definitions and types are `OAI.Falconer.AngularAdmissible`, `OAI.Falconer.BoundedProfile`, `OAI.Falconer.CapAvailable`, `OAI.Falconer.ChartCapControl`, `OAI.Falconer.ChartSymbolControl`, `OAI.Falconer.DescriptorInverseFamilyIndex`, `OAI.Falconer.DescriptorInverseIndex`, `OAI.Falconer.DescriptorInverseLabel`, `OAI.Falconer.DescriptorInverseSymbols`, `OAI.Falconer.DescriptorInverseSymbols.coefficient`, `OAI.Falconer.DescriptorInverseSymbols.twoProfilePairIntegral`, `OAI.Falconer.DescriptorJetSymbol`, `OAI.Falconer.DescriptorJetSymbol.ambient`, `OAI.Falconer.DescriptorJetSymbol.base`, `OAI.Falconer.DescriptorJetSymbol.conj`, `OAI.Falconer.DescriptorJetSymbol.inverseLeftJets`, `OAI.Falconer.DescriptorJetSymbol.inverseRightJets`, `OAI.Falconer.DescriptorJetSymbol.multiplier`, `OAI.Falconer.DescriptorJetSymbol.pairAmbient`, `OAI.Falconer.DescriptorJetSymbol.relax`, `OAI.Falconer.DescriptorJetSymbol.restrict`, `OAI.Falconer.DescriptorJetSymbol.restrictSpatial`, `OAI.Falconer.DescriptorJetSymbol.seedJet`, `OAI.Falconer.DescriptorJetSymbol.seedMask`, `OAI.Falconer.DescriptorJetSymbol.seedRadius`, `OAI.Falconer.DescriptorJetSymbol.spatialFourier`, `OAI.Falconer.DescriptorJetSymbol.spatialMultiplier`, `OAI.Falconer.DescriptorJetSymbol.value`, `OAI.Falconer.DimensionalProfileLipschitz`, `OAI.Falconer.DyadicCapWitnesses`, `OAI.Falconer.DyadicCube`, `OAI.Falconer.DyadicCube.carrier`, `OAI.Falconer.DyadicCube.center`, `OAI.Falconer.DyadicCube.child`, `OAI.Falconer.DyadicCube.descendant`, `OAI.Falconer.DyadicCube.eligiblePaths`, `OAI.Falconer.DyadicCube.emptyTreeCells`, `OAI.Falconer.DyadicCube.occupiedPaths`, `OAI.Falconer.DyadicCube.occupiedTreeCore`, `OAI.Falconer.DyadicParallelTest` and 257 more.
--
--   **Sources.** They come from these modules of lean/OAI/MeasureTheory, in whole or in part: `Falconer_Angular_AngularEnvelope`, `Falconer_Angular_AngularEnvelopeGraph`, `Falconer_Angular_AngularJetSymbol`, `Falconer_Angular_AngularPair`, `Falconer_Angular_CapDenominator`, `Falconer_Angular_CapReciprocal`, `Falconer_Angular_CapScaleGeometry`, `Falconer_Angular_FactorizedAngularState`, `Falconer_Angular_FarAngularStep`, `Falconer_Angular_FlexibleAngularRoot`, `Falconer_Angular_GlobalCapBounds`, `Falconer_Angular_GnomonicCap`, `Falconer_Angular_GnomonicChart`, `Falconer_Angular_GnomonicInverse`, `Falconer_Angular_MixedCapBounds`, `Falconer_Angular_NormalizedCaps`, `Falconer_Angular_PolicyAngularBranches`, `Falconer_Angular_SmoothCapPartition`, `Falconer_Angular_SphereModel`, `Falconer_Angular_SphereNonstationary`, `Falconer_Angular_SphereNormalization`, `Falconer_Angular_SphereProduct`, `Falconer_Angular_SphereRotations`, `Falconer_Angular_SphereStationary`, `Falconer_Angular_SphereStationaryAssembly`, `Falconer_Estimates_ActualFarBuffer`, `Falconer_Estimates_AllDimensionalRegularizationLabels`, `Falconer_Estimates_AllDimensions`, `Falconer_Estimates_AnchoredBufferedMasks`, `Falconer_Estimates_AnchoredMasks`, `Falconer_Estimates_Availability`, `Falconer_Estimates_ComparableBands`, `Falconer_Estimates_DescriptorAmbient`, `Falconer_Estimates_DescriptorInverseRegime`, `Falconer_Estimates_DescriptorMasks`, `Falconer_Estimates_DescriptorSeededInverse`, `Falconer_Estimates_DescriptorTests`, `Falconer_Estimates_DyadicAncestors`, `Falconer_Estimates_DyadicCenters`, `Falconer_Estimates_DyadicTree`, `Falconer_Estimates_Eligibility`, `Falconer_Estimates_FarCellCount`, `Falconer_Estimates_FarData`, `Falconer_Estimates_FarEnvelope`, `Falconer_Estimates_FarPolicyScales`, `Falconer_Estimates_FilteredLimit`, `Falconer_Estimates_FourPointPartition`, `Falconer_Estimates_GeneralColumns`, `Falconer_Estimates_GlobalDescriptorBounds`, `Falconer_Estimates_InverseClassExpansion`, `Falconer_Estimates_LaplacianBounds`, `Falconer_Estimates_LocalInverse`, `Falconer_Estimates_MixedComposition`, `Falconer_Estimates_MixedMaskBounds`, `Falconer_Estimates_NonstationaryScales`, `Falconer_Estimates_OuterDescriptors`, `Falconer_Estimates_OuterRestrictedConversion`, `Falconer_Estimates_OuterRootGain`, `Falconer_Estimates_Packing`, `Falconer_Estimates_ParallelGood`, `Falconer_Estimates_PlanarGainNumerics`, `Falconer_Estimates_PolicyCommonBudgets`, `Falconer_Estimates_PolicyEnergy`, `Falconer_Estimates_PolicyEnergySteps`, `Falconer_Estimates_PolicyFarCoefficients`, `Falconer_Estimates_PolicyFarStep`, `Falconer_Estimates_PolicyPrefixScales`, `Falconer_Estimates_PolicyRootApplication`, `Falconer_Estimates_PolicySuffixRecurrence`, `Falconer_Estimates_ProjectedPair`, `Falconer_Estimates_RegularClasses`, `Falconer_Estimates_RegularizationSubpower`, `Falconer_Estimates_RetainedPairs`, `Falconer_Estimates_RotatedNonstationary`, `Falconer_Estimates_SeededInverse`, `Falconer_Estimates_SeparatedInverse`, `Falconer_Estimates_SphericalEnergy`, `Falconer_Estimates_SuffixScales`, `Falconer_Estimates_TestWidths`, `Falconer_Estimates_TwoPolicyEnergy`, `Falconer_Estimates_WeightedLowpass`, `Falconer_Fourier_AllDimensionalSpatialFourierIntegration`, `Falconer_Fourier_AllDimensionalSpatialFourierSeparation`, `Falconer_Fourier_ChartBumps`, `Falconer_Fourier_ChartJetOperators`, `Falconer_Fourier_ChartSymbolControl`, `Falconer_Fourier_ComplexMaskJets`, `Falconer_Fourier_CoordinateIntegral`, `Falconer_Fourier_DescriptorDerivativeScale`, `Falconer_Fourier_DescriptorInverseJets`, `Falconer_Fourier_DescriptorJetProduct`, `Falconer_Fourier_DescriptorJetRemoval`, `Falconer_Fourier_EndpointTransform`, `Falconer_Fourier_InverseClassIntegration`, `Falconer_Fourier_InverseJetShell`, `Falconer_Fourier_InverseJetState`, `Falconer_Fourier_InverseJetSymbols`, `Falconer_Fourier_InverseJetValues`, `Falconer_Fourier_InverseMaskJets`, `Falconer_Fourier_JetStateAmbient`, `Falconer_Fourier_JetStateBudgetOrder`, `Falconer_Fourier_JetStateChildren`, `Falconer_Fourier_JetStateEnvelope`, `Falconer_Fourier_JetStateFarSupport`, `Falconer_Fourier_JetStateOperations`, `Falconer_Fourier_JetStateSpatialShell`, `Falconer_Fourier_JetStateStationary`, `Falconer_Fourier_JointStationaryGeometry`, `Falconer_Fourier_MaskJetAlgebra`, `Falconer_Fourier_MaskJetCount`, `Falconer_Fourier_MaskJetGeometry`, `Falconer_Fourier_MaskJetIsometry`, `Falconer_Fourier_MaskJetSeed`, `Falconer_Fourier_MaskedStationaryJets`, `Falconer_Fourier_NoncomparableOriginalIntegral`, `Falconer_Fourier_NormalizedJetDerivatives`, `Falconer_Fourier_PoleCutoffs`, `Falconer_Fourier_PolicyJetChildren`, `Falconer_Fourier_PolicyJetData`, `Falconer_Fourier_PublishedQuadraticStationary`, `Falconer_Fourier_QuadraticStationary`, `Falconer_Fourier_ReachedMaskJets`, `Falconer_Fourier_SafeStationaryChart`, `Falconer_Fourier_SmoothMask`, `Falconer_Fourier_SmoothReciprocal`, `Falconer_Fourier_StationaryCoefficients`, `Falconer_Fourier_StationaryInverse`, `Falconer_Fourier_StationaryTransport`, `Falconer_Geometry_ConditionalProjectionTest`, `Falconer_Geometry_DyadicCube`, `Falconer_Geometry_DyadicSeparation`, `Falconer_Geometry_EuclideanRieszEnergy`, `Falconer_Geometry_FixedChartBounds`, `Falconer_Geometry_FrameEmbedding`, `Falconer_Geometry_IntegerFivePaths`, `Falconer_Geometry_IntegerFourPaths`, `Falconer_Geometry_NormalizedInverseFactors`, `Falconer_Geometry_ProjectionGood`, `Falconer_Geometry_ProjectionLaw`, `Falconer_Geometry_QuadraticChart`, `Falconer_Graphs_AllDimensionalGraphGeometry`, `Falconer_Graphs_EligibleDyadicGraph`, `Falconer_Graphs_FlexibleGraphChild`, `Falconer_Graphs_GraphDegrees`, `Falconer_Graphs_GraphEnergyEstimate`, `Falconer_Graphs_GraphPolicyScales`, `Falconer_Graphs_GraphScaleData`, `Falconer_Graphs_GraphTestScales`, `Falconer_Graphs_JetStateGraph`, `Falconer_Graphs_OuterGraphData`, `Falconer_Graphs_OuterGraphStep`, `Falconer_Graphs_PolicyGraphAt`, `Falconer_Graphs_PolicyGraphGeometry`, `Falconer_Graphs_PolicyGraphRecurrence`, `Falconer_Graphs_PolicyGraphStep`, `Falconer_Graphs_TwoGraphChildren`, `Falconer_Graphs_TwoGraphScales`, `Falconer_Graphs_TwoProfileGraph`, `Falconer_Graphs_WitnessGraph`, `Falconer_Incidence_AngularTubeCount`, `Falconer_Incidence_BlockRegularization`, `Falconer_Incidence_LoomisWhitneyCoordinates`, `Falconer_Incidence_PlanarIncidence`, `Falconer_Incidence_PublishedFurstenberg`, `Falconer_Incidence_WeightedLoomisStep`, `Falconer_Measures_AmbientProduct`, `Falconer_Measures_BorelProductPartition`, `Falconer_Measures_ConditionalFrostman`, `Falconer_Measures_DensityTruncation`, `Falconer_Measures_DescriptorProduct`, `Falconer_Measures_MaskProductBudget`, `Falconer_Measures_SpatialRestriction`, `Falconer_Measures_StartingMeasures`, `Falconer_Radial_HeavyPlateCells`, `Falconer_Radial_OccupiedRadialTree`, `Falconer_Radial_PublishedHeavyPlates`, `Falconer_Radial_RadialMoments`, `Falconer_Radial_RadialZoom`, `Falconer_Recursion_BoundedPotentialCompact`, `Falconer_Recursion_DimensionalBranchBounds`, `Falconer_Recursion_FrostmanProfiles`, `Falconer_Recursion_InheritedPolicyState`, `Falconer_Recursion_InteriorPolicy`, `Falconer_Recursion_MinimalDescriptorLength`, `Falconer_Recursion_OrderedEndpointIntervals`, `Falconer_Recursion_ParallelProfile`, `Falconer_Recursion_PolicyBranchCoefficients`, `Falconer_Recursion_PolicyDescriptors`, `Falconer_Recursion_PolicyFarSuccessors`, `Falconer_Recursion_PolicyRecursionBounds`, `Falconer_Recursion_PrefixPolicyGeometry`, `Falconer_Recursion_ProfileCompactness`, `Falconer_Recursion_ProfileExcess`, `Falconer_Recursion_ProfileNear`, `Falconer_Recursion_ProfilePacking`, `Falconer_Recursion_TwoProfileInverseIntegrable`, `Falconer_Shells_EndpointWeightedDistance`, `Falconer_Shells_FarPositiveSum`, `Falconer_Shells_PolicyPositiveBand`, `Falconer_Shells_PolicyPositiveBranches`, `Falconer_Shells_PositiveSuffix`, `Falconer_Slicing_GaussianRieszKernel`, `Falconer_Slicing_GaussianRowMap`.
--
--   **Imports.** It imports the bundles `OAIQ038F000` and `OAIQ038F001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ088F002` and `OAIQ088F003`; the statements `OAI.Falconer.Regularization.endpoint_one_scale_gain`, `OAI_Falconer_Regularization_endpoint_two_sided_one_scale`, `OAI.Falconer.centered_packet_product_power`, `OAI_Falconer_choose_two_projected_laws`, `OAI_Falconer_endpoint_dyadic_angular_gain`, `OAI_Falconer_eventually_initial_plate_loss`, `OAI_Falconer_exists_jetState_far_tested_integral`, `OAI_Falconer_planar_case_of_published_radial`, `OAI.Falconer.small_chart_weak_radial` and `OAI_Falconer_uniform_projection_profile_mean`; the proofs of `OAI_Falconer_planar_case_of_published_radial`, `OAI_PlanarFalconer_exists_normalized_root_setup_of_published_radial` and `OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum`.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F000
import Definitions.Def_OAIQ038F001

section
-- module Solutions.OAIQ088_FD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
open scoped ContDiff in
/-- Backport (Mathlib d13f23b), with Mathlib's own proof: the iterated derivatives up to order `m` of a
smooth compactly supported function are uniformly bounded (Falconer all dimensions, oaiq-088: 3 modules;
OAIHecke carried its own copy). -/
theorem _root_.HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The all-dimensional Falconer statement and the final measure argument

The Falconer distance conjecture concerns compact subsets of Euclidean
space with Hausdorff dimension greater than half the ambient dimension.
The dimension-independent final measure argument reduces positivity of
the original distance set to absolute continuity of a weighted distance
pushforward.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Original Euclidean distances; auxiliary projections are not used here. -/
def distanceSet {X : Type*} [PseudoMetricSpace X] (E : Set X) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

/-- The Falconer distance conjecture in every ambient dimension at least two. -/
def MainTarget : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (Space d), IsCompact E →
    (d : ℝ≥0∞) / 2 < dimH E → 0 < volume (distanceSet E)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Euclidean sphere and its surface measure

The surface measure is induced by polar coordinates of Euclidean
Lebesgue measure.
-/

namespace Falconer
open Set MeasureTheory

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Space d) 1

noncomputable def sphereMeasure (d : ℕ) : Measure (Sphere d) :=
  (volume : Measure (Space d)).toSphere

@[simp] theorem sphere_norm {d : ℕ} (w : Sphere d) : ‖(w : Space d)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using w.property

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Perpendicular displacement from the line in a unit direction. -/
def perpendicularPart (w v : E) : E := v - inner ℝ w v • w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Degrees of the higher-dimensional retained graph

The vertex sets are the eligible depth-`p` grid cells for a
fixed pair of caps. A parallel test controls the first unknown cell; the
scalar constraint then controls the second, in its own cap direction.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

@[simp] theorem perpendicularPart_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w v : E) :
    perpendicularPart w (-v) = -perpendicularPart w v := by
  simp only [perpendicularPart, inner_neg_right, neg_smul]
  abel

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SphericalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent angular energy in every dimension

The angular measure is the actual sphere measure obtained from Euclidean
Lebesgue measure by polar coordinates. The radial measure is the same
nonnegative shell cutoff used by the scalar reconstruction. Both angular
variables remain independent in this energy.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def sphereMoment {d : ℕ} (U : ℝ × Sphere d → ℂ) (r : ℝ) : ℝ :=
  ∫ w, ‖U (r,w)‖^2 ∂sphereMeasure d

noncomputable def independentAngularEnergy {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    (U V : ℝ × Sphere d → ℂ) : ℝ :=
  (2 : ℝ)^((d : ℝ)*(v-a)) *
    ∫ r, sphereMoment U r * sphereMoment V r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EndpointTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original endpoint transforms in arbitrary dimension

The spatial measure argument is already restricted to its cell. A child
therefore uses the same endpoint symbol and the original restricted law.
The exact finite-measure splitting keeps the model-mass factors explicit.
-/

namespace Falconer
open MeasureTheory

noncomputable def endpointTransform {d : ℕ} (ρ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) : ℂ :=
  M⁻¹ • ∫ x, Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w ∂ρ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AllDimensionalSpatialFourierSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact separated spatial factors in every dimension. Fourier inversion is applied on Space d, with an integrable coefficient and endpoint phases of norm one. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
variable {d : ℕ}

noncomputable def spatialFourierPhase (s : ℝ) (ξ x : Space d) : ℂ :=
  Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • x))*Complex.I)

@[fun_prop] theorem spatialFourierPhase_continuous (s : ℝ) :
    Continuous (fun z : Space d × Space d => spatialFourierPhase s z.1 z.2) := by
  unfold spatialFourierPhase
  fun_prop

theorem spatialFourierPhase_norm (s : ℝ) (ξ x : Space d) :
    ‖spatialFourierPhase s ξ x‖ = 1 := by
  simp [spatialFourierPhase, Complex.norm_exp, Complex.mul_re]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AllDimensionalSpatialFourierIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fubini for the original pair measure and the actual all-dimensional spatial factors. This is the spatial separation used by osc:spatial-separation. -/

namespace Falconer
open MeasureTheory Filter
open scoped ComplexConjugate
variable {d : ℕ}

noncomputable def spatialPairPhase (s : ℝ) (ξ : Space d) (z : Space d × Space d) : ℂ :=
  spatialFourierPhase s ξ z.1 * conj (spatialFourierPhase s ξ z.2)

@[fun_prop] theorem spatialPairPhase_continuous (s : ℝ) :
    Continuous (fun p : Space d × (Space d × Space d) => spatialPairPhase s p.1 p.2) := by
  unfold spatialPairPhase spatialFourierPhase
  fun_prop

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing bounds for the cap centers

Disjoint Euclidean balls give a bound independent of the number of chosen
centers. This supplies the bounded-overlap count needed for a separated cap
partition, and a polynomial global bound on the cap count.
-/

namespace Falconer
open Set Metric MeasureTheory

theorem volume_real_ball {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Space d)).real (ball x r) =
      r^d*(volume : Measure (Space d)).real (ball 0 1) := by
  simp only [measureReal_def,Measure.addHaar_ball_of_pos volume x hr,ENNReal.toReal_mul,
    finrank_euclideanSpace,Fintype.card_fin,ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

theorem separated_ball_card {d : ℕ} (S : Finset (Space d)) (x₀ : Space d)
    {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → s ≤ dist x y)
    (hball : ∀ x ∈ S, dist x x₀ ≤ r) :
    (S.card : ℝ) ≤ (2*r/s+1)^d := by
  have ht : 0 < s/2 := half_pos hs
  have hbig : 0 < r+s/2 := by linarith
  have hd : PairwiseDisjoint (S : Set (Space d)) (fun x => ball x (s/2)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hdist := dist_triangle x z y
    have h₁ := mem_ball.mp hz
    have h₂ := mem_ball.mp hz'
    rw [dist_comm z x] at h₁
    have hh := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ S, ball x (s/2)) ⊆ ball x₀ (r+s/2) := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp hz
    apply mem_ball.mpr
    have h₁ := mem_ball.mp hzx
    have h₂ := hball x hx
    have h₃ := dist_triangle z x x₀
    linarith
  have hm := measureReal_mono (μ := (volume : Measure (Space d))) hsub
    (measure_ball_lt_top.ne)
  rw [measureReal_biUnion_finset hd (fun _ _ => isOpen_ball.measurableSet)] at hm
  simp_rw [volume_real_ball _ ht] at hm
  rw [Finset.sum_const, nsmul_eq_mul, volume_real_ball _ hbig] at hm
  let V := (volume : Measure (Space d)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : Space d) zero_lt_one).ne' measure_ball_lt_top.ne
  have he : r+s/2 = (2*r/s+1)*(s/2) := by field_simp
  rw [he,mul_pow] at hm
  have hp : 0 < (s/2)^d*V := mul_pos (pow_pos ht d) hV
  apply (mul_le_mul_iff_right₀ hp).mp
  first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def smoothReciprocal (τ : ℝ) (hτ : 0 < τ) (u : ℝ) : ℝ :=
  (1 - PlanarFalconer.sineZeroCutoff τ hτ u) * u⁻¹

theorem smoothReciprocal_contDiff (τ : ℝ) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (smoothReciprocal τ hτ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hb := (PlanarFalconer.sineZeroCutoff τ hτ).eventuallyEq_one
    have he : smoothReciprocal τ hτ =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [hb] with y hy
      simp [smoothReciprocal,hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (contDiffAt_const.sub (PlanarFalconer.sineZeroCutoff τ hτ).contDiffAt).mul
      (contDiffAt_id.inv hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SmoothCapPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite smooth cap partition on the actual sphere

These are ambient smooth functions restricted to the sphere. The denominator
is extended smoothly away from the sphere, where the covering lower bound
need not hold. Quantitative derivative and overlap estimates are separate
from this qualitative construction.
-/

namespace Falconer
open Set Metric
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def capBump {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) :
    ContDiffBump (c : Space d) where
  rIn := δ/2
  rOut := δ
  rIn_pos := half_pos hδ
  rIn_lt_rOut := half_lt_self hδ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

noncomputable def sphereMap {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) : Sphere d :=
  ⟨e w, by simpa only [Metric.mem_sphere,dist_zero_right,e.norm_map] using w.property⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def northLift {n : ℕ} (x : Space n) : Space (n+1) :=
  WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))

@[simp] theorem northLift_zero {n : ℕ} (x : Space n) : northLift x 0 = 1 := rfl

@[simp] theorem northLift_succ {n : ℕ} (x : Space n) (i : Fin n) :
    northLift x i.succ = x i := by simp [northLift]

theorem northLift_ne_zero {n : ℕ} (x : Space n) : northLift x ≠ 0 := by
  intro h
  have hh := congrArg (fun z : Space (n+1) => z 0) h
  simp at hh

theorem northLift_norm_sq {n : ℕ} (x : Space n) : ‖northLift x‖^2 = 1+‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  simp

noncomputable def gnomonicChart {n : ℕ} (x : Space n) : Sphere (n+1) :=
  ⟨‖northLift x‖⁻¹ • northLift x, by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero x))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (northLift_ne_zero x))]⟩

@[simp] theorem gnomonicChart_zero {n : ℕ} (x : Space n) :
    (gnomonicChart x : Space (n+1)) 0 = ‖northLift x‖⁻¹ := by
  simp [gnomonicChart]

@[simp] theorem gnomonicChart_succ {n : ℕ} (x : Space n) (i : Fin n) :
    (gnomonicChart x : Space (n+1)) i.succ = ‖northLift x‖⁻¹ * x i := by
  simp [gnomonicChart]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CoordinateIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating one Euclidean chart coordinate

This change of coordinates preserves the actual Euclidean volume. It
therefore allows the scalar nonstationary bound to be integrated in the
remaining chart coordinates without any additional measure assumption.
-/

namespace Falconer
open MeasureTheory Set

noncomputable def coordinateEquiv (n : ℕ) : Space (n+1) ≃ᵐ Space n × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin (n+1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)).trans
      (((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))).trans
        (MeasurableEquiv.prodComm : ℝ × Space n ≃ᵐ Space n × ℝ))

noncomputable def coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) : Space (n+1) :=
  (coordinateEquiv n).symm (x,u)

theorem coordinateJoin_eq {n : ℕ} (x : Space n) (u : ℝ) :
    coordinateJoin x u = WithLp.toLp 2 (Fin.cons u (WithLp.ofLp x)) := by
  change WithLp.toLp 2 (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) 0 u
    (WithLp.ofLp x)) = _
  rw [Fin.insertNth_zero]
  simp only [cast_eq]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Filter
open scoped Topology ENNReal

theorem fixed_polynomial_subpower (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((4*(N:ℝ)+1)^k) ≤ ((2:ℝ)^N)^e := by
  have hb : 1 < (2:ℝ)^e := Real.one_lt_rpow (by norm_num) he
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hb).const_mul ((5:ℝ)^k)
  have hevent : ∀ᶠ N : ℕ in atTop, (5:ℝ)^k*((N:ℝ)^k/((2:ℝ)^e)^N) < 1 := by
    exact ht.eventually (gt_mem_nhds (by simp : (5:ℝ)^k*0 < (1:ℝ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast ((le_max_left 1 N₀).trans hN)
  have hh := hN₀ N ((le_max_right 1 N₀).trans hN)
  rw [← mul_div_assoc] at hh
  have hp : 0 < ((2:ℝ)^e)^N := by positivity
  have hpol : (4*(N:ℝ)+1)^k ≤ (5:ℝ)^k*(N:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hbound := hpol.trans ((div_lt_one hp).mp hh).le
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm e (N:ℝ),
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

theorem policy_move_length (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    let p := policyDepth A N q a t
    let l := min (p-a) (t-p)
    q ≤ l ∧ a ≤ p-l ∧ p+l ≤ t := by
  have hh := policyDepth_interior A hq hne
  dsimp only
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policyOrigins_mono {N q a a' t t' : ℕ} (ha : a ≤ a') (ht : t' ≤ t) :
    policyOrigins N q a' t' ⊆ policyOrigins N q a t := by
  intro z hz
  obtain ⟨hz,ha',ht',hwide⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz,ha.trans ha',ht'.trans ht,hwide⟩

theorem policyDescriptorList_mono (A : ℕ → ℝ) {N q a a' t t' : ℕ}
    (ha : a ≤ a') (ht : t' ≤ t) :
    policyDescriptorList A N q a' t' ⊆ policyDescriptorList A N q a t := by
  intro d hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨z,policyOrigins_mono ha ht hz,hd⟩

theorem originDescriptor_anchor (A : ℕ → ℝ) {N q b u : ℕ} {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) : descriptorAnchor d = policyDepth A N q b u := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    rfl
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d; rfl
    · simp at hd

theorem originDescriptor_length (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) :
    0 < descriptorLength d ∧ b ≤ descriptorAnchor d-descriptorLength d ∧
      descriptorAnchor d+descriptorLength d ≤ u := by
  have hne := policyBlocks_nonempty hq huN hwide
  have hp := policyDepth_interior A hq hne
  have hl := policy_move_length A hq hne
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hg := Finset.mem_Ico.mp hg
    dsimp only [descriptorLength,descriptorAnchor] at *
    omega
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d
      dsimp only [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem originDescriptors_card (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) : (originDescriptors A N q b u).card ≤ N+1 := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  unfold originDescriptors
  apply (Finset.card_union_le _ _).trans
  have hfirst : ((Finset.Ico (policyDepth A N q b u-min (policyDepth A N q b u-b)
      (u-policyDepth A N q b u)) (policyDepth A N q b u)).image
      (fun g => PolicyDescriptor.parallel g (policyDepth A N q b u))).card ≤ N := by
    apply Finset.card_image_le.trans
    rw [Nat.card_Ico]
    omega
  split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem policyDescriptorList_card (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) :
    (policyDescriptorList A N q a t).card ≤ (N+1)^3 := by
  classical
  calc
    _ ≤ ∑ z ∈ policyOrigins N q a t, (originDescriptors A N q z.1 z.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ policyOrigins N q a t, (N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
      have huN := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
      exact originDescriptors_card A hq huN hwide
    _ = (policyOrigins N q a t).card*(N+1) := by simp
    _ ≤ ((N+1)*(N+1))*(N+1) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = (N+1)^3 := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A nonstationary estimate for the actual sphere measure

The amplitude is supported in one gnomonic cap. Ordinary one-coordinate
regularity and a phase lower bound give arbitrary repeated-integration
decay, with a constant independent of the cap amplitude and frequency.
The density and the remaining-coordinate integration are included.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def chartAmplitude {n : ℕ} (b : Sphere (n+2) → ℂ)
    (y : Space n) (u : ℝ) : ℂ := b (gnomonicChart (coordinateJoin y u))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform rotation of the spherical nonstationary estimate

The same constant applies to every cap center and every choice of its
first tangent direction. The displacement is pulled back by the linear
isometry, while the amplitude keeps its original point labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def rotatedChartAmplitude {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (b : Sphere (n+2) → ℂ)
    (y : Space n) (u : ℝ) : ℂ := chartAmplitude (fun w => b (sphereMap e w)) y u

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap bump derivatives in every rotated spherical chart

The constants depend only on the ambient dimension and derivative order.
The cap center, rotation, radius and transverse chart coordinate remain free.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def rotatedChartCurve {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ) : Space (n+2) :=
  e (gnomonicChart (coordinateJoin y u))

@[simp] theorem rotatedChartCurve_norm {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ) :
    ‖rotatedChartCurve e y u‖ = 1 := by
  simp only [rotatedChartCurve,LinearIsometryEquiv.norm_map,sphere_norm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def capDenominator {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (x : Space d) : ℝ :=
  ∑ c ∈ S, capBump δ hδ c x

theorem capDenominator_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) : ContDiff ℝ ∞ (capDenominator δ hδ S) :=
  ContDiff.sum (fun c _ => (capBump δ hδ c).contDiff)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

noncomputable def capReciprocal {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (x : Space d) : ℝ :=
  smoothReciprocal 1 zero_lt_one (capDenominator δ hδ S x)

theorem capReciprocal_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) : ContDiff ℝ ∞ (capReciprocal δ hδ S) :=
  (smoothReciprocal_contDiff 1 zero_lt_one).comp (capDenominator_contDiff hδ S)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NormalizedCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def normalizedCap {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) (x : Space d) : ℝ :=
  capBump δ hδ c x * capReciprocal δ hδ S x

theorem normalizedCap_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) : ContDiff ℝ ∞ (normalizedCap δ hδ S c) :=
  (capBump δ hδ c).contDiff.mul (capReciprocal_contDiff hδ S)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two independent angular variables in one graph term

For fixed spatial points, the four-point phase separates into two sphere
integrals. A nonstationary bound in either variable can thus be used without
any angle separation or pointwise truncation of the amplitude.
-/

namespace Falconer
open MeasureTheory

noncomputable def sphereOscillator {d : ℕ} (Λ : ℝ) (v : Space d) (w : Sphere d) : ℂ :=
  Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) v : ℂ))

@[simp] theorem sphereOscillator_norm {d : ℕ} (Λ : ℝ) (v : Space d) (w : Sphere d) :
    ‖sphereOscillator Λ v w‖ = 1 := by
  simp [sphereOscillator,Complex.norm_exp]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

structure DyadicCube (d : ℕ) where
  origin : Space d
  side : ℝ

def DyadicCube.carrier {d : ℕ} (Q : DyadicCube d) : Set (Space d) :=
  {x | ∀ i, Q.origin i ≤ x i ∧ x i < Q.origin i + Q.side}

noncomputable def DyadicCube.child {d : ℕ} (Q : DyadicCube d) (b : Fin d → Bool) : DyadicCube d where
  origin := WithLp.toLp 2 (fun i => Q.origin i + if b i then Q.side / 2 else 0)
  side := Q.side / 2

noncomputable def DyadicCube.center {d : ℕ} (Q : DyadicCube d) : Space d :=
  WithLp.toLp 2 (fun i => Q.origin i + Q.side / 2)

theorem DyadicCube.child_subset {d : ℕ} (Q : DyadicCube d)
    (b : Fin d → Bool) : (Q.child b).carrier ⊆ Q.carrier := by
  intro x hx i
  have hh := hx i
  cases h : b i <;> simp only [child, PiLp.toLp_apply, h, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true, add_zero] at hh <;>
    constructor <;> linarith

theorem DyadicCube.cover_children {d : ℕ} (Q : DyadicCube d) :
    Q.carrier = ⋃ b : Fin d → Bool, (Q.child b).carrier := by
  classical
  apply subset_antisymm
  · intro x hx
    let b : Fin d → Bool := fun i => decide (Q.origin i + Q.side / 2 ≤ x i)
    apply mem_iUnion.mpr
    refine ⟨b, ?_⟩
    intro i
    have hi := hx i
    by_cases h : Q.origin i + Q.side / 2 ≤ x i
    · simp only [child, b, h, decide_true, ite_true, if_true, PiLp.toLp_apply]
      exact ⟨trivial, by linarith⟩
    · simp only [child, b, h, decide_false, Bool.false_eq_true, ite_false, if_false,
        PiLp.toLp_apply, add_zero]
      exact ⟨hi.1, lt_of_not_ge h⟩
  · exact iUnion_subset fun b => Q.child_subset b

theorem DyadicCube.children_disjoint {d : ℕ} (Q : DyadicCube d)
    {b b' : Fin d → Bool} (hne : b ≠ b') :
    Disjoint (Q.child b).carrier (Q.child b').carrier := by
  classical
  have hex : ∃ i, b i ≠ b' i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h0 := hx i
  have h1 := hx' i
  cases hb : b i <;> cases hb' : b' i <;>
    simp_all only [child, PiLp.toLp_apply, Bool.false_eq_true,
      ite_false, if_false, ite_true, if_true, add_zero, ne_eq, not_true_eq_false] <;> linarith

theorem DyadicCube.center_mem {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side) :
    Q.center ∈ Q.carrier := by
  intro i
  change Q.origin i ≤ Q.origin i + Q.side / 2 ∧
    Q.origin i + Q.side / 2 < Q.origin i + Q.side
  constructor <;> linarith

/-- The cube diameter estimate used when choosing a same-ancestor witness. -/
theorem DyadicCube.dist_le {d : ℕ} (Q : DyadicCube d) (hQ : 0 ≤ Q.side)
    {x y : Space d} (hx : x ∈ Q.carrier) (hy : y ∈ Q.carrier) :
    dist x y ≤ Real.sqrt d * Q.side := by
  have hc (i : Fin d) : |x i - y i| ≤ Q.side := by
    have hxi := hx i
    have hyi := hy i
    rw [abs_le]
    constructor <;> linarith
  have hs := EuclideanSpace.dist_sq_eq x y
  have hb : ∑ i : Fin d, dist (x i) (y i)^2 ≤ (d : ℝ) * Q.side^2 := by
    calc
      _ ≤ ∑ _i : Fin d, Q.side^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.dist_eq]
        exact (sq_le_sq₀ (abs_nonneg _) hQ).mpr (hc i)
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rw [← hs] at hb
  have hprod : 0 ≤ Real.sqrt (d : ℝ) * Q.side := mul_nonneg (Real.sqrt_nonneg _) hQ
  nlinarith [dist_nonneg (x := x) (y := y)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def cubePaths (d : ℕ) : ℕ → Finset (List (Fin d → Bool))
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun b => (cubePaths d n).image (List.cons b)

@[simp] theorem mem_cubePaths (d n : ℕ) (p : List (Fin d → Bool)) :
    p ∈ cubePaths d n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [cubePaths]
  | succ n ih =>
    cases p with
    | nil => simp [cubePaths]
    | cons b p => simp [cubePaths, ih]

noncomputable def DyadicCube.descendant {d : ℕ} (Q : DyadicCube d) :
    List (Fin d → Bool) → DyadicCube d
  | [] => Q
  | b :: p => (Q.child b).descendant p

@[simp] theorem DyadicCube.descendant_nil {d : ℕ} (Q : DyadicCube d) :
    Q.descendant [] = Q := rfl

theorem DyadicCube.descendant_append {d : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) :
    Q.descendant (p ++ q) = (Q.descendant p).descendant q := by
  induction p generalizing Q with
  | nil => rfl
  | cons b p ih => exact ih (Q.child b)

theorem DyadicCube.descendant_side {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons b p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

theorem DyadicCube.descendant_side_pos {d : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) :
    0 < (Q.descendant p).side := by
  rw [Q.descendant_side]
  positivity

theorem DyadicCube.descendant_subset {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) : (Q.descendant p).carrier ⊆ Q.carrier := by
  induction p generalizing Q with
  | nil => exact Subset.rfl
  | cons b p ih => exact (ih (Q.child b)).trans (Q.child_subset b)

theorem DyadicCube.descendants_disjoint {d : ℕ} (Q : DyadicCube d)
    {p q : List (Fin d → Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).carrier (Q.descendant q).carrier := by
  induction p generalizing Q q with
  | nil =>
    have hq : q = [] := by cases q <;> simp_all
    exact (hne hq.symm).elim
  | cons b p ih =>
    cases q with
    | nil => simp at hlen
    | cons c q =>
      by_cases hbc : b = c
      · subst c
        exact ih (Q.child b) (by simpa using hlen)
          (fun he => hne (he ▸ rfl))
      · exact (Q.children_disjoint hbc).mono
          ((Q.child b).descendant_subset p) ((Q.child c).descendant_subset q)

theorem DyadicCube.mem_descendant_at_depth {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    {x : Space d} (hx : x ∈ Q.carrier) :
    ∃ p ∈ cubePaths d n, x ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[], by simp, hx⟩
  | succ n ih =>
    rw [Q.cover_children] at hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    obtain ⟨p, hp, hxp⟩ := ih (Q.child b) hb
    exact ⟨b :: p, by simpa using hp, hxp⟩

noncomputable def DyadicCube.occupiedPaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) : Finset (List (Fin d → Bool)) :=
  (cubePaths d n).filter fun p => 0 < μ (Q.descendant p).carrier

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartSymbolControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite derivative data for the graph localization

These records express cap and endpoint regularity bounds. They contain no oscillatory estimate or incidence conclusion.
Spatial cell indicators preserve all the required angular derivative bounds.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

structure ChartSymbolControl {n : ℕ} (m : ℕ)
    (b : Space (n+2) → Sphere (n+2) → ℂ) (B D : ℝ) : Prop where
  measurable : Measurable (Function.uncurry b)
  bound : ∀ x w, ‖b x w‖ ≤ B
  smooth : ∀ x (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n),
    ContDiff ℝ ∞ (rotatedChartAmplitude e (b x) y)
  derivative : ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)), ∀ k ≤ m,
    ∀ x (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
    ‖iteratedDeriv k (rotatedChartAmplitude e (b x) y) u‖ ≤ B*D^k

structure ChartCapControl {n : ℕ} (m : ℕ) (η : Sphere (n+2) → ℝ)
    (w : Space (n+2)) (δ H : ℝ) : Prop where
  measurable : Measurable η
  bound : ∀ z, |η z| ≤ 1
  support : ∀ z, η z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ
  smooth : ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n),
    ContDiff ℝ ∞ (rotatedChartAmplitude e (fun z => (η z : ℂ)) y)
  derivative : ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)), ∀ k ≤ m,
    ∀ (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
    ‖iteratedDeriv k (rotatedChartAmplitude e (fun z => (η z : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite inverse for the higher-dimensional stationary expansion

The polynomials are those of `osc:L-operators` and `osc:B-operators` in
Section 6 of the manuscript. Their variable represents the sphere Laplacian.
The finite inverse identity is algebraic and independent of a sphere
stationary-phase expansion.
-/

namespace Falconer
open Polynomial
open scoped BigOperators

noncomputable def sphereStationaryConstant (n : ℕ) : ℂ :=
  ((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) *
    Complex.exp (-(Real.pi : ℂ) * n / 4 * Complex.I)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PublishedQuadraticStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed negative-quadratic stationary-phase input

Maciej Zworski, *Semiclassical Analysis*, AMS Graduate Studies in Mathematics
138 (2012), Theorem 3.13, equation (3.5.3), and the remainder estimate in its
proof (printed pp. 54–55):
https://math.jhu.edu/~lindblad/633/Zworski_final.pdf

This is only the specialization `Q = -I`, `h = 1 / Λ`, in dimension
`n = d - 1 ≥ 2`, for amplitudes supported in the fixed closed unit ball.
The Fourier convention in the cited formula is `exp (-i ⟨x, ξ⟩)`, with
`D = (1/i) ∂`. Consequently `⟨Q⁻¹ D, D⟩` is the ordinary Laplacian
`∑ ∂ᵢ²`, and the coefficient is `Δʲ / ((2i)ʲ j!)`. The Gaussian factor is
`(2π)^(n/2) exp (-iπn/4)`, already defined as `sphereStationaryConstant`.

The source controls the remainder by derivatives through order `2J+n+1`.
An operator-norm bound for the iterated Fréchet derivatives bounds each
coordinate derivative; its dimensional constants are absorbed into `C`.
No spherical stationary-phase statement is assumed here.
-/

namespace Falconer
open Set MeasureTheory
open scoped BigOperators ContDiff

/-- Actual Euclidean iterated Laplacian, with the ordinary positive-second-
derivative sign convention. -/
noncomputable def quadraticJetCoefficient {n : ℕ} (j : ℕ) (a : Space n → ℂ) : ℂ :=
  sphereStationaryConstant n / ((2 * Complex.I)^j * (j.factorial : ℂ)) *
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] a) 0

@[simp] theorem quadraticJetCoefficient_zero {n : ℕ} (a : Space n → ℂ) :
    quadraticJetCoefficient 0 a = sphereStationaryConstant n * a 0 := by
  simp [quadraticJetCoefficient]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite-derivative bounds for stationary jets

The Laplacian is a fixed finite sum of second directional derivatives.
Expressing that contraction as a continuous linear map gives bounds for
all mixed Fréchet derivatives, without replacing them by separate bounds
on a single chart coordinate. Vertical unit vectors in a parameter/tangent
product give the partial Laplacian used by the actual stationary operators.
-/

namespace Falconer
open scoped BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def verticalDirections (n : ℕ) : Fin n → P × Space n :=
  fun i => (0, (EuclideanSpace.basisFun (Fin n) ℝ) i)

end Parameters

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_MixedCapBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mixed ambient derivatives of the actual cap bumps

The fixed compactly supported bump is rescaled by an affine similarity.
This proves a bound for its full Fréchet derivative, not only the derivative
along one selected chart curve. No new regularity assumption is used.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def mixedUnitCapBump (d : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

theorem capBump_eq_mixedUnit {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (c : Sphere d) (x : Space d) :
    capBump δ hδ c x = mixedUnitCapBump d ((δ/2)⁻¹ • (x-(c : Space d))) := by
  have hr : δ/(δ/2) = 2 := by field_simp
  simp only [ContDiffBump.apply, capBump, mixedUnitCapBump, hr,
    div_one, inv_one, one_smul, sub_zero]

theorem iteratedFDeriv_affine_scale_bound {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : Space d) (s : ℝ) (k : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ k (fun y => f (s • (y-c))) x‖ ≤
      ‖iteratedFDeriv ℝ k f (s • (x-c))‖ * |s|^k := by
  let L : Space d →L[ℝ] Space d := s • ContinuousLinearMap.id ℝ (Space d)
  have he : (fun y => f (s • (y-c))) = fun y => (f ∘ L) (-c+y) := by
    funext y
    simp [L, sub_eq_add_neg, add_comm]
  rw [he, iteratedFDeriv_comp_add_left]
  rw [L.iteratedFDeriv_comp_right hf _ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  have hL : ‖L‖ ≤ |s| := by
    calc
      ‖L‖ = |s| * ‖ContinuousLinearMap.id ℝ (Space d)‖ := by
        simp only [L, norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg s)
      _ = |s| := mul_one _
  have h := (iteratedFDeriv ℝ k f (L (-c+x))).norm_compContinuousLinearMap_le
    (fun _ : Fin k => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  have hp : ‖L‖^k ≤ |s|^k := pow_le_pow_left₀ (norm_nonneg L) hL k
  simpa only [L, smul_apply, ContinuousLinearMap.id_apply,
    sub_eq_add_neg, add_comm] using mul_le_mul_of_nonneg_left hp
      (norm_nonneg (iteratedFDeriv ℝ k f (L (-c+x))))

theorem capBump_ambient_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) (x : Space d),
      ‖iteratedFDeriv ℝ k (capBump δ hδ c) x‖ ≤ C*(δ⁻¹)^k := by
  obtain ⟨B,hB,hBb⟩ := (mixedUnitCapBump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (mixedUnitCapBump d).contDiff k
  refine ⟨B*2^k, mul_nonneg hB (by positivity), ?_⟩
  intro δ hδ c x
  have he : (capBump δ hδ c : Space d → ℝ) =
      fun y => mixedUnitCapBump d ((δ/2)⁻¹ • (y-(c : Space d))) := by
    funext y
    exact capBump_eq_mixedUnit δ hδ c y
  rw [he]
  have hh := iteratedFDeriv_affine_scale_bound (mixedUnitCapBump d).contDiff
    (c : Space d) ((δ/2)⁻¹) k x
  have hs : |(δ/2)⁻¹| = 2*δ⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (half_pos hδ))]
    field_simp
  apply hh.trans
  rw [hs, mul_pow]
  calc
    _ ≤ B * (2^k*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right (hBb k le_rfl _) (by positivity)
    _ = _ := by ring

theorem capBump_ambient_derivative_zero {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (c : Sphere d) (x : Space d) (hfar : δ < ‖x-(c : Space d)‖) (k : ℕ) :
    iteratedFDeriv ℝ k (capBump δ hδ c) x = 0 := by
  have hn : x ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he := (notMem_tsupport_iff_eventuallyEq.mp hn).iteratedFDeriv ℝ k
  simpa using he.self_of_nhds

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuadraticChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed quadratic chart at a sphere pole

This is the actual chart in `osc:stationary`. Its phase is exactly quadratic,
in every dimension. Surface measure transport and its Jacobian are separate
from the geometric statements here.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def quadraticSpherePoint {n : ℕ} (u : Space n) : Space (n+1) :=
  coordinateJoin (Real.sqrt (1-‖u‖^2/4) • u) (1-‖u‖^2/2)

@[simp] theorem quadraticSpherePoint_zero_coord {n : ℕ} (u : Space n) :
    quadraticSpherePoint u 0 = 1-‖u‖^2/2 := by
  simp [quadraticSpherePoint, coordinateJoin_eq]

@[simp] theorem quadraticSpherePoint_succ_coord {n : ℕ} (u : Space n) (i : Fin n) :
    quadraticSpherePoint u i.succ = Real.sqrt (1-‖u‖^2/4) * u i := by
  simp [quadraticSpherePoint, coordinateJoin_eq]

theorem quadraticSpherePoint_contDiffAt {n : ℕ} {u : Space n} (hu : ‖u‖ < 2) :
    ContDiffAt ℝ ∞ (@quadraticSpherePoint n) u := by
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 2)).mpr hu
  have harg : 0 < 1-‖u‖^2/4 := by nlinarith
  have hs : ContDiffAt ℝ ∞ (fun v : Space n => Real.sqrt (1-‖v‖^2/4)) u :=
    (contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt harg.ne'
  apply (contDiffAt_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [quadraticSpherePoint_zero_coord] using
      (contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 2))
  · simpa only [quadraticSpherePoint_succ_coord] using
      hs.mul (contDiffAt_piLp_apply (p := 2) (i := j))

/-- The exact change from quadratic coordinates to the existing gnomonic
coordinates. On the unit ball its denominator is bounded away from zero. -/
noncomputable def quadraticToGnomonic {n : ℕ} (u : Space n) : Space n :=
  (Real.sqrt (1-‖u‖^2/4) / (1-‖u‖^2/2)) • u

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_QuadraticStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the quadratic expansion to the actual sphere integral

The amplitude is the explicitly computed surface density times the spherical
amplitude, extended by zero from the fixed unit chart. Smoothness and its
quantitative derivative bounds are retained as local obligations. The only
published inputs are the gnomonic measure formula and the fixed Euclidean
quadratic stationary-phase theorem.
-/

namespace Falconer
open Set MeasureTheory Metric
open scoped BigOperators ContDiff

noncomputable def quadraticAmplitude (m : ℕ) (b : Sphere (m+3) → ℂ) :
    Space (m+2) → ℂ :=
  (Metric.ball (0 : Space (m+2)) 1).indicator (fun u =>
    ((Real.sqrt (1-‖u‖^2/4))^m : ℂ) * b (gnomonicChart (quadraticToGnomonic u)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identification of the outgoing stationary coefficients

The zeroth coefficient is evaluated on the chart amplitude.
The outgoing Helmholtz recurrence uniquely determines the manuscript's
polynomial coefficients. The identification for local quadratic jets is
conditional on their satisfying this recurrence.
-/

namespace Falconer
open Polynomial

@[simp] theorem quadraticAmplitude_zero (m : ℕ) (b : Sphere (m+3) → ℂ) :
    quadraticAmplitude m b 0 = b (gnomonicChart 0) := by
  simp [quadraticAmplitude, quadraticToGnomonic]

@[simp] theorem quadraticJetCoefficient_amplitude_zero
    (m : ℕ) (b : Sphere (m+3) → ℂ) :
    quadraticJetCoefficient 0 (quadraticAmplitude m b) =
      sphereStationaryConstant (m+2) * b (gnomonicChart 0) := by
  rw [quadraticJetCoefficient_zero, quadraticAmplitude_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of the fixed-pole stationary expansion

A concrete orthogonal reflection takes the chart pole to any requested
unit direction. Rotation invariance transports the actual spherical
integral. Complex conjugation handles the opposite oscillatory sign.
Neither transport uses an additional published input.
-/

namespace Falconer
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

/-- This formula gives smooth dependence on the requested pole whenever the
pole is separated from the antipode of `p`. -/
noncomputable def poleRotationFormula {n : ℕ} (p e x : Space n) : Space n :=
  (2 * inner ℝ (p+e) x / ‖p+e‖^2) • (p+e) - x

theorem poleRotationFormula_contDiffAt {n : ℕ} (p e x : Space n) (he : p+e ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : Space n × Space n => poleRotationFormula p z.1 z.2) (e,x) := by
  have hv : ContDiffAt ℝ ∞ (fun z : Space n × Space n => p+z.1) (e,x) :=
    contDiffAt_const.add contDiffAt_fst
  have hx : ContDiffAt ℝ ∞ (fun z : Space n × Space n => z.2) (e,x) := contDiffAt_snd
  have hi := hv.inner ℝ hx
  have hn : ContDiffAt ℝ ∞ (fun z : Space n × Space n => ‖p+z.1‖^2) (e,x) :=
    (contDiff_norm_sq ℝ).contDiffAt.comp (e,x) hv
  exact ((contDiffAt_const.mul hi).div hn
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr he))).smul hv |>.sub hx

noncomputable def sphereOscillation {d : ℕ} (Λ : ℝ) (e : Sphere d)
    (b : Sphere d → ℂ) : ℂ :=
  ∫ w : Sphere d, Complex.exp (Complex.I*(Λ : ℂ)*
    (inner ℝ (w : Space d) (e : Space d) : ℂ)) * b w ∂sphereMeasure d

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual stationary operators on a smooth pole patch

The operators are the quadratic Laplacian jets of the explicit chart
amplitude. They depend smoothly on the evaluation direction away from the
opposite pole. Their equality with the coefficients in the local
sphere expansion follows by locality, including the fixed chart cutoff.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def unmaskedStationaryAmplitude (m : ℕ) (B : Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+2)) : ℂ :=
  ((Real.sqrt (1-‖z.2‖^2/4))^m : ℂ) *
    B (poleRotationFormula (gnomonicChart (0 : Space (m+2))) z.1 (quadraticSpherePoint z.2))

noncomputable def actualStationaryCoefficient (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Space (m+3)) : ℂ :=
  quadraticJetCoefficient j (fun u => unmaskedStationaryAmplitude m B (e,u))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual north, south, and off-pole partition

The fixed ambient bumps have outer radius 1/4 and are one on radius 1/8.
The remainder therefore stays a fixed distance from both stationary poles.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

def oppositePole {d : ℕ} (e : Sphere d) : Sphere d :=
  ⟨-(e : Space d), by simpa only [mem_sphere,dist_zero_right,norm_neg] using e.property⟩

@[simp] theorem oppositePole_coe {d : ℕ} (e : Sphere d) :
    (oppositePole e : Space d) = -(e : Space d) := rfl

@[simp] theorem oppositePole_opposite {d : ℕ} (e : Sphere d) :
    oppositePole (oppositePole e) = e := by ext; simp

noncomputable def poleCutoff {d : ℕ} (e : Sphere d) : Space d → ℝ :=
  capBump (1/4) (by norm_num) e

theorem poleCutoff_contDiff {d : ℕ} (e : Sphere d) : ContDiff ℝ ∞ (poleCutoff e) :=
  (capBump (1/4) (by norm_num) e).contDiff

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MixedComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise mixed derivative budgets for composition

The fixed constant is the actual finite sum over ordered partitions. A
derivative budget of degree `i` for the inner map gives degree `n` for its
composition, with no loss depending on the scale.
-/

namespace Falconer
open Set
open scoped ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compact_iteratedFDeriv_bound {f : E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  choose A hA using fun i : ℕ => hK.exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (i : ℕ∞ω) ≤ ∞)).continuousOn)
  let C := ∑ i ∈ Finset.range (n+1), max 0 (A i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro i hi x hx
  apply (hA i x hx).trans
  apply (le_max_right 0 (A i)).trans
  exact Finset.single_le_sum (fun j _ => le_max_left 0 (A j)) (by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

noncomputable def mixedCompositionBudget (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ j, B (c.partSize j)

theorem mixedCompositionBudget_nonneg {B : ℕ → ℝ} (hB : ∀ i, 0 ≤ B i) (n : ℕ) :
    0 ≤ mixedCompositionBudget B n := by
  exact Finset.sum_nonneg (fun c _ => Finset.prod_nonneg (fun j _ => hB _))

theorem mixed_composition_derivative_bound {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    {B : ℕ → ℝ} {C D : ℝ} (hC : 0 ≤ C)
    (n : ℕ)
    (houter : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hinner : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B i*D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ mixedCompositionBudget B n*C*D^n := by
  rw [iteratedFDeriv_comp hg hf (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  simp only [FormalMultilinearSeries.taylorComp, mixedCompositionBudget,
    Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
  change ‖iteratedFDeriv ℝ c.length g (f x)‖ *
    (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) f x‖) ≤ _
  have hp : (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) f x‖) ≤
      ∏ j, B (c.partSize j)*D^(c.partSize j) := by
    apply Finset.prod_le_prod
    · intro j _; exact norm_nonneg _
    · intro j _; exact hinner _ (c.partSize_pos j) (c.partSize_le j)
  have he : (∏ j, D^(c.partSize j)) = D^n := by
    simpa using c.prod_sigma_eq_prod (fun _ => D)
  calc
    _ ≤ C * (∏ j, B (c.partSize j)*D^(c.partSize j)) :=
      mul_le_mul (houter _ c.length_le) hp
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC
    _ = _ := by rw [Finset.prod_mul_distrib, he]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FixedChartBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite derivative bounds for fixed quadratic geometry

Only compact sets inside the smooth chart are used. The chart need not
extend smoothly through its outer singularity.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def quadraticChartDensity (m : ℕ) {n : ℕ} (u : Space n) : ℂ :=
  ((Real.sqrt (1-‖u‖^2/4))^m : ℂ)

theorem quadraticChartDensity_contDiffAt (m : ℕ) {n : ℕ} {u : Space n}
    (hu : ‖u‖ < 2) : ContDiffAt ℝ ∞ (quadraticChartDensity m) u := by
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0 : ℝ) ≤ 2)).mpr hu
  apply ContDiffAt.pow
  exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
    ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
      (by nlinarith : 1-‖u‖^2/4 ≠ 0))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskedStationaryJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth fixed-patch extensions of actual stationary jets

The mask is one on the prepared inner cap and vanishes near the antipodal
singularity of the chosen frame. No global spherical differential operator
is assumed.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryPatchMask (m : ℕ) : Space (m+3) → ℝ :=
  poleCutoff (gnomonicChart (0 : Space (m+2)))

theorem stationaryPatchMask_contDiff (m : ℕ) : ContDiff ℝ ∞ (stationaryPatchMask m) :=
  poleCutoff_contDiff _

noncomputable def maskedStationaryCoefficient (m j : ℕ) (B : Space (m+3) → ℂ)
    (x : Space (m+3)) : ℂ :=
  (stationaryPatchMask m x : ℂ)*actualStationaryCoefficient m j B x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite inverse amplitudes built from the actual local jets

Each recursive amplitude is globally smooth and supported in the same fixed
pole patch. The diagonal cancellation is pointwise on the prepared inner
patch and does not assume a spherical differential-operator identity.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def localInverseAmplitude (m : ℕ) (B : Space (m+3) → ℂ) :
    ℕ → Space (m+3) → ℂ
  | 0 => fun x => (sphereStationaryConstant (m+2))⁻¹ * (stationaryPatchMask m x : ℂ) * B x
  | j+1 => fun x => -(sphereStationaryConstant (m+2))⁻¹ *
      ∑ h ∈ Finset.range (j+1),
        maskedStationaryCoefficient m (h+1) (localInverseAmplitude m B (j-h)) x
termination_by j => j
decreasing_by omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JointStationaryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mixed bounds for the actual stationary chart

The reflection formula preserves norm even when its direction parameter is
off the sphere. This permits ambient derivatives in that parameter while
the original symbol is evaluated only on sphere points.
-/

namespace Falconer
open Set Metric
open scoped ContDiff RealInnerProductSpace

noncomputable def jointStationaryChart (m : ℕ)
    (z : Space (m+3) × Space (m+2)) : Space (m+3) :=
  poleRotationFormula (gnomonicChart (0 : Space (m+2))) z.1 (quadraticSpherePoint z.2)

def jointStationaryRegion (m : ℕ) : Set (Space (m+3) × Space (m+2)) :=
  {z | (gnomonicChart (0 : Space (m+2)) : Space (m+3))+z.1 ≠ 0 ∧ ‖z.2‖ < 2}

theorem jointStationaryChart_contDiffAt (m : ℕ)
    {z : Space (m+3) × Space (m+2)} (hz : z ∈ jointStationaryRegion m) :
    ContDiffAt ℝ ∞ (jointStationaryChart m) z := by
  have hq := (quadraticSpherePoint_contDiffAt hz.2).comp z contDiffAt_snd
  have hr := (poleRotationFormula_contDiffAt (gnomonicChart (0 : Space (m+2)))
    z.1 (quadraticSpherePoint z.2) hz.1).comp z (contDiffAt_fst.prodMk hq)
  exact hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SafeStationaryChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A global smooth extension of the fixed local stationary chart

The extension equals the actual chart near every direction in the support
of the fixed patch mask. It exists only to express its finite derivatives
as globally smooth separated factors; the stationary coefficients remain
the original coefficients.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryExtensionBump {n : ℕ} (c : Space n) : ContDiffBump c where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def stationarySafePoint {n : ℕ} (c x : Space n) : Space n :=
  c+(stationaryExtensionBump c x) • (x-c)

theorem stationarySafePoint_contDiff {n : ℕ} (c : Space n) :
    ContDiff ℝ ∞ (stationarySafePoint c) :=
  contDiff_const.add ((stationaryExtensionBump c).contDiff.smul
    (contDiff_id.sub contDiff_const))

theorem stationarySafePoint_bound {n : ℕ} (c x : Space n) :
    ‖stationarySafePoint c x-c‖ ≤ 1 := by
  by_cases hb : stationaryExtensionBump c x = 0
  · simp only [stationarySafePoint,hb,zero_smul,add_zero,sub_self,norm_zero]
    norm_num
  · have hx : ‖x-c‖ < 1 := by
      have hs : x ∈ Function.support (stationaryExtensionBump c) := hb
      rw [(stationaryExtensionBump c).support_eq] at hs
      simpa only [stationaryExtensionBump,mem_ball,dist_eq_norm] using hs
    simp only [stationarySafePoint,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (stationaryExtensionBump c).nonneg]
    calc
      _ ≤ 1*‖x-c‖ := mul_le_mul_of_nonneg_right (stationaryExtensionBump c).le_one (norm_nonneg _)
      _ ≤ 1 := by simpa using hx.le

theorem stationarySafePoint_nonantipodal (m : ℕ) (e : Space (m+3)) :
    (gnomonicChart (0 : Space (m+2)) : Space (m+3))+
      stationarySafePoint (gnomonicChart (0 : Space (m+2))) e ≠ 0 := by
  intro he
  have hbound := stationarySafePoint_bound
    (gnomonicChart (0 : Space (m+2)) : Space (m+3)) e
  have hv : stationarySafePoint (gnomonicChart (0 : Space (m+2))) e =
      -(gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using he
  rw [hv,norm_sub_rev,sub_neg_eq_add,← two_smul ℝ,norm_smul,sphere_norm] at hbound
  norm_num at hbound

noncomputable def safeStationaryChart (m : ℕ)
    (z : Space (m+3) × Space (m+2)) : Space (m+3) :=
  jointStationaryChart m
    (stationarySafePoint (gnomonicChart (0 : Space (m+2))) z.1,
      stationarySafePoint 0 z.2)

theorem safeStationaryChart_contDiff (m : ℕ) : ContDiff ℝ ∞ (safeStationaryChart m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let g : Space (m+3) × Space (m+2) → Space (m+3) × Space (m+2) := fun q =>
    (stationarySafePoint (gnomonicChart (0 : Space (m+2))) q.1,stationarySafePoint 0 q.2)
  have hg : ContDiff ℝ ∞ g :=
    ((stationarySafePoint_contDiff _).comp contDiff_fst).prodMk
      ((stationarySafePoint_contDiff _).comp contDiff_snd)
  have hu : ‖stationarySafePoint (0 : Space (m+2)) z.2‖ < 2 := by
    have h := stationarySafePoint_bound (0 : Space (m+2)) z.2
    rw [sub_zero] at h
    linarith
  have hz : g z ∈ jointStationaryRegion m :=
    ⟨stationarySafePoint_nonantipodal m z.1,hu⟩
  change ContDiffAt ℝ ∞ (jointStationaryChart m ∘ g) z
  exact (jointStationaryChart_contDiffAt m hz).comp z hg.contDiffAt

noncomputable def safeStationaryDensity (m : ℕ) (u : Space (m+2)) : ℂ :=
  quadraticChartDensity m (stationarySafePoint 0 u)

theorem safeStationaryDensity_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (safeStationaryDensity m) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have hu : ‖stationarySafePoint (0 : Space (m+2)) u‖ < 2 := by
    have h := stationarySafePoint_bound (0 : Space (m+2)) u
    rw [sub_zero] at h
    linarith
  exact (quadraticChartDensity_contDiffAt m hu).comp u
    (stationarySafePoint_contDiff _).contDiffAt

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SeparatedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite endpoint separation of the actual inverse amplitudes

The finite expansion is constructed from product rules and chart pullbacks.
Every factor is globally smooth and depends on one endpoint only. This is
an identity for the original masked inverse, with no extra analytic input.
-/

namespace Falconer
open scoped ContDiff

variable {X Y : Type*}

namespace SmoothSeparation

noncomputable def stationaryJetMultiplier (m j : ℕ) (e : Space (m+3)) : ℂ :=
  (stationaryPatchMask m e : ℂ)*
    (sphereStationaryConstant (m+2)/((2*Complex.I)^j*(j.factorial : ℂ)))

theorem stationaryJetMultiplier_contDiff (m j : ℕ) :
    ContDiff ℝ ∞ (stationaryJetMultiplier m j) := by
  exact (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)).mul contDiff_const

noncomputable def stationaryJointDensity (m : ℕ) (z : Space (m+3) × Space (m+2)) : ℂ :=
  safeStationaryDensity m z.2

theorem stationaryJointDensity_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (stationaryJointDensity m) :=
  (safeStationaryDensity_contDiff m).comp contDiff_snd

end SmoothSeparation

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedInverseFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size-one endpoint factors with the exact total derivative cost

Positive upper sizes are selected before the scale label. Division by
those sizes retains all zero sets and chart bounds; their product costs
only the sum of the original endpoint derivative orders.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem ChartSymbolControl.conj {n K : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl K b B D) :
    ChartSymbolControl K (fun x w => star (b x w)) B D := by
  refine ⟨continuous_star.measurable.comp h.measurable,?_,?_,?_⟩
  · intro x w
    simpa only [norm_star] using h.bound x w
  · intro x e y
    exact Complex.conjCLE.contDiff.comp (h.smooth x e y)
  · intro e k hk x y hy u hu
    have hn := Complex.conjLIE.norm_iteratedFDeriv_comp_left
      (rotatedChartAmplitude e (b x) y) u k
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hn
    exact hn.le.trans (h.derivative e k hk x y hy u hu)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded supremum of the actual admissible endpoint energies

The admissible class records only the existing chart-symbol control and
the required support. Its envelope is the real supremum of the original
endpoint-transform energies, with zero inserted to ensure nonemptiness.
-/

namespace Falconer
open Set MeasureTheory

def AngularAdmissible {n : ℕ} (k : ℕ) (D : ℝ)
    (Good : Set (Space (n+2) × Sphere (n+2)))
    (b : Space (n+2) → Sphere (n+2) → ℂ) : Prop :=
  ChartSymbolControl k b 1 D ∧ ∀ x w, b x w ≠ 0 → (x,w) ∈ Good

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Eligibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Eligible cell--cap incidences

Positive incidence supplies one point--angle witness. Zero incidence
annihilates the endpoint transform on almost every angle in the cap,
simultaneously for every radial frequency. The symbols need only be
measurable in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def capIncidence {d : ℕ} (ρ : Measure (Space d))
    (η : Sphere d → ℝ) (b : Space d → Sphere d → ℂ) : ℝ :=
  ∫ w, η w * (∫ x, ‖b x w‖^2 ∂ρ) ∂sphereMeasure d

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

def dyadicCode {d : ℕ} : List (Fin d → Bool) → Fin d → ℤ
  | [] => fun _ => 0
  | b :: p => fun i => (if b i then (2 : ℤ)^p.length else 0) + dyadicCode p i

theorem DyadicCube.descendant_origin {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (i : Fin d) :
    (Q.descendant p).origin i =
      Q.origin i + (Q.side / (2 : ℝ)^p.length) * (dyadicCode p i : ℝ) := by
  induction p generalizing Q with
  | nil => simp [DyadicCube.descendant, dyadicCode]
  | cons b p ih =>
    rw [DyadicCube.descendant, ih]
    simp only [DyadicCube.child, PiLp.toLp_apply, dyadicCode, List.length_cons, pow_succ]
    cases b i <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, add_zero]
    · push_cast
      ring
    · push_cast
      field_simp
      ring

theorem DyadicCube.descendant_center {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (i : Fin d) :
    (Q.descendant p).center i =
      Q.origin i + (Q.side / (2 : ℝ)^p.length)/2 +
        (Q.side / (2 : ℝ)^p.length) * (dyadicCode p i : ℝ) := by
  change (Q.descendant p).origin i + (Q.descendant p).side / 2 = _
  rw [Q.descendant_origin, Q.descendant_side]
  ring

theorem dyadicCode_injective_at_depth {d n : ℕ} {p q : List (Fin d → Bool)}
    (hp : p.length = n) (hq : q.length = n) (heq : dyadicCode p = dyadicCode q) : p = q := by
  classical
  let Q : DyadicCube d := ⟨0,1⟩
  have hQ : 0 < Q.side := by norm_num [Q]
  by_contra hne
  have hc : (Q.descendant p).center = (Q.descendant q).center := by
    ext i
    rw [Q.descendant_center, Q.descendant_center, hp, hq, heq]
  have hleft := (Q.descendant p).center_mem (Q.descendant_side_pos hQ p)
  have hright := (Q.descendant q).center_mem (Q.descendant_side_pos hQ q)
  rw [← hc] at hright
  exact Set.disjoint_left.mp (Q.descendants_disjoint (hp.trans hq.symm) hne) hleft hright

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicAncestors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ancestor groups for the retained graph witnesses

There are at most `2^(d*g)` ancestor groups at relative depth `g`.
All centers within one group lie in the same original dyadic cube, giving
the diameter used in the parallel-test witness argument.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem DyadicCube.center_mem_ancestor {d : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) (g : ℕ) :
    (Q.descendant p).center ∈ (Q.descendant (p.take g)).carrier := by
  have he : Q.descendant p = (Q.descendant (p.take g)).descendant (p.drop g) := by
    rw [← Q.descendant_append, List.take_append_drop]
  rw [he]
  exact (Q.descendant (p.take g)).descendant_subset (p.drop g)
    (((Q.descendant (p.take g)).descendant (p.drop g)).center_mem
      ((Q.descendant (p.take g)).descendant_side_pos (Q.descendant_side_pos hQ _) _))

theorem DyadicCube.same_ancestor_center_dist {d n g : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hg : g ≤ n) (heq : p.take g = q.take g) :
    dist (Q.descendant p).center (Q.descendant q).center ≤
      Real.sqrt d * (Q.side / (2 : ℝ)^g) := by
  have hcp := Q.center_mem_ancestor hQ p g
  have hcq := Q.center_mem_ancestor hQ q g
  rw [← heq] at hcq
  have hh := (Q.descendant (p.take g)).dist_le (Q.descendant_side_pos hQ _).le hcp hcq
  simpa only [Q.descendant_side, List.length_take, hp, min_eq_left hg] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_WitnessGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Schur bound from the original parallel-test witnesses

For each endpoint, all retained cells in an ancestor group are charged
to one actual eligible witness. Combining both candidate bounds with the
center tests gives the smaller of the two profile counts.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

def DyadicParallelTest {d : ℕ} (Q : DyadicCube d)
    (A : Finset (List (Fin d → Bool))) (g : ℕ) (a : List (Fin d → Bool))
    (w : Space d) (W : ℝ) (C : ℕ) : Prop :=
  (A.filter (fun z => z.take g = a.take g ∧
    ‖(Q.descendant z).center - (Q.descendant a).center‖ ≤
      Real.sqrt d * (Q.side/(2 : ℝ)^g) ∧
    ‖perpendicularPart w ((Q.descendant z).center - (Q.descendant a).center)‖ ≤ W)).card ≤ C

def DyadicCapWitnesses {d : ℕ} (Q : DyadicCube d)
    (A : Finset (List (Fin d → Bool))) (g : ℕ)
    (w₀ : Space d) (δ W : ℝ) (C : ℕ) : Prop :=
  ∀ a ∈ A, ∃ w : Space d, ‖w‖ = 1 ∧ ‖w-w₀‖ ≤ δ ∧ DyadicParallelTest Q A g a w W C

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_EligibleDyadicGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph of eligible original cell--cap incidences

Support of an endpoint symbol in a literal parallel test supplies the
witnesses used by the degree estimate. Eligibility only filters the finite
cell list; no angular support is cut by a pointwise edge decision.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def DyadicCube.eligiblePaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) (η : Sphere d → ℝ)
    (b : Space d → Sphere d → ℂ) : Finset (List (Fin d → Bool)) :=
  (Q.occupiedPaths μ n).filter fun p =>
    0 < capIncidence (μ.restrict (Q.descendant p).carrier) η b

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphEnergyEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph energy estimate before profile normalization

This assembles the exact splitting, proved localization and retained
Schur bound. All endpoint symbols, including reached anchor masks, remain
unchanged on children. The numerical error is explicit.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

noncomputable def capGraphError (d m : ℕ) (A C W R T M₁ M₂ H B D v τ : ℝ) (K S : ℕ) : ℝ :=
  (K : ℝ)^2*(S : ℝ)^2 *
    (|(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
      (A*(4^m*H*B*B)*(B*B)*(sphereMeasure d).real univ) *
        (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
    |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
      ((B*B)*(B*B)*C*((sphereMeasure d).real univ)^2*R^(-T)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

noncomputable def sphereNormalizeVector (w₀ : Sphere d) (v : Space d) : Space d :=
  if v = 0 then w₀ else normalize v

theorem sphereNormalizeVector_norm (w₀ : Sphere d) (v : Space d) :
    ‖sphereNormalizeVector w₀ v‖ = 1 := by
  by_cases hv : v = 0
  · simp only [sphereNormalizeVector,ite_eq_left hv,sphere_norm]
  · simp only [sphereNormalizeVector,ite_eq_right hv,norm_normalize hv]

noncomputable def normalizeToSphere (w₀ : Sphere d) (v : Space d) : Sphere d :=
  ⟨sphereNormalizeVector w₀ v,by
    rw [Metric.mem_sphere,dist_zero_right,sphereNormalizeVector_norm]⟩

@[simp] theorem normalizeToSphere_coe_of_ne (w₀ : Sphere d) {v : Space d} (hv : v ≠ 0) :
    (normalizeToSphere w₀ v : Space d) = normalize v := by
  simp only [normalizeToSphere,sphereNormalizeVector,ite_eq_right hv]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth angular masks from buffered good sets

A finite subcollection of the normalized cap partition gives a cutoff
supported inside a prescribed set. It equals one wherever a closed ball
of twice the cap radius lies in that set. No regularity of the set is
needed for this finite construction.
-/

namespace Falconer
open Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def cutoffCapCenters {d : ℕ} (δ : ℝ) (S : Finset (Sphere d))
    (U : Set (Sphere d)) : Finset (Sphere d) :=
  S.filter (fun c => ∀ z : Sphere d, dist z c ≤ δ → z ∈ U)

noncomputable def capCutoffAmbient {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) (x : Space d) : ℝ :=
  ∑ c ∈ cutoffCapCenters δ S U, normalizedCap δ hδ S c x

theorem capCutoffAmbient_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) :
    ContDiff ℝ ∞ (capCutoffAmbient δ hδ S U) :=
  ContDiff.sum (fun c _ => normalizedCap_contDiff hδ S c)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MaskProductBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual buffered masks satisfy finite symbol budgets

Derivative constants depend on dimension and the fixed budget, never on
the number of descriptors. Only a polynomial factor in the list size
enters positive-order derivatives, and this is absorbed into R^sigma.
-/

namespace Falconer
open Set
open scoped ContDiff

/-- The list-size loss in the previous theorem is bounded by R^sigma,
with no dependence on the angular or spatial data. -/
theorem descriptor_count_subpower (C : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type*} (I : Finset ι),
      I.card ≤ (N+1)^C → (I.card : ℝ) ≤ ((2 : ℝ)^N)^σ := by
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_polynomial_subpower C hσ
  refine ⟨N₀,?_⟩
  intro N hN ι I hI
  have hh : (I.card : ℝ) ≤ ((N : ℝ)+1)^C := by exact_mod_cast hI
  apply hh.trans
  exact (pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ)+1)
    (by linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N] : (N : ℝ)+1 ≤ 4*(N : ℝ)+1) C).trans (hN₀ N hN)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Angular masks attached to actual dyadic anchor cells

The spatial dependence is a finite Borel choice of the anchor cell.
On every descendant of an anchor cell, its angular mask is exactly
constant in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def anchoredMask {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (x : Space d) (w : Sphere d) : ℝ :=
  ∑ p ∈ cubePaths d n, if x ∈ (Q.descendant p).carrier then F p w else 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredBufferedMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Buffered masks on the original spatial anchor cells

These masks are jointly measurable, bounded between zero and one, smooth
in every adapted angular chart, and constant in the spatial variable on
all descendants of a reached anchor. Their angular derivative constants
are independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def anchoredBufferedMask {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (S : Finset (Sphere d))
    (U : List (Fin d → Bool) → Set (Sphere d)) : Space d → Sphere d → ℝ :=
  anchoredMask Q g (fun p w => capCutoffAmbient δ hδ S (U p) w)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

abbrev CellPath (d : ℕ) := List (Fin d → Bool)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

abbrev blockDepth (N B i : ℕ) : ℕ := N-i*B

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FrostmanProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frostman lower envelopes for the constructed all-dimensional profiles

The enclosing-ball constant is 2*sqrt d, and the numerical choice of block
length is independent of dimension.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have ht : Filter.Tendsto (fun N : ℕ => ((2:ℝ)^N)^lam) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hlam).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop C))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regular classes of an original Frostman law in arbitrary dimension

This proves the application-level form of Lemma `reg:regularization`.
The classes are unions of the original half-open leaves.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

structure RegularizedProfileData (Q : DyadicCube d) (ρ : Measure (Space d))
    (N : ℕ) (s lam : ℝ) (m : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure ρ
  continuous : Continuous m
  zero : m 0 = 0
  monotone : MonotoneOn m (Icc 0 1)
  lipschitz : LipschitzOnWith (d : NNReal) m (Icc 0 1)
  range : ∀ u ∈ Icc (0:ℝ) 1, m u ∈ Icc (0:ℝ) d
  cells : ∀ j ≤ N, ∀ P : CellPath d, P.length = j → 0 < ρ (Q.descendant P).carrier →
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-m ((j:ℝ)/N)) ≤
        (ρ (Q.descendant P).carrier).toReal ∧
      (ρ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-m ((j:ℝ)/N))
  envelope : ∀ u ∈ Icc (0:ℝ) 1, s*u-((d:ℝ)+4)*lam ≤ m u

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfilePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local occupied-cell counts from the original class profiles -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def occupiedCenterCells (Q : DyadicCube d) (ν : Measure (Space d))
    (p : ℕ) (x : Space d) (r : ℝ) : Finset (CellPath d) := by
  classical
  exact (cubePaths d p).filter fun q => 0 < ν (Q.descendant q).carrier ∧
    (Q.descendant q).center ∈ ball x r

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ConditionalFrostman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale Frostman bounds for the full rescaled conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def profileDrop (m : ℝ → ℝ) (N : ℕ) (s : ℝ) (p t : ℕ) : ℝ :=
  (m p-s*(p:ℝ)/N)-PlanarFalconer.intervalMin (fun n : ℕ => m n-s*(n:ℝ)/N) p t

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_AngularTubeCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean and exceptional mass of a finite original tube count -/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

def angularTubeEvent {d : ℕ} (v : Space d) (W : ℝ) : Set (Sphere d) :=
  {w | ‖perpendicularPart (w:Space d) v‖ ≤ W}

noncomputable def finiteTubeCount {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) : ℕ := by
  classical
  exact (S.filter (fun i => w ∈ angularTubeEvent (v i) W)).card

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual scalar projection law and its sinc collision bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def projectionCollision (μ : Measure (Space d)) (w : Space d) (ε : ℝ) : ℝ≥0∞ :=
  (μ.prod μ) {z : Space d × Space d | |inner ℝ (z.1-z.2) w| ≤ ε}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation of distinct actual dyadic centers in any dimension -/

namespace Falconer

theorem DyadicCube.centers_separated {d n : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    {p q : List (Fin d → Bool)} (hp : p.length = n) (hq : q.length = n) (hpq : p ≠ q) :
    Q.side/(2:ℝ)^n ≤ dist (Q.descendant p).center (Q.descendant q).center := by
  classical
  have hcode : dyadicCode p ≠ dyadicCode q := fun h => hpq (dyadicCode_injective_at_depth hp hq h)
  have hex : ∃ i, dyadicCode p i ≠ dyadicCode q i := by
    by_contra h
    push Not at h
    exact hcode (funext h)
  obtain ⟨i,hi⟩ := hex
  have hz : (1:ℤ) ≤ |dyadicCode p i-dyadicCode q i| := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi) with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have hr : (1:ℝ) ≤ |(dyadicCode p i:ℝ)-(dyadicCode q i:ℝ)| := by exact_mod_cast hz
  have hs : 0 < Q.side/(2:ℝ)^n := by positivity
  have hcoord : (Q.descendant p).center i-(Q.descendant q).center i =
      (Q.side/(2:ℝ)^n)*((dyadicCode p i:ℝ)-(dyadicCode q i:ℝ)) := by
    rw [Q.descendant_center,Q.descendant_center,hp,hq]
    ring
  have hb := PiLp.norm_apply_le ((Q.descendant p).center-(Q.descendant q).center) i
  change |(Q.descendant p).center i-(Q.descendant q).center i| ≤
    ‖(Q.descendant p).center-(Q.descendant q).center‖ at hb
  rw [hcoord,abs_mul,abs_of_pos hs] at hb
  rw [dist_eq_norm]
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ParallelProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The inverse-power sum for actual parallel-test centers

The critical kernel exponent is arbitrary here so the application can
use d/2. Every counted center belongs to the original normalized class.
-/

namespace Falconer.Regularization
open Set Metric MeasureTheory
variable {d : ℕ}

noncomputable def parallelTestCells (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) : Finset (CellPath d) :=
  occupiedCenterCells Q ρ p (Q.descendant P).center (10*((d:ℝ)+1)/(2:ℝ)^g)

noncomputable def parallelTestCount (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : Sphere d) : ℕ :=
  finiteTubeCount (parallelTestCells Q ρ g p P)
    (fun c => (Q.descendant c).center-(Q.descendant P).center) W w

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

namespace Regularization
variable {d : ℕ}

noncomputable def parallelGoodSet (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) : Set (Sphere d) :=
  if 0 < ρ (Q.descendant P).carrier then
    {w | (parallelTestCount Q ρ g p P W w : ℝ≥0∞) ≤ ENNReal.ofReal T} else ∅

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TestWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The width and buffer scales of the all-dimensional tests

These are the exponents 500 and 50 in the all-dimensional test family.
-/

namespace Falconer

noncomputable def angularTestWidth (N : ℕ) (σ : ℝ) (J i n : ℕ) : ℝ :=
  (2-(i:ℝ)/(J:ℝ))/(2:ℝ)^n*((2:ℝ)^N)^(500*σ)

noncomputable def angularTestRadius (N : ℕ) (σ : ℝ) (l : ℕ) : ℝ :=
  min 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*σ))

theorem angularTestRadius_pos (N : ℕ) (σ : ℝ) (l : ℕ) :
    0 < angularTestRadius N σ l := by unfold angularTestRadius; positivity

theorem angularTestWidth_lower (N : ℕ) (σ : ℝ) {J i : ℕ}
    (hJ : 0 < J) (hi : i ≤ J) (n : ℕ) :
    ((2:ℝ)^N)^(500*σ)/(2:ℝ)^n ≤ angularTestWidth N σ J i n := by
  have hj : 0 < (J:ℝ) := Nat.cast_pos.mpr hJ
  have hi' : (i:ℝ) ≤ J := Nat.cast_le.mpr hi
  have hcoeff : 1 ≤ 2-(i:ℝ)/(J:ℝ) := by
    have := (div_le_one hj).mpr hi'
    linarith
  unfold angularTestWidth
  calc
    _ = (1/(2:ℝ)^n)*((2:ℝ)^N)^(500*σ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff (by positivity)) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable projection tests on the full conditional probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def projectionGoodSet (μ : Measure (Space d)) (W T : ℝ) : Set (Sphere d) :=
  {w | projectionCollision μ (w:Space d) W ≤ ENNReal.ofReal T}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

noncomputable def conditionalProjectionGoodSet (Q : DyadicCube d) (ρ : Measure (Space d))
    (P : CellPath d) (W T : ℝ) : Set (Sphere d) :=
  if 0 < ρ (Q.descendant P).carrier then
    projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W T else ∅

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

def descriptorValid (N : ℕ) : PolicyDescriptor → Prop
  | .parallel g p => g ≤ p ∧ p ≤ N
  | .projection p t => p ≤ t ∧ t ≤ N

noncomputable def descriptorGoodDirections (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (P : List (Fin d → Bool)) :
    PolicyDescriptor → Set (Sphere d)
  | .parallel g p => Regularization.parallelGoodSet Q ρ g p P (angularTestWidth N σ J i p)
      (((2:ℝ)^N)^(PlanarFalconer.height
        (fun n : ℕ => m n-((d:ℝ)/2)*(n:ℝ)/N) g p+1000*((d:ℝ)+1)*σ))
  | .projection p t => Regularization.conditionalProjectionGoodSet Q ρ P
      (angularTestWidth N σ J i t)
      ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
        Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

noncomputable def descriptorMaskRadius (N : ℕ) (σ : ℝ) (b : PolicyDescriptor) : ℝ :=
  angularTestRadius N σ (descriptorLength b)/8

theorem descriptorMaskRadius_pos (N : ℕ) (σ : ℝ) (b : PolicyDescriptor) :
    0 < descriptorMaskRadius N σ b := by
  exact div_pos (angularTestRadius_pos N σ _) (by norm_num)

noncomputable def descriptorMask (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) : Space d → Sphere d → ℝ :=
  anchoredBufferedMask Q (descriptorAnchor b) (descriptorMaskRadius N σ b)
    (descriptorMaskRadius_pos N σ b) S
    (fun p => descriptorGoodDirections Q ρ m N σ J (i+1) p b)

def descriptorEndpointGood (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Set (Space d × Sphere d) :=
  {z | ∀ p ∈ cubePaths d (descriptorAnchor b), z.1 ∈ (Q.descendant p).carrier →
    z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}

noncomputable def descriptorPairTests (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) : Set (Space d × Space d) :=
  {z | ∀ b ∈ B,
    (z.1,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b ∧
    (z.2,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition into the suffix cells having a witness

Only actual original-law restrictions occur. Empty intersections with the
parent's good-pair set contribute zero, so retaining witnessed cells is an
exact identity, before their full cell measures are used for comparison.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

noncomputable def testedCellPair (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) : Measure (Space d × Space d) :=
  ((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).restrict G

noncomputable def testedCellDistance (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) : Measure ℝ :=
  (testedCellPair μ ν P Q G).map (fun z => dist z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem dyadic_side_mono {a p : ℕ} (h : a ≤ p) :
    1/(2:ℝ)^p ≤ 1/(2:ℝ)^a :=
  div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphTestScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph widths fit inside the actual parallel tests -/

namespace Falconer

theorem uniform_graph_parallel_width (d : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a g p i : ℕ, a ≤ g → i ≤ J →
      ∀ δ : ℝ, 0 ≤ δ →
      δ ≤ ((2:ℝ)^a/(2:ℝ)^p)*((2:ℝ)^N)^(10*σ) →
      2*((1/(2:ℝ)^p)*((2:ℝ)^N)^(30*σ)) +
        2*δ*(Real.sqrt d*(1/(2:ℝ)^g)) ≤ angularTestWidth N σ J i p := by
  obtain ⟨N₀,h₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 470*σ) (2+2*Real.sqrt d)
  refine ⟨N₀,?_⟩
  intro N hN a g p i hag hi δ _hδ hδbound
  let R := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hscale : δ*(1/(2:ℝ)^g) ≤ (1/(2:ℝ)^p)*R^(10*σ) := by
    calc
      _ ≤ (((2:ℝ)^a/(2:ℝ)^p)*R^(10*σ))*(1/(2:ℝ)^g) :=
        mul_le_mul_of_nonneg_right hδbound (by positivity)
      _ ≤ (((2:ℝ)^a/(2:ℝ)^p)*R^(10*σ))*(1/(2:ℝ)^a) :=
        mul_le_mul_of_nonneg_left (dyadic_side_mono hag) (by positivity)
      _ = _ := by field_simp
  have hpowers : R^(10*σ) ≤ R^(30*σ) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hcoefficient : (2+2*Real.sqrt d)*R^(30*σ) ≤ R^(500*σ) := by
    calc
      _ ≤ R^(470*σ)*R^(30*σ) :=
        mul_le_mul_of_nonneg_right (h₀ N hN) (by positivity)
      _ = _ := by rw [← Real.rpow_add hRpos]; congr 1; ring
  calc
    _ = 2*((1/(2:ℝ)^p)*R^(30*σ)) +
        (2*Real.sqrt d)*(δ*(1/(2:ℝ)^g)) := by ring
    _ ≤ 2*((1/(2:ℝ)^p)*R^(30*σ)) +
        (2*Real.sqrt d)*((1/(2:ℝ)^p)*R^(10*σ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hscale
        (by positivity : 0 ≤ 2*Real.sqrt d))
    _ ≤ 2*((1/(2:ℝ)^p)*R^(30*σ)) +
        (2*Real.sqrt d)*((1/(2:ℝ)^p)*R^(30*σ)) := by gcongr
    _ = ((2+2*Real.sqrt d)*R^(30*σ))/(2:ℝ)^p := by ring
    _ ≤ R^(500*σ)/(2:ℝ)^p :=
      div_le_div_of_nonneg_right hcoefficient (by positivity)
    _ ≤ _ := angularTestWidth_lower N σ hJ hi p

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized near reduction for the actual regularized profile

The child energies retain the original endpoint symbols. No separation of
the parent cells is imposed; the near relation is on their two internal
center displacements, as in the manuscript.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def profileModelMass (m : ℝ → ℝ) (N a : ℕ) : ℝ :=
  ((2:ℝ)^N)^(-m ((a:ℝ)/N))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularEnvelopeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual profile graph estimate on the admissible energy envelope

Restriction to a child is implemented by the existing spatial cell symbol.
The original restricted endpoint integral is unchanged, and the support
condition is propagated explicitly to the child's good set.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

noncomputable def finiteEnvelopeMaximum {ι : Type*} (S : Finset ι) (F : ι → ℝ) : ℝ :=
  sSup (insert 0 (F '' (S : Set ι)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MixedMaskBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixed derivative bounds for the actual buffered angular masks -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem normalizedCap_ambient_derivative_zero {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) (x : Space d)
    (hfar : δ < ‖x-(c : Space d)‖) (k : ℕ) :
    iteratedFDeriv ℝ k (normalizedCap δ hδ S c) x = 0 := by
  have hn : x ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he : normalizedCap δ hδ S c =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change capBump δ hδ c y = (0 : ℝ) at hy
    simp only [normalizedCap,hy,zero_mul]
  simpa using (he.iteratedFDeriv ℝ k).self_of_nhds

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GlobalCapBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global ambient bounds for the actual normalized cap cutoffs

The packing argument works around every ambient point.  The fixed smooth
reciprocal also keeps the sum of all normalized caps between zero and one
off the sphere.  These are the bounds needed by the separated jet operators.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem separated_ambient_overlap {d : ℕ} (S : Finset (Sphere d))
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) (w : Space d) :
    ((S.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d := by
  classical
  let T := S.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)
  have hinj : Function.Injective (fun c : Sphere d => (c : Space d)) := Subtype.val_injective
  have he := separated_ball_card (T.image (fun c : Sphere d => (c : Space d))) w
    (half_pos hδ) hδ.le (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (fun hab => hxy (congrArg Subtype.val hab))) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      simpa only [dist_comm] using (Finset.mem_filter.mp ha).2)
  rw [Finset.card_image_of_injective T hinj] at he
  have hratio : 2*δ/(δ/2)+1 = (5 : ℝ) := by
    field_simp
    norm_num
  simpa only [hratio] using he


theorem capDenominator_global_derivatives (d k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ w : Space d,
      ‖iteratedFDeriv ℝ k (capDenominator δ hδ S) w‖ ≤ B*(δ⁻¹)^k := by
  classical
  obtain ⟨C,hC,hCb⟩ := capBump_ambient_derivatives d k
  refine ⟨5^d*C, by positivity, ?_⟩
  intro δ hδ S hsep w
  let T := S.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)
  let f := fun c : Sphere d => iteratedFDeriv ℝ k (capBump δ hδ c) w
  have hzero (c : Sphere d) (hc : c ∈ S) (hct : c ∉ T) : f c = 0 := by
    have hd : δ < dist w (c : Space d) :=
      lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact capBump_ambient_derivative_zero hδ c w (by
      simpa only [dist_eq_norm] using hd) k
  have hsum : (∑ c ∈ S, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change ‖iteratedFDeriv ℝ k (fun x => ∑ c ∈ S, capBump δ hδ c x) w‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply (n := k)
    (fun c _ => ((capBump δ hδ c).contDiff (n := (k : ℕ∞))).contDiffAt)]
  change ‖∑ c ∈ S, f c‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, ‖f c‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^k := Finset.sum_le_sum (fun c _ => hCb δ hδ c w)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^k) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^d*(C*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right
      (separated_ambient_overlap S hδ hsep w) (by positivity)
    _ = _ := by ring


theorem capReciprocal_global_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ w : Space d,
      ‖iteratedFDeriv ℝ k (capReciprocal δ hδ S) w‖ ≤ C*(δ⁻¹)^k := by
  choose B hB hBb using fun j => capDenominator_global_derivatives d j
  obtain ⟨C,hC,hCb⟩ := compact_iteratedFDeriv_bound
    (smoothReciprocal_contDiff 1 zero_lt_one)
    (isCompact_closedBall (0 : ℝ) (B 0)) k
  refine ⟨mixedCompositionBudget B k*C,
    mul_nonneg (mixedCompositionBudget_nonneg hB k) hC, ?_⟩
  intro δ hδ S hsep w
  have hmem : capDenominator δ hδ S w ∈ Metric.closedBall (0 : ℝ) (B 0) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa using hBb 0 δ hδ S hsep w
  exact mixed_composition_derivative_bound
    (capDenominator_contDiff hδ S).contDiffAt
    (smoothReciprocal_contDiff 1 zero_lt_one).contDiffAt hC k
    (fun j hj => hCb j hj _ hmem)
    (fun j _ _ => hBb j δ hδ S hsep w)

theorem normalizedCap_global_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (c : Sphere d) (w : Space d),
      ‖iteratedFDeriv ℝ k (normalizedCap δ hδ S c) w‖ ≤ C*(δ⁻¹)^k := by
  choose B hB hBb using fun j => capBump_ambient_derivatives d j
  choose Q hQ hQb using fun j => capReciprocal_global_derivatives d j
  let A := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*Q (k-j)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hQ _))
  refine ⟨A,hA,?_⟩
  intro δ hδ S hsep c w
  apply (norm_iteratedFDeriv_mul_le (capBump δ hδ c).contDiff
    (capReciprocal_contDiff hδ S) w (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)).trans
  change _ ≤ (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*B j*Q (k-j))*(δ⁻¹)^k
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (k.choose j : ℝ)*(B j*(δ⁻¹)^j)*(Q (k-j)*(δ⁻¹)^(k-j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hBb j δ hδ c w) (Nat.cast_nonneg _))
        (hQb (k-j) δ hδ S hsep w) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB j) (by positivity)))
    _ = _ := by
      have hp : (δ⁻¹)^j*(δ⁻¹)^(k-j) = (δ⁻¹)^k := by
        rw [← pow_add,Nat.add_sub_of_le hjk]
      calc
        _ = ((k.choose j : ℝ)*B j*Q (k-j))*((δ⁻¹)^j*(δ⁻¹)^(k-j)) := by ring
        _ = _ := by rw [hp]


theorem capCutoffAmbient_global_derivatives (d k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (U : Set (Sphere d)) (w : Space d),
      ‖iteratedFDeriv ℝ k (capCutoffAmbient δ hδ S U) w‖ ≤ B*(δ⁻¹)^k := by
  classical
  obtain ⟨C,hC,hCb⟩ := normalizedCap_global_derivatives d k
  refine ⟨5^d*C, by positivity, ?_⟩
  intro δ hδ S hsep U w
  let S₀ := cutoffCapCenters δ S U
  let T := S₀.filter (fun c : Sphere d => dist w (c : Space d) ≤ δ)
  let f := fun c : Sphere d =>
    iteratedFDeriv ℝ k (normalizedCap δ hδ S c) w
  have hsub : S₀ ⊆ S := Finset.filter_subset _ _
  have hzero (c : Sphere d) (hc : c ∈ S₀) (hct : c ∉ T) : f c = 0 := by
    have hd : δ < dist w (c : Space d) :=
      lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact normalizedCap_ambient_derivative_zero hδ S c w (by
      simpa only [dist_eq_norm] using hd) k
  have hsum : (∑ c ∈ S₀, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change ‖iteratedFDeriv ℝ k (fun x => ∑ c ∈ S₀, normalizedCap δ hδ S c x) w‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply
    (fun c _ => ((normalizedCap_contDiff hδ S c).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  change ‖∑ c ∈ S₀, f c‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, ‖f c‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^k := Finset.sum_le_sum (fun c _ => hCb δ hδ S hsep c w)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^k) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^d*(C*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right
      (separated_ambient_overlap S₀ hδ
        (fun x hx y hy hxy => hsep x (hsub hx) y (hsub hy) hxy) w) (by positivity)
    _ = _ := by ring



theorem smoothReciprocal_nonneg {τ u : ℝ} (hτ : 0 < τ) (hu : 0 ≤ u) :
    0 ≤ smoothReciprocal τ hτ u :=
  mul_nonneg (sub_nonneg.mpr (PlanarFalconer.sineZeroCutoff τ hτ).le_one)
    (inv_nonneg.mpr hu)

theorem mul_smoothReciprocal_le_one {τ u : ℝ} (hτ : 0 < τ) :
    u*smoothReciprocal τ hτ u ≤ 1 := by
  by_cases hu : u = 0
  · simp [hu]
  · calc
      u*smoothReciprocal τ hτ u = 1-PlanarFalconer.sineZeroCutoff τ hτ u := by
        unfold smoothReciprocal
        rw [mul_comm (1-_),← mul_assoc,mul_inv_cancel₀ hu,one_mul]
      _ ≤ 1 := sub_le_self _ (PlanarFalconer.sineZeroCutoff τ hτ).nonneg

theorem normalizedCap_global_nonneg {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) (x : Space d) :
    0 ≤ normalizedCap δ hδ S c x := by
  have hden : 0 ≤ capDenominator δ hδ S x :=
    Finset.sum_nonneg (fun c _ => (capBump δ hδ c).nonneg)
  exact mul_nonneg (capBump δ hδ c).nonneg (smoothReciprocal_nonneg zero_lt_one hden)

theorem normalizedCap_global_sum_le_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (x : Space d) :
    ∑ c ∈ S, normalizedCap δ hδ S c x ≤ 1 := by
  simp only [normalizedCap,← Finset.sum_mul]
  exact mul_smoothReciprocal_le_one zero_lt_one

theorem capCutoffAmbient_global_bounds {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) (x : Space d) :
    0 ≤ capCutoffAmbient δ hδ S U x ∧ capCutoffAmbient δ hδ S U x ≤ 1 := by
  classical
  constructor
  · exact Finset.sum_nonneg (fun c _ => normalizedCap_global_nonneg hδ S c x)
  · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun c _ _ => normalizedCap_global_nonneg hδ S c x))
    exact normalizedCap_global_sum_le_one hδ S x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def descriptorAmbientMask (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x z : Space d) : ℝ :=
  ∑ p ∈ cubePaths d (descriptorAnchor b),
    if x ∈ (Q.descendant p).carrier then
      capCutoffAmbient (descriptorMaskRadius N σ b) (descriptorMaskRadius_pos N σ b) S
        (descriptorGoodDirections Q ρ m N σ J (i+1) p b) z
    else 0

theorem descriptorAmbientMask_on_cell (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (p : List (Fin d → Bool)) (hp : p.length = descriptorAnchor b)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (z : Space d) :
    descriptorAmbientMask Q ρ m N σ J i b S x z =
      capCutoffAmbient (descriptorMaskRadius N σ b) (descriptorMaskRadius_pos N σ b) S
        (descriptorGoodDirections Q ρ m N σ J (i+1) p b) z := by
  unfold descriptorAmbientMask
  rw [Finset.sum_eq_single p]
  · simp only [ite_eq_left hx]
  · intro q hq hqp
    have hdis := Q.descendants_disjoint (((mem_cubePaths d _ q).mp hq).trans hp.symm) hqp
    exact ite_eq_right (fun hq => Set.disjoint_left.mp hdis hq hx)
  · exact fun hn => (hn ((mem_cubePaths d _ p).mpr hp)).elim

theorem descriptorAmbientMask_off_parent (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) {x : Space d} (hx : x ∉ Q.carrier) :
    descriptorAmbientMask Q ρ m N σ J i b S x = fun _ => 0 := by
  funext z
  apply Finset.sum_eq_zero
  intro p _
  exact ite_eq_right (fun hp => hx (Q.descendant_subset p hp))

theorem descriptorAmbientMask_contDiff (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) :
    ContDiff ℝ ∞ (descriptorAmbientMask Q ρ m N σ J i b S x) := by
  apply ContDiff.sum
  intro p _
  by_cases hx : x ∈ (Q.descendant p).carrier
  · simp only [ite_eq_left hx]
    exact capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _
  · simp only [ite_eq_right hx]
    exact contDiff_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DescriptorProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descriptor products and their reached angular factors -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def descriptorProduct (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d) : ℝ :=
  ∏ b ∈ B, descriptorMask Q ρ m N σ J i b (S b) x w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient products preserve every original descriptor support -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

noncomputable def descriptorAmbientProduct (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x z : Space d) : ℝ :=
  ∏ b ∈ B, descriptorAmbientMask Q ρ m N σ J i b (S b) x z

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GlobalDescriptorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global derivative budgets for actual descriptor products

The constants are chosen before the scale, cells, descriptor list and cap
families.  The only list-size loss is a power of its cardinality.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer

theorem descriptorAmbientMask_global_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (x w : Space d),
        ‖iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w‖ ≤
          C*((descriptorMaskRadius N σ b)⁻¹)^k := by
  obtain ⟨C,hC,hCb⟩ := capCutoffAmbient_global_derivatives d k
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep x w
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
      ((mem_cubePaths d _ p).mp hp) hxp)
    rw [he]
    exact hCb _ (descriptorMaskRadius_pos N σ b) S hsep _ w
  · rw [descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx]
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) k)

theorem descriptorAmbientMask_global_bounds {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (x z : Space d) :
    0 ≤ descriptorAmbientMask Q ρ m N σ J i b S x z ∧
      descriptorAmbientMask Q ρ m N σ J i b S x z ≤ 1 := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    rw [descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
      ((mem_cubePaths d _ p).mp hp) hxp]
    exact capCutoffAmbient_global_bounds (descriptorMaskRadius_pos N σ b) S _ z
  · rw [descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx]
    exact ⟨le_rfl,zero_le_one⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ReachedMaskJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized mask derivatives at reached anchors

Reached masks agree as ambient functions throughout a child cell. All their
ambient jets therefore agree too. Radius normalization makes each fixed
order uniformly bounded before any scale or descriptor is selected.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff

noncomputable def normalizedDescriptorJet {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (x : Space d) (w : Sphere d) : ℂ :=
  ((descriptorMaskRadius N σ b)^k *
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w) v : ℝ)


theorem normalizedDescriptorJet_zero {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (v : Fin 0 → Space d)
    (x : Space d) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S 0 v x w =
      (descriptorMask Q ρ m N σ J i b S x w : ℂ) := by
  simp only [normalizedDescriptorJet,pow_zero,iteratedFDeriv_zero_apply,one_mul]
  rfl

theorem normalizedDescriptorJet_bound (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x : Space d) (w : Sphere d), ‖normalizedDescriptorJet Q ρ m N σ J i b S k v x w‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientMask_global_derivatives d k
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x w
  have hr : 0 < descriptorMaskRadius N σ b := descriptorMaskRadius_pos N σ b
  have hprod : (∏ j, ‖v j‖) ≤ 1 :=
    Finset.prod_le_one (fun j _ => norm_nonneg (v j)) (fun j _ => hv j)
  have heval := (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w).le_opNorm v
  have he : |(iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w) v| ≤
      C*((descriptorMaskRadius N σ b)⁻¹)^k := by
    have hh := heval.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)
    exact hh.trans (hbound Q ρ m N σ J i b S hsep x w)
  rw [normalizedDescriptorJet,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (pow_nonneg hr.le k)]
  calc
    _ ≤ (descriptorMaskRadius N σ b)^k*(C*((descriptorMaskRadius N σ b)⁻¹)^k) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hr.le k)
    _ = C := by
      calc
        _ = C*((descriptorMaskRadius N σ b)*((descriptorMaskRadius N σ b)⁻¹))^k := by
          rw [mul_pow]
          ring
        _ = C := by rw [mul_inv_cancel₀ hr.ne',one_pow,mul_one]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed products of actual normalized descriptor derivatives

The index set distinguishes repeated descriptors. Its total derivative
order controls the norm independently of the number of undifferentiated
masks. Reached factors split off as one angular function on each cell.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def descriptorJetProduct {d : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (x : Space d) (w : Sphere d) : ℂ :=
  ∏ j ∈ F, normalizedDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w

theorem normalizedDescriptorJet_order_bound (d K : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ k ≤ K, ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x : Space d) (w : Sphere d),
        ‖normalizedDescriptorJet Q ρ m N σ J i b S k v x w‖ ≤ A^k := by
  classical
  choose C hC hbound using fun k => normalizedDescriptorJet_bound d k
  let A := 1+∑ k ∈ Finset.range (K+1), C k
  have hA : 1 ≤ A := by
    have hsum := Finset.sum_nonneg (fun j _ => hC j) (s := Finset.range (K+1))
    dsimp [A]
    linarith
  refine ⟨A,hA,?_⟩
  intro Q ρ m N σ J i b S hsep k hk v hv x w
  cases k with
  | zero =>
    rw [normalizedDescriptorJet_zero,pow_zero,Complex.norm_real,Real.norm_eq_abs]
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b S x w
    exact (abs_of_nonneg h.1).le.trans h.2
  | succ k =>
    have hCA : C (k+1) ≤ A := by
      have hsum := Finset.single_le_sum (fun j _ => hC j)
        (Finset.mem_range.mpr (by omega : k+1 < K+1))
      dsimp [A]
      linarith
    exact (hbound (k+1) Q ρ m N σ J i b S hsep v hv x w).trans
      (hCA.trans (le_self_pow₀ hA (by omega : k+1 ≠ 0)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebra of individual ambient mask jets

A term contains each original mask exactly once, evaluated at one smooth
angular chart point, with a fixed finite jet on each occurrence. The
coefficient contains only the fixed chart geometry. Differentiation can
therefore distribute to one mask without deleting any other occurrence.
-/

namespace Falconer
open Set
open scoped ContDiff

structure MaskJetIndex (d : ℕ) where
  order : ℕ
  vectors : Fin order → Space d
  norm_vectors : ∀ i, ‖vectors i‖ ≤ 1

namespace MaskJetIndex

noncomputable def zero (d : ℕ) : MaskJetIndex d :=
  ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩

noncomputable def prepend {d : ℕ} (j : MaskJetIndex d) (v : Space d) (hv : ‖v‖ ≤ 1) :
    MaskJetIndex d :=
  ⟨j.order+1,Fin.cons v j.vectors,by intro i; refine Fin.cases hv (fun i => ?_) i; exact j.norm_vectors i⟩

noncomputable def value {d : ℕ} (j : MaskJetIndex d) (B : Space d → ℂ) (z : Space d) : ℂ :=
  iteratedFDeriv ℝ j.order B z j.vectors

@[simp] theorem zero_value (d : ℕ) (B : Space d → ℂ) (z : Space d) :
    (zero d).value B z = B z := rfl

theorem value_contDiff {d : ℕ} (j : MaskJetIndex d) {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (j.value B) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j.order => Space d) ℂ j.vectors).contDiff.comp
    (hB.iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end MaskJetIndex

structure MaskJetTerm (ι : Type*) (d : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  coefficient : E → ℂ
  point : E → Space d
  jet : ι → MaskJetIndex d
  coefficient_smooth : ContDiff ℝ ∞ coefficient
  point_smooth : ContDiff ℝ ∞ point

namespace MaskJetTerm
variable {ι X E H : Type*} {d : ℕ}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def value (T : MaskJetTerm ι d E) (B : ι → X → Space d → ℂ)
    (x : X) (z : E) : ℂ :=
  T.coefficient z * ∏ i, (T.jet i).value (B i x) (T.point z)

def order (T : MaskJetTerm ι d E) : ℕ := ∑ i, (T.jet i).order

noncomputable def mulFixed (T : MaskJetTerm ι d E) (c : E → ℂ) (hc : ContDiff ℝ ∞ c) :
    MaskJetTerm ι d E :=
  ⟨fun z => c z*T.coefficient z,T.point,T.jet,hc.mul T.coefficient_smooth,T.point_smooth⟩

@[simp] theorem mulFixed_value (T : MaskJetTerm ι d E) (c : E → ℂ) (hc : ContDiff ℝ ∞ c)
    (B : ι → X → Space d → ℂ) (x : X) (z : E) :
    (T.mulFixed c hc).value B x z = c z*T.value B x z := by
  simp only [value,mulFixed,mul_assoc]

noncomputable def pullback (T : MaskJetTerm ι d E) (g : H → E) (hg : ContDiff ℝ ∞ g) :
    MaskJetTerm ι d H :=
  ⟨T.coefficient ∘ g,T.point ∘ g,T.jet,T.coefficient_smooth.comp hg,T.point_smooth.comp hg⟩

@[simp] theorem pullback_value (T : MaskJetTerm ι d E) (g : H → E) (hg : ContDiff ℝ ∞ g)
    (B : ι → X → Space d → ℂ) (x : X) (z : H) :
    (T.pullback g hg).value B x z = T.value B x (g z) := rfl

noncomputable def derivativeTerm [DecidableEq ι] (T : MaskJetTerm ι d E)
    (v : E) : Unit ⊕ (ι × Fin d) → MaskJetTerm ι d E
  | .inl _ =>
    ⟨fun z => fderiv ℝ T.coefficient z v,T.point,T.jet,
      (T.coefficient_smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const,T.point_smooth⟩
  | .inr (i,j) =>
    ⟨fun z => T.coefficient z*((fderiv ℝ T.point z v) j : ℂ),T.point,
      Function.update T.jet i ((T.jet i).prepend ((EuclideanSpace.basisFun (Fin d) ℝ) j)
        (by simp)),
      T.coefficient_smooth.mul (Complex.ofRealCLM.contDiff.comp
        ((PiLp.proj 2 (fun _ : Fin d => ℝ) j).contDiff.comp
          ((T.point_smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const))),T.point_smooth⟩

end MaskJetTerm
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseMaskJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse as finite products of individual mask jets

The construction follows the already proved safe-chart inverse recursion.
All mask occurrences survive in every term, and the total order charged to
them is at most twice the inverse index.
-/

namespace Falconer
open scoped ContDiff

structure MaskJetExpansion (ι : Type) (d : ℕ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  index : Type
  finite : Fintype index
  term : index → MaskJetTerm ι d E

attribute [instance] MaskJetExpansion.finite

namespace MaskJetExpansion
variable {ι : Type} {X E H : Type*} {d : ℕ}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def value (S : MaskJetExpansion ι d E)
    (B : ι → X → Space d → ℂ) (x : X) (z : E) : ℂ :=
  ∑ a : S.index, (S.term a).value B x z

def HasOrder (S : MaskJetExpansion ι d E) (K : ℕ) : Prop :=
  ∀ a, (S.term a).order ≤ K

noncomputable def product : MaskJetExpansion ι d (Space d) where
  index := Unit
  finite := inferInstance
  term := fun _ => ⟨fun _ => 1,id,fun _ => MaskJetIndex.zero d,contDiff_const,contDiff_id⟩

@[simp] theorem product_value (B : ι → X → Space d → ℂ) (x : X) (z : Space d) :
    (product : MaskJetExpansion ι d (Space d)).value B x z = ∏ i, B i x z := by
  change (∑ _a : Unit, (1:ℂ)*∏ i, (MaskJetIndex.zero d).value (B i x) z) = _
  simp

noncomputable def mulFixed (S : MaskJetExpansion ι d E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) : MaskJetExpansion ι d E :=
  ⟨S.index,S.finite,fun a => (S.term a).mulFixed c hc⟩

@[simp] theorem mulFixed_value (S : MaskJetExpansion ι d E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) (B : ι → X → Space d → ℂ) (x : X) (z : E) :
    (S.mulFixed c hc).value B x z = c z*S.value B x z := by
  change (∑ a : S.index, ((S.term a).mulFixed c hc).value B x z) = _
  simp only [MaskJetTerm.mulFixed_value,← Finset.mul_sum]
  rfl

noncomputable def pullback (S : MaskJetExpansion ι d E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) : MaskJetExpansion ι d H :=
  ⟨S.index,S.finite,fun a => (S.term a).pullback g hg⟩

@[simp] theorem pullback_value (S : MaskJetExpansion ι d E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) (B : ι → X → Space d → ℂ) (x : X) (z : H) :
    (S.pullback g hg).value B x z = S.value B x (g z) := rfl

noncomputable def sum {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E) :
    MaskJetExpansion ι d E :=
  ⟨(j : J) × (S j).index,inferInstance,fun a => (S a.1).term a.2⟩

@[simp] theorem sum_value {J : Type} [Fintype J] (S : J → MaskJetExpansion ι d E)
    (B : ι → X → Space d → ℂ) (x : X) (z : E) :
    (sum S).value B x z = ∑ j, (S j).value B x z :=
  Fintype.sum_sigma _

noncomputable def derivative [DecidableEq ι] (S : MaskJetExpansion ι d E)
    (v : E) : MaskJetExpansion ι d E :=
  ⟨S.index × (Unit ⊕ (ι × Fin d)),inferInstance,
    fun a => (S.term a.1).derivativeTerm v a.2⟩

noncomputable def laplacian [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) : MaskJetExpansion ι d E :=
  sum (fun j => (S.derivative (v j)).derivative (v j))

noncomputable def iteratedLaplacian [DecidableEq ι] {n : ℕ} (S : MaskJetExpansion ι d E)
    (v : Fin n → E) (j : ℕ) : MaskJetExpansion ι d E :=
  (fun T : MaskJetExpansion ι d E => T.laplacian v)^[j] S

noncomputable def stationaryJet [DecidableEq ι] (m j : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) : MaskJetExpansion ι d (Space (m+3)) :=
  let T := (S.pullback (safeStationaryChart m) (safeStationaryChart_contDiff m)).mulFixed
    (SmoothSeparation.stationaryJointDensity m) (SmoothSeparation.stationaryJointDensity_contDiff m)
  let U := (T.iteratedLaplacian (verticalDirections (m+2)) j).pullback
    (fun e => (e,(0 : Space (m+2)))) (contDiff_id.prodMk contDiff_const)
  U.mulFixed (SmoothSeparation.stationaryJetMultiplier m j)
    (SmoothSeparation.stationaryJetMultiplier_contDiff m j)

noncomputable def inverse [DecidableEq ι] (m : ℕ)
    (S : MaskJetExpansion ι d (Space (m+3))) : ℕ → MaskJetExpansion ι d (Space (m+3))
  | 0 => S.mulFixed (fun e => (sphereStationaryConstant (m+2))⁻¹*(stationaryPatchMask m e : ℂ))
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)))
  | j+1 => (sum (fun h : Fin (j+1) => (inverse m S (j-h)).stationaryJet m (h+1))).mulFixed
      (fun _ => -(sphereStationaryConstant (m+2))⁻¹) contDiff_const
termination_by j => j
decreasing_by omega

/-- Every individual mask jet in the expansion is evaluated at the same point. -/
def HasPointAt (S : MaskJetExpansion ι d E) (z : E) (p : Space d) : Prop :=
  ∀ a, (S.term a).point z = p

end MaskJetExpansion
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorInverseJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Individual radius normalization in the actual inverse expansion

Every mask retains its own radius and derivative order. The extracted
coefficient costs only the largest inverse radius to the total order.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
variable {d : ℕ}

noncomputable def normalizedValue (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℝ) (z : Space d) : ℂ :=
  (r^j.order * (iteratedFDeriv ℝ j.order f z) j.vectors : ℝ)

end MaskJetIndex

namespace MaskJetTerm
variable {ι X E : Type*} {d : ℕ} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def radiusCoefficient (T : MaskJetTerm ι d E) (r : ι → ℝ) (z : E) : ℂ :=
  T.coefficient z * ((∏ i, (r i)⁻¹^(T.jet i).order : ℝ) : ℂ)

end MaskJetTerm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ComplexMaskJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale-normalized jets of the complex angular multiplier

The multiplier is treated as an additional label. Its new derivative
order is charged to the inverse, and its available smoothness budget is
reduced by exactly that order.
-/

namespace Falconer.MaskJetIndex
open Set
open scoped ContDiff
variable {d : ℕ}

noncomputable def scaledValue (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℂ) (z : Space d) : ℂ :=
  r^j.order • j.value f z

theorem scaledValue_contDiff (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (j.scaledValue r f) :=
  (show ContDiff ℝ ∞ (fun z => r^j.order • j.value f z) from
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space d => r^j.order)).smul
      (j.value_contDiff hf))

end Falconer.MaskJetIndex

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularJetSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-budget angular jets as normalized recursive multipliers

A fixed chart constant is selected before the angular multiplier or its
previous derivative order. Taking a jet consumes that exact order from
the ambient budget; normalization does not enlarge the derivative scale.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def normalizedAngular (A : ℝ) {d : ℕ} (B : Space d → ℂ) : Space d → ℂ :=
  fun z => A⁻¹ • B z

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NonstationaryScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scale gain for the angular integration by parts

Depths are normalized by `N`, so `2^p = R^(p/N)`
is represented by `R^p`. The hypotheses and constants are those of
`graph:range` and `graph:ibp-ratio`, without asymptotic notation.
-/

namespace Falconer

theorem graph_nonstationary_ratio_bound {R c₀ σ a p v L : ℝ}
    (hR : 1 ≤ R) (hc₀ : 0 < c₀) (hσ : 0 ≤ σ)
    (hh : p-a ≤ v-p+2*σ) (hL : L ≤ v-p+2*σ) (hq : 10*σ ≤ v-p) :
    (1 + R^σ * max 1 (R^(L-50*σ)) +
        (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a) / R^(-p+30*σ)) /
      (R^v * R^(-p+30*σ)) ≤ (4+c₀⁻¹) * R^(-26*σ) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let t := R^(v-p+4*σ)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by linarith)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have h₁ : R^σ ≤ t := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have h₂ : R^σ * R^(L-50*σ) ≤ t := by
    rw [← Real.rpow_add hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hsymbol : R^σ * max 1 (R^(L-50*σ)) ≤ t := by
    by_cases hx : 1 ≤ R^(L-50*σ)
    · simpa only [max_eq_right hx] using h₂
    · simpa only [max_eq_left (le_of_not_ge hx), mul_one] using h₁
  have hcInv : 0 ≤ c₀⁻¹ := inv_nonneg.mpr hc₀.le
  have hcap : (min c₀ (R^(a-p+10*σ)))⁻¹ ≤ c₀⁻¹ * t + t := by
    by_cases hc : c₀ ≤ R^(a-p+10*σ)
    · rw [min_eq_left hc]
      have hmul := mul_le_mul_of_nonneg_left ht hcInv
      linarith
    · rw [min_eq_right (le_of_not_ge hc), ← Real.rpow_neg hR0.le]
      have hpower : R^(-(a-p+10*σ)) ≤ t :=
        Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      have hmul := mul_nonneg hcInv ht0
      linarith
  have hspatial : R^(-a) / R^(-p+30*σ) ≤ t := by
    rw [← Real.rpow_sub hR0]
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hnum : 1 + R^σ * max 1 (R^(L-50*σ)) +
      (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a) / R^(-p+30*σ) ≤ (4+c₀⁻¹)*t := by
    nlinarith
  have hden : R^v * R^(-p+30*σ) = R^(v-p+30*σ) := by
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  apply (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq
  dsimp only [t]
  rw [hden, mul_div_assoc, ← Real.rpow_sub hR0]
  congr 2
  ring

theorem graph_radial_oscillation_size {R σ p v : ℝ} (hR : 1 ≤ R)
    (hq : 10*σ ≤ v-p) : R^(40*σ) ≤ R^v * R^(-p+30*σ) := by
  rw [← Real.rpow_add (zero_lt_one.trans_le hR)]
  exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapScaleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The cap and cell replacement error at the graph scales

The geometric constant is explicit. The fixed gap between `10σ` and `30σ`
makes the point-replacement and cap-replacement errors less than half the
failed-test threshold once the displayed power inequality holds.
-/

namespace Falconer

theorem graph_cap_replacement_scale {R σ C a p δ : ℝ}
    (hR : 1 ≤ R) (hσ : 0 ≤ σ) (hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (hcap : δ ≤ R^(a-p+10*σ)) :
    2*C*R^(-p)+8*δ*(C*R^(-a)) ≤ 10*C*R^(-p+10*σ) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hfirst : R^(-p) ≤ R^(-p+10*σ) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hsecond : δ*R^(-a) ≤ R^(-p+10*σ) := by
    apply (mul_le_mul_of_nonneg_right hcap (by positivity)).trans_eq
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  have h₁ := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2*C by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 8*C by positivity)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reached differentiated masks in positive independent energy

Every unreached occurrence remains in the endpoint transform. The cost of
removing reached factors depends on the fixed total jet order, not on the
number of undifferentiated masks or the scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def descriptorJetBound (d K : ℕ) : ℝ :=
  (normalizedDescriptorJet_order_bound d K).choose

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_NormalizedJetDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale-normalized ambient derivatives of a single mask -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def normalizedAmbientDescriptorJet {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x z : Space d) : ℝ :=
  (descriptorMaskRadius N σ b)^k *
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) z) v

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FactorizedAngularState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorized symbols used by recursive angular states

The descriptor list is part of the type: every descriptor occurs once,
with an explicitly recorded jet. Passing to a deeper cell filters that
list and keeps the same spatial and smooth angular multipliers.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

structure DescriptorJetSymbol (n K L : ℕ) (F : Finset PolicyDescriptor) (D : ℝ) where
  jet : PolicyDescriptor → MaskJetIndex (n+2)
  order_le : (∑ b ∈ F, (jet b).order) ≤ K
  angular : Space (n+2) → ℂ
  angular_smooth : ContDiff ℝ ∞ angular
  angular_derivative : ∀ t ≤ L, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ t angular w‖ ≤ D^t
  angular_control : ChartSymbolControl L
    (fun (_ : Space (n+2)) (w : Sphere (n+2)) => angular w) 1 D
  spatial : Space (n+2) → ℂ
  spatial_measurable : Measurable spatial
  spatial_bound : ∀ x, ‖spatial x‖ ≤ 1

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def restrict (f : DescriptorJetSymbol n K L F D)
    (G : Finset PolicyDescriptor) (hG : G ⊆ F) : DescriptorJetSymbol n K L G D where
  jet := f.jet
  order_le := (Finset.sum_le_sum_of_subset hG).trans f.order_le
  angular := f.angular
  angular_smooth := f.angular_smooth
  angular_derivative := f.angular_derivative
  angular_control := f.angular_control
  spatial := f.spatial
  spatial_measurable := f.spatial_measurable
  spatial_bound := f.spatial_bound

noncomputable def multiplier (f : DescriptorJetSymbol n K L F D) (A : ℝ)
    (x : Space (n+2)) (w : Sphere (n+2)) : ℂ :=
  f.spatial x*(A⁻¹ : ℝ)*f.angular w

noncomputable def value (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ)
    (x : Space (n+2)) (w : Sphere (n+2)) : ℂ :=
  descriptorJetProduct Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) x w *
      f.multiplier A x w

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ComparableBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Borel dyadic bands for the two original comparable displacements

The finite cover has the exact constants used by the far-cell partner
geometry. Nonnegative integration only needs a cover, so no arbitrary
choice of a depth or additional measurability hypothesis is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem descendant_common_band_scale {d a b : ℕ} (Q : DyadicCube d)
    (hQ : Q.side = 1) (X : List (Fin d → Bool)) (hX : X.length = a) (hab : a ≤ b) :
    (Q.descendant X).side/(2:ℝ)^(b-a) = (2:ℝ)^(-(b:ℝ)) := by
  rw [Q.descendant_side,hQ,hX,div_div,← pow_add,Nat.add_sub_of_le hab]
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FourPointPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original four-point partitions before far rebinning

Each internal pair keeps its original two endpoint restrictions. These
identities allow a nonnegative kernel bound to discard a far-label
selection and then repartition at the common comparable-displacement depth.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def originalFourPointMeasure {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) : Measure ((Space d × Space d) × (Space d × Space d)) :=
  ((μ.restrict P.carrier).prod (μ.restrict P.carrier)).prod
    ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereStationaryAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration for the two stationary poles

These identities retain the original sphere measure and the original
ambient amplitude. The antipodal contribution uses the same smooth pole
patch as the outgoing contribution.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def antipodalConjugate {d : ℕ} (B : Space d → ℂ) (x : Space d) : ℂ :=
  star (B (-x))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full-sphere stationary phase for the actual amplitude

The two pole expansions are combined with the proved off-pole estimate.
The only inputs are the recorded gnomonic surface formula and the precise
quadratic stationary-phase specialization. No spherical estimate is an
assumption.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def directStationarySum (m J : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) : ℂ :=
  ∑ j ∈ Finset.range J, ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*actualStationaryCoefficient m j B e

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual products of two spherical oscillations

The leading expression keeps both signs at each stationary pole. Its
product therefore contains the four radial phases used in the comparable
far reduction. The error uses only norm bounds, never derivatives of a
stationary remainder.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationarySphereApprox (m J : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) : ℂ :=
  ((Λ^(-(((m+2 : ℕ) : ℝ)/2)) : ℝ) : ℂ)*
    (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e+
      star (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ (antipodalConjugate B) e))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root symbols and Fourier operations in the exact descriptor class -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped ContDiff

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def spatialMultiplier (f : DescriptorJetSymbol n K L F D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    DescriptorJetSymbol n K L F D where
  jet := f.jet
  order_le := f.order_le
  angular := f.angular
  angular_smooth := f.angular_smooth
  angular_derivative := f.angular_derivative
  angular_control := f.angular_control
  spatial := fun x => c x*f.spatial x
  spatial_measurable := hc.mul f.spatial_measurable
  spatial_bound := by
    intro x
    rw [norm_mul]
    calc
      _ ≤ (1:ℝ)*1 := mul_le_mul (hcb x) (f.spatial_bound x) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

noncomputable def base (F : Finset PolicyDescriptor) (K L : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    DescriptorJetSymbol n K L F D where
  jet := fun _ => MaskJetIndex.zero (n+2)
  order_le := by simp [MaskJetIndex.zero]
  angular := fun _ => 1
  angular_smooth := contDiff_const
  angular_derivative := by
    intro t _ w
    cases t with
    | zero => simp
    | succ t => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using pow_nonneg hD (t+1)
  angular_control := by
    refine ⟨measurable_const,?_,?_,?_⟩
    · intro x w; simp
    · intro x e y; exact contDiff_const
    · intro e t _ x y _ u _
      cases t with
      | zero => simp [rotatedChartAmplitude,chartAmplitude]
      | succ t =>
        change ‖iteratedDeriv (t+1) (fun _ : ℝ => (1:ℂ)) u‖ ≤ 1*D^(t+1)
        simpa [iteratedDeriv_const] using pow_nonneg hD (t+1)
  spatial := c
  spatial_measurable := hc
  spatial_bound := hcb

noncomputable def conj (f : DescriptorJetSymbol n K L F D) : DescriptorJetSymbol n K L F D where
  jet := f.jet
  order_le := f.order_le
  angular := fun z => star (f.angular z)
  angular_smooth := Complex.conjCLE.contDiff.comp f.angular_smooth
  angular_derivative := by
    intro t ht w
    have he := Complex.conjLIE.norm_iteratedFDeriv_comp_left f.angular (w : Space (n+2)) t
    exact he.le.trans (f.angular_derivative t ht w)
  angular_control := f.angular_control.conj
  spatial := fun x => star (f.spatial x)
  spatial_measurable := continuous_star.measurable.comp f.spatial_measurable
  spatial_bound := fun x => (norm_star _).le.trans (f.spatial_bound x)

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient representatives of the exact recursive symbols

The bound is uniform in the descriptor list and scale. It retains the
ambient representative needed for the full-sphere far expansion.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)


namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}

noncomputable def ambient (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x z : Space (n+2)) : ℂ :=
  f.spatial x*(A⁻¹:ℝ)*
    ((∏ b ∈ F, normalizedAmbientDescriptorJet Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z : ℝ)*f.angular z)

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual stationary amplitudes retain every old descriptor

The far expansion uses these internal endpoint pairs before any reached
mask is removed. Locality of the stationary operator preserves the old
support tests, also for already differentiated masks.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}

noncomputable def pairAmbient (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x y z : Space (n+2)) : ℂ :=
  f.ambient Q ρ m N σ J i S A x z * star (f.ambient Q ρ m N σ J i S A y z)

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_NoncomparableOriginalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The noncomparable contribution on the original four-point law -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

noncomputable def jetStateOriginalKernel {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (T : PolicyDescriptor → Finset (Sphere (m+3))) (Af Ag v : ℝ) (Ψ : ℝ → ℝ)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) : ℂ :=
  ∫ r : ℝ,
    sphereOscillation (r*dist z.1.1 z.1.2) (normalizeToSphere w₀ (z.1.1-z.1.2))
      (fun w => f.value Q ρ profile N σ J i T Af z.1.1 w *
        star (f.value Q ρ profile N σ J i T Af z.1.2 w)) *
    sphereOscillation (r*dist z.2.1 z.2.2) (normalizeToSphere w₀ (z.2.1-z.2.2))
      (fun w => g.value Q ρ profile N σ J i T Ag z.2.1 w *
        star (g.value Q ρ profile N σ J i T Ag z.2.2 w))
    ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual policy suffix transition for positive distance counts -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

noncomputable def policyTestPairs (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) : Set (Space d × Space d) :=
  descriptorPairTests w₀ Q ρ m N σ J i (PlanarFalconer.policyDescriptorList A N q a t)

noncomputable def positiveCollisionCount (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
    ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
        (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
      (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
        (policyTestPairs w₀ Q ρ m A N σ J i q a t)))
      {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t}

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All original descriptor tests survive the full far radial sum -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

noncomputable def jetStateStationaryKernel {m K L : ℕ}
    {F : Finset PolicyDescriptor} {Dq : ℝ}
    (f g : DescriptorJetSymbol (m+1) K L F Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3))) (A : ℝ)
    (M : ℕ) (R : ℝ) (Ψ : ℝ → ℝ)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) : ℂ :=
  R⁻¹ • ∫ r : ℝ, (Ψ (r/R):ℂ)*
    stationarySphereApprox m M (r*dist z.1.1 z.1.2)
      (f.pairAmbient Q ρ profile N σ J i S A z.1.1 z.1.2)
      (normalizeToSphere w₀ (z.1.1-z.1.2))*
    stationarySphereApprox m M (r*dist z.2.1 z.2.2)
      (g.pairAmbient Q ρ profile N σ J i S A z.2.1 z.2.2)
      (normalizeToSphere w₀ (z.2.1-z.2.2))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarCellCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only a dimensional number of partners at a comparable far depth -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def farCellPartners {d : ℕ} (P : DyadicCube d) (ρ : Measure (Space d))
    (n : ℕ) : Finset (List (Fin d → Bool) × List (Fin d → Bool)) :=
  (P.occupiedPaths ρ n ×ˢ P.occupiedPaths ρ n).filter (fun z =>
    125*((d:ℝ)+1)*P.side/(2:ℝ)^n ≤ ‖(P.descendant z.2).center-(P.descendant z.1).center‖ ∧
    ‖(P.descendant z.2).center-(P.descendant z.1).center‖ ≤
      1100*((d:ℝ)+1)*P.side/(2:ℝ)^n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FarPositiveSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive far kernels over the actual comparable cell pairs

The maximum ranges over the original tested distance laws.  The number
of summands is bounded by two free cell labels, not four.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def farCollisionMaximum {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q b t : ℕ)
    (X Y : List (Fin d → Bool)) (n : ℕ) : ℝ≥0∞ :=
  ((farCellPartners (Q.descendant X) ρ n) ×ˢ
    (farCellPartners (Q.descendant Y) ρ n)).sup fun z =>
      max (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (X++z.1.1) (X++z.1.2))
        (positiveCollisionCount w₀ Q ρ m A N σ J i q b t (Y++z.2.1) (Y++z.2.2))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supremum of the factorized recursive angular states

The supremum varies the actual finite jets and the bounded smooth/spatial
multipliers. The displayed descriptor lists and all normalization data stay
fixed. Reached deletion maps each such symbol into the exact shorter list.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def jetStateEnergy {n K L : ℕ} {D : ℝ}
    {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ)
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) : ℝ :=
  independentAngularEnergy a v Ψ
    (fun z => endpointTransform μ M (f.value Q ρ m N σ J i S A) z.1 z.2)
    (fun z => endpointTransform ν P (g.value Q ρ m N σ J i S A) z.1 z.2)

noncomputable def jetStateValues (n K L : ℕ) (D : ℝ) (F G : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {h | ∃ (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D),
    h = jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g}

noncomputable def jetStateEnvelope (n K L : ℕ) (D : ℝ) (F G : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  sSup (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateChildren
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual graph children in the factorized angular envelope -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

noncomputable def childJetStateMaximum (n K L : ℕ) (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  finiteEnvelopeMaximum
    ((Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j)
    (fun row => jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M a v Ψ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual excess profile used by the all-dimensional branch ledger -/

namespace Falconer
open Set
variable {d : ℕ}

noncomputable def profileExcess (m : ℝ → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  m ((j:ℝ)/N)-((d:ℝ)/2)*(j:ℝ)/N

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric data for the actual far branch

These are scale and descriptor conditions to be verified by the recursive
policy. They are not additional published inputs.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

noncomputable def farMinimumLength (d h : ℕ) : ℝ :=
  4*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ))

structure JetStateFarData (m : ℕ) (B : ℝ) where
  Q : DyadicCube (m+3)
  unit : Q.side = 1
  ρ : Measure (Space (m+3))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  regular : Regularization.RegularizedProfileData Q ρ N s lam profile
  N_pos : 0 < N
  a : ℕ
  h : ℕ
  t : ℕ
  ah : a ≤ h
  ht : h+6 ≤ t
  tN : t ≤ N
  σ : ℝ
  J : ℕ
  i : ℕ
  q : ℕ
  policy : ℕ → ℝ
  X : List (Fin (m+3) → Bool)
  Y : List (Fin (m+3) → Bool)
  X_length : X.length = a
  Y_length : Y.length = a
  F : Finset PolicyDescriptor
  masks : PolicyDescriptor → Finset (Sphere (m+3))
  separated : ∀ b ∈ F, ∀ w ∈ masks b, ∀ z ∈ masks b, w ≠ z →
    descriptorMaskRadius N σ b/2 ≤ dist w z
  child_list : ∀ b ∈ Finset.Icc (a+9) (h+6),
    PlanarFalconer.policyDescriptorList policy N q b t ⊆ F
  Dq : ℝ
  Dmask : ℝ
  E : ℝ
  Z : ℝ
  Dq_nonneg : 0 ≤ Dq
  Dmask_one : 1 ≤ Dmask
  Z_pos : 0 < Z
  scale_one : 1 ≤ 2*(E+Dq)
  mask_scale : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask
  list_scale : (F.card:ℝ)*B*Dmask ≤ E
  κ : ℝ
  loss : ℝ
  loss_nonneg : 0 ≤ loss
  scale_upper : 2*(E+Dq) ≤ ((2:ℝ)^N)^2
  band_scale : (2*(E+Dq))^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ))
  large_scale : (2*(E+Dq))^2 ≤ (2:ℝ)^t*farMinimumLength (m+3) h
  large_frequency : ((2:ℝ)^N)^κ ≤ (2:ℝ)^t*farMinimumLength (m+3) h
  shell_one : 1 ≤ ((2:ℝ)^t/4)*farMinimumLength (m+3) h
  shell_scale : (2*(E+Dq))^2/(((2:ℝ)^t/4)*farMinimumLength (m+3) h) ≤ ((2:ℝ)^N)^(-κ)

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

noncomputable def originalMeasure (D : JetStateFarData m B) :=
  originalFourPointMeasure (D.Q.descendant D.X) (D.Q.descendant D.Y) D.ρ D.ρ

noncomputable def prefactor (D : JetStateFarData m B) : ℝ :=
  (2:ℝ)^(((m+3:ℕ):ℝ)*((D.t:ℝ)-D.a))*(profileModelMass D.profile D.N D.a)⁻¹^4

noncomputable def kernel (D : JetStateFarData m B) {K L : ℕ}
    (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)) (Ψ : ℝ → ℝ) :=
  jetStateOriginalKernel f g w₀ D.Q D.ρ (fun t => D.profile (t/D.N))
    D.N D.σ D.J D.i D.masks D.Z D.Z D.t Ψ

noncomputable def stationaryKernel (D : JetStateFarData m B) {K L : ℕ}
    (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3))
    (J : ℕ) (Ψ : ℝ → ℝ) :=
  jetStateStationaryKernel f g w₀ D.Q D.ρ (fun t => D.profile (t/D.N))
    D.N D.σ D.J D.i D.masks D.Z J ((2:ℝ)^D.t) Ψ

noncomputable def collisionTerm (D : JetStateFarData m B) (w₀ : Sphere (m+3))
    (C : ℝ) (b : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    ((2:ℝ)^D.N)^(-2*((D.profile ((b:ℝ)/D.N)-((m+3:ℕ):ℝ)/2*(b:ℝ)/D.N)-
      (D.profile ((D.a:ℝ)/D.N)-((m+3:ℕ):ℝ)/2*(D.a:ℝ)/D.N))+4*(((m+3:ℕ):ℝ)+1)*D.lam)) *
    (PlanarFalconer.binKernelConstant * farCollisionMaximum w₀ D.Q D.ρ
      (fun t => D.profile (t/D.N)) D.policy D.N D.σ D.J (D.i+1) D.q b D.t D.X D.Y (b-D.a))

end JetStateFarData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FarAngularStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conditional angular far branch, with the actual near child

This is the analytic far step of the recursive argument. Its inputs are
geometric scale data; only the cited gnomonic and quadratic stationary
results are published hypotheses.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

noncomputable def energy (D : JetStateFarData m B) {K L : ℕ}
    (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (Ψ : ℝ → ℝ) : ℝ :=
  jetStateEnergy D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.Z
    (D.ρ.restrict (D.Q.descendant D.X).carrier) (D.ρ.restrict (D.Q.descendant D.Y).carrier)
    (profileModelMass D.profile D.N D.a) (profileModelMass D.profile D.N D.a) D.a D.t Ψ f g

noncomputable def nearBound (D : JetStateFarData m B) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ) *
    ((2:ℝ)^D.N)^(-2*(profileExcess (d := m+3) D.profile D.N D.h-
      profileExcess (d := m+3) D.profile D.N D.a)+4*(((m+3:ℕ):ℝ)+1)*D.lam)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
      childJetStateMaximum (m+1) K L D.Dq (D.F.filter (fun b => D.h < PlanarFalconer.descriptorAnchor b))
        D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.Z D.X D.Y (D.h-D.a)
        (profileModelMass D.profile D.N D.h) D.h D.t Ψ)

end JetStateFarData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FilteredLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits of decreasing original-pair filters

For the manuscript application, `ρ` is the original product measure with
the bounded distance weight, and `f` is the original distance map. These
lemmas do not replace distances by those of any auxiliary projection.
-/

namespace Falconer
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def filteredPushforward (f : X → Y) (ρ : Measure X) (G : Set X) : Measure Y :=
  Measure.map f (ρ.restrict G)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedLowpass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive lowpass comparison for the actual masked distance law

The comparison is made between positive measures before taking Fourier
transforms. All old masks remain in the weighted distance pushforward.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def descriptorPairWeight (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (z : Space d × Space d) : ℝ :=
  (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2)) *
    descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1 (normalizeToSphere w₀ (z.1-z.2)) *
    descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2 (normalizeToSphere w₀ (z.1-z.2))

noncomputable def maskedCellDistance (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (X Y : DyadicCube d) : Measure ℝ :=
  (((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).withDensity
    (fun z => ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 *
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z))).map
    (fun z => dist z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ActualFarBuffer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem sourceFarBuffer_ge_length (N L : ℕ) (sig : ℝ) : L ≤ sourceFarBuffer N L sig :=
  le_max_left _ _

theorem sourceFarBuffer_ge_slack (N L : ℕ) (sig : ℝ) :
    10*sig*(N:ℝ) ≤ (sourceFarBuffer N L sig:ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorDerivativeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derivative scale for the actual descriptor family

The fixed derivative constants and polynomial list size are absorbed before
choosing any cells, net points or descriptor family. The retained scale
remembers the largest nominal descriptor length.
-/

namespace Falconer
open Set MeasureTheory

noncomputable def descriptorDerivativeScale (N : ℕ) (σ : ℝ) (L : ℕ) : ℝ :=
  ((2:ℝ)^N)^σ * max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))

theorem descriptorMaskRadius_inv_eq (N : ℕ) (σ : ℝ) (b : PlanarFalconer.PolicyDescriptor) :
    (descriptorMaskRadius N σ b)⁻¹ =
      8*max 1 ((2:ℝ)^(PlanarFalconer.descriptorLength b)*((2:ℝ)^N)^(-50*σ)) := by
  let t : ℝ := 1/(2:ℝ)^(PlanarFalconer.descriptorLength b)*((2:ℝ)^N)^(50*σ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hi : t⁻¹ = (2:ℝ)^(PlanarFalconer.descriptorLength b)*((2:ℝ)^N)^(-50*σ) := by
    rw [show -50*σ = -(50*σ) by ring,Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)^N)]
    simp only [t,mul_inv_rev,one_div,inv_inv]
    ring
  change (min 1 t/8)⁻¹ = _
  rw [inv_div]
  by_cases h : t ≤ 1
  · rw [min_eq_right h,← hi,max_eq_right ((one_le_inv₀ ht).mpr h),div_eq_mul_inv]
  · rw [min_eq_left (le_of_not_ge h),← hi,max_eq_left ((inv_le_one₀ ht).mpr (le_of_not_ge h))]
    norm_num

theorem descriptorMaskRadius_inv_le (N : ℕ) (σ : ℝ)
    (b : PlanarFalconer.PolicyDescriptor) {L : ℕ} (hL : PlanarFalconer.descriptorLength b ≤ L) :
    (descriptorMaskRadius N σ b)⁻¹ ≤
      8*max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ)) := by
  rw [descriptorMaskRadius_inv_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hL) (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorInverseRegime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual descriptor derivative scale is in the inverse regime

The high-frequency condition and the retained descriptor length give a
uniform gap between the squared derivative scale and the oscillation.
The fixed shell factor four is absorbed before selecting any cells.
-/

namespace Falconer

theorem dyadic_nat_rpow (N : ℕ) (t : ℝ) :
    ((2 : ℝ)^N)^t = (2 : ℝ)^((N : ℝ)*t) :=
  (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) N t).symm

theorem dyadic_square_div (u q : ℝ) :
    ((2 : ℝ)^u)^2/(2 : ℝ)^q = (2 : ℝ)^(2*u-q) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem descriptorDerivativeScale_le_square (N L : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hLN : L ≤ N) :
    descriptorDerivativeScale N σ L ≤ ((2 : ℝ)^N)^2 := by
  let R := (2 : ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hr : R^σ ≤ R := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR hσ1
  have hneg : R^(-50*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hw : max 1 ((2 : ℝ)^L*R^(-50*σ)) ≤ R := by
    apply max_le hR
    calc
      _ ≤ (2 : ℝ)^L*1 := mul_le_mul_of_nonneg_left hneg (by positivity)
      _ ≤ R := by simpa only [mul_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hLN
  change R^σ*max 1 ((2 : ℝ)^L*R^(-50*σ)) ≤ R^2
  exact (mul_le_mul hr hw (by positivity) (by positivity)).trans_eq (by ring)

theorem descriptorDerivativeScale_inverse_ratio (N L : ℕ) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq : 20*σ*(N : ℝ) ≤ q)
    (hL : (L : ℝ) ≤ q/2+σ*(N : ℝ)) :
    (descriptorDerivativeScale N σ L)^2/(2 : ℝ)^q ≤ ((2 : ℝ)^N)^(-18*σ) := by
  have hσN : 0 ≤ σ*(N : ℝ) := mul_nonneg hσ (Nat.cast_nonneg _)
  by_cases hw : (2 : ℝ)^L*((2 : ℝ)^N)^(-50*σ) ≤ 1
  · have he : descriptorDerivativeScale N σ L = (2 : ℝ)^((N : ℝ)*σ) := by
      rw [descriptorDerivativeScale,max_eq_left hw,mul_one,dyadic_nat_rpow]
    rw [he,dyadic_square_div,dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  · have he : descriptorDerivativeScale N σ L =
        (2 : ℝ)^((L : ℝ)-49*σ*(N : ℝ)) := by
      rw [descriptorDerivativeScale,max_eq_right (le_of_not_ge hw),
        dyadic_nat_rpow N σ,dyadic_nat_rpow N (-50*σ),← Real.rpow_natCast (2 : ℝ) L,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [he,dyadic_square_div,dyadic_nat_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarPolicyScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive split supplies the far-branch scale conditions

The estimates use the actual largest remaining descriptor length. The
angular multiplier scale is one, which is preserved by the normalized
inverse construction. All constants are chosen before the terminal depth.
-/

namespace Falconer
open PlanarFalconer (PolicyDescriptor)

noncomputable def descriptorListScale (B : ℝ) (N : ℕ) (σ : ℝ) (L : ℕ)
    (F : Finset PolicyDescriptor) : ℝ :=
  (F.card:ℝ)*B*(8*max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ)))

theorem eventual_descriptor_list_scale (P : ℕ) {B σ : ℝ}
    (hB : 1 ≤ B) (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ F : Finset PolicyDescriptor,
      F.card ≤ (N+1)^P →
      4 ≤ descriptorDerivativeScale N σ L ∧
      2*(descriptorListScale B N σ L F+1) ≤ descriptorDerivativeScale N σ L := by
  obtain ⟨N₁,hcount⟩ := descriptor_count_subpower P (half_pos hσ)
  obtain ⟨N₂,hconstant⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) (32*B)
  obtain ⟨N₃,hfour⟩ := Regularization.fixed_constant_absorbed hσ 4
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN L F hcard
  have h₁ := hcount N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) F hcard
  have h₂ := hconstant N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have h₃ := hfour N ((le_max_right _ _).trans hN)
  let W := max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*σ))
  have hW : 1 ≤ W := le_max_left _ _
  have hprod : (F.card:ℝ)*(32*B) ≤ ((2:ℝ)^N)^σ := by
    calc
      _ ≤ ((2:ℝ)^N)^(σ/2)*((2:ℝ)^N)^(σ/2) :=
        mul_le_mul h₁ h₂ (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hscale : 4 ≤ descriptorDerivativeScale N σ L := by
    exact h₃.trans (le_mul_of_one_le_right (by positivity) hW)
  have hlist : descriptorListScale B N σ L F ≤ descriptorDerivativeScale N σ L/4 := by
    have hh := mul_le_mul_of_nonneg_right hprod (show 0 ≤ W from zero_le_one.trans hW)
    change (F.card:ℝ)*B*(8*W) ≤ ((2:ℝ)^N)^σ*W/4
    nlinarith
  exact ⟨hscale,by linarith⟩

/-- Every geometric frequency condition in `JetStateFarData` follows from
the split gap and the largest descriptor length. -/
theorem eventual_far_split_scales (d : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L h t : ℕ, L ≤ N → h ≤ t →
      20*σ*(N:ℝ) ≤ (t:ℝ)-h → 2*(L:ℝ) ≤ (t:ℝ)-h →
      ∀ D : ℝ, 1 ≤ D → D ≤ descriptorDerivativeScale N σ L →
      h+6 ≤ t ∧ D ≤ ((2:ℝ)^N)^2 ∧
      D^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ)) ∧
      D^2 ≤ (2:ℝ)^t*farMinimumLength d h ∧
      ((2:ℝ)^N)^(16*σ) ≤ (2:ℝ)^t*farMinimumLength d h ∧
      1 ≤ ((2:ℝ)^t/4)*farMinimumLength d h ∧
      D^2/(((2:ℝ)^t/4)*farMinimumLength d h) ≤ ((2:ℝ)^N)^(-16*σ) := by
  obtain ⟨N₀,hlarge⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < 18*σ) 64
  refine ⟨N₀,?_⟩
  intro N hN L h t hLN hht hgap hlength D hD hDs
  let R := (2:ℝ)^N
  let gap : ℝ := (t:ℝ)-h
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hσN : 0 ≤ σ*(N:ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hrat := descriptorDerivativeScale_inverse_ratio N L hσ.le hgap
    (show (L:ℝ) ≤ gap/2+σ*(N:ℝ) by dsimp [gap]; linarith)
  have hratD : D^2/(2:ℝ)^gap ≤ R^(-18*σ) :=
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hD) hDs 2)
      (by positivity)).trans hrat
  have h64 : (64:ℝ) ≤ R^(18*σ) := hlarge N hN
  have h18 : R^(18*σ) ≤ (2:ℝ)^gap := by
    rw [show R^(18*σ) = (2:ℝ)^((N:ℝ)*(18*σ)) from
      (Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (18*σ)).symm]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [gap]
    nlinarith
  have hgap6 : (6:ℝ) ≤ gap := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp
    convert h64.trans h18 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hht6 : h+6 ≤ t := by
    have hh : (h:ℝ)+6 ≤ t := by dsimp [gap] at hgap6; linarith
    exact_mod_cast hh
  have hsmall : R^(-18*σ) ≤ (64:ℝ)⁻¹ := by
    rw [show -18*σ = -(18*σ) by ring,Real.rpow_neg hRp.le]
    exact (inv_le_inv₀ (by positivity : 0 < R^(18*σ)) (by norm_num : (0:ℝ) < 64)).mpr h64
  have hband : D^2 ≤ (2:ℝ)^((t:ℝ)-(h+6:ℕ)) := by
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^gap)).mp (hratD.trans hsmall)
    have he : (2:ℝ)^((t:ℝ)-(h+6:ℕ)) = (2:ℝ)^gap/64 := by
      rw [Nat.cast_add,Nat.cast_ofNat,show (t:ℝ)-((h:ℝ)+6) = gap-6 by dsimp [gap]; ring,
        Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    nlinarith
  have hden : ((2:ℝ)^t/4)*farMinimumLength d h = ((d:ℝ)+1)*(2:ℝ)^gap := by
    unfold farMinimumLength
    rw [← Real.rpow_natCast (2:ℝ) t]
    calc
      _ = ((d:ℝ)+1)*((2:ℝ)^(t:ℝ)*(2:ℝ)^(-(h:ℝ))) := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; rfl
  have hdenle : (2:ℝ)^gap ≤ ((2:ℝ)^t/4)*farMinimumLength d h := by
    rw [hden]
    exact le_mul_of_one_le_left (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hratioOne : R^(-18*σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hDsquare : D^2 ≤ (2:ℝ)^gap :=
    (div_le_one (by positivity : 0 < (2:ℝ)^gap)).mp (hratD.trans hratioOne)
  have hlargeD : D^2 ≤ (2:ℝ)^t*farMinimumLength d h := by
    have hp : 0 ≤ (2:ℝ)^t*farMinimumLength d h := by unfold farMinimumLength; positivity
    exact (hDsquare.trans hdenle).trans (by linarith)
  have hfreq : R^(16*σ) ≤ (2:ℝ)^gap := by
    apply (Real.rpow_le_rpow_of_exponent_le hR (by linarith : 16*σ ≤ 18*σ)).trans h18
  have hfreqLarge : R^(16*σ) ≤ (2:ℝ)^t*farMinimumLength d h := by
    have hp : 0 ≤ (2:ℝ)^t*farMinimumLength d h := by unfold farMinimumLength; positivity
    exact (hfreq.trans hdenle).trans (by linarith)
  have hone : 1 ≤ ((2:ℝ)^t/4)*farMinimumLength d h :=
    (one_le_pow₀ hD).trans (hDsquare.trans hdenle)
  refine ⟨hht6,hDs.trans (descriptorDerivativeScale_le_square N L hσ.le hσ1 hLN),
    hband,hlargeD,hfreqLarge,hone,?_⟩
  exact ((div_le_div_of_nonneg_left (sq_nonneg D) (by positivity) hdenle).trans hratD).trans
    (Real.rpow_le_rpow_of_exponent_le hR (by linarith : -18*σ ≤ -16*σ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InheritedPolicyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem policyDescriptor_anchor_gt_left (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) : a < descriptorAnchor d := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,_,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  rw [originDescriptor_anchor A hd]
  omega

 theorem minimal_policy_list_survives (A : ℕ → ℝ) {N q a₀ t₀ a b v : ℕ}
    (hq : 0 < q) (hleft : a₀ ≤ b) (hright : v ≤ t₀) (hdepth : a ≤ b) :
    policyDescriptorList A N q b v ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  exact Finset.mem_filter.mpr ⟨policyDescriptorList_mono A hleft hright hd,
    hdepth.trans_lt (policyDescriptor_anchor_gt_left A hq hd)⟩

 theorem remainingPolicyDescriptors_mono (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    remainingPolicyDescriptors A N q a₀ t₀ p ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  obtain ⟨hd,hp⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd,hap.trans_lt hp⟩

 theorem remainingPolicyDescriptors_card (A : ℕ → ℝ) {N q a₀ t₀ a : ℕ} (hq : 0 < q) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).card ≤ (N+1)^3 :=
  (Finset.card_filter_le _ _).trans (policyDescriptorList_card A hq)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_MinimalDescriptorLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length_le_anchor (A : ℕ → ℝ) {N q b u : ℕ}
    {d : PolicyDescriptor} (hd : d ∈ originDescriptors A N q b u) :
    descriptorLength d ≤ descriptorAnchor d := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.sub_le _ _
  · split_ifs at hd with h
    · obtain rfl := Finset.mem_singleton.mp hd
      dsimp [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_twice_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    a + 2*descriptorLength d ≤ t := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,ht,hw⟩ := Finset.mem_filter.mp hz
  have hu := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hl := originDescriptor_length A hq hu hw hd
  have hp := originDescriptor_length_le_anchor A hd
  omega

theorem policyDescriptor_length_le_half (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    descriptorLength d ≤ (t-a)/2 := by
  have := policyDescriptor_twice_length A hq hd
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PolicyJetData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual retained policy list supplies the far analytic data -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor remainingPolicyDescriptors descriptorLength)

/-- Data retained during an angular episode. Its descriptor list and split
are computed from the inherited positive interval. -/
structure PolicyJetData (m : ℕ) where
  Q : DyadicCube (m+3)
  unit : Q.side = 1
  ρ : Measure (Space (m+3))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  regular : Regularization.RegularizedProfileData Q ρ N s lam profile
  N_pos : 0 < N
  σ : ℝ
  J : ℕ
  i : ℕ
  q : ℕ
  q_pos : 0 < q
  policy : ℕ → ℝ
  a₀ : ℕ
  t₀ : ℕ
  a : ℕ
  t : ℕ
  base_left : a₀ ≤ a
  base_right : t ≤ t₀
  base_N : t₀ ≤ N
  X : List (Fin (m+3) → Bool)
  Y : List (Fin (m+3) → Bool)
  X_length : X.length = a
  Y_length : Y.length = a
  masks : PolicyDescriptor → Finset (Sphere (m+3))
  separated : ∀ b ∈ remainingPolicyDescriptors policy N q a₀ t₀ a,
    ∀ w ∈ masks b, ∀ z ∈ masks b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z
  Z : ℝ
  Z_pos : 0 < Z

namespace PolicyJetData
variable {m : ℕ}

noncomputable def list (P : PolicyJetData m) :=
  remainingPolicyDescriptors P.policy P.N P.q P.a₀ P.t₀ P.a

noncomputable def longest (P : PolicyJetData m) := P.list.sup descriptorLength

noncomputable def splitDepth (P : PolicyJetData m) :=
  P.t-2*PlanarFalconer.sourceFarBuffer P.N P.longest P.σ

theorem list_card (P : PolicyJetData m) : P.list.card ≤ (P.N+1)^3 :=
  PlanarFalconer.remainingPolicyDescriptors_card P.policy P.q_pos

theorem longest_le_N (P : PolicyJetData m) : P.longest ≤ P.N := by
  apply Finset.sup_le
  intro b hb
  have hbase := (Finset.mem_filter.mp hb).1
  have hh := PlanarFalconer.policyDescriptor_twice_length P.policy P.q_pos hbase
  have := P.base_N
  omega

theorem split_gap (P : PolicyJetData m) (hfar : P.a < P.splitDepth) :
    20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.splitDepth ∧
      2*(P.longest:ℝ) ≤ (P.t:ℝ)-P.splitDepth := by
  have ht : 2*PlanarFalconer.sourceFarBuffer P.N P.longest P.σ ≤ P.t := by
    change P.a < P.t-2*PlanarFalconer.sourceFarBuffer P.N P.longest P.σ at hfar
    omega
  have he : (P.t:ℝ)-P.splitDepth =
      2*(PlanarFalconer.sourceFarBuffer P.N P.longest P.σ:ℝ) := by
    rw [splitDepth,Nat.cast_sub ht,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [he]
  have hs := PlanarFalconer.sourceFarBuffer_ge_slack P.N P.longest P.σ
  have hl : (P.longest:ℝ) ≤ (PlanarFalconer.sourceFarBuffer P.N P.longest P.σ:ℝ) :=
    Nat.cast_le.mpr (PlanarFalconer.sourceFarBuffer_ge_length P.N P.longest P.σ)
  constructor <;> linarith

noncomputable def farThreshold (B σ : ℝ) (hB : 1 ≤ B) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (m : ℕ) : ℕ :=
  max (Classical.choose (eventual_descriptor_list_scale 3 hB hσ))
    (Classical.choose (eventual_far_split_scales (m+3) hσ hσ1))

/-- The retained list and prescribed split determine the analytic data.
No frequency assumption is supplied by the caller. -/
noncomputable def farData (P : PolicyJetData m) (B : ℝ)
    (hB : 1 ≤ B) (hσ : 0 < P.σ) (hσ1 : P.σ ≤ 1)
    (hN : farThreshold B P.σ hB hσ hσ1 m ≤ P.N)
    (hfar : P.a < P.splitDepth) (loss : ℝ) (hloss : 0 ≤ loss) : JetStateFarData m B := by
  let Dmask := 8*max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ))
  let E := descriptorListScale B P.N P.σ P.longest P.list
  have hlist := (Classical.choose_spec (eventual_descriptor_list_scale 3 hB hσ)) P.N
    ((le_max_left _ _).trans hN) P.longest P.list P.list_card
  have hE : 0 ≤ E := by dsimp [E,descriptorListScale]; positivity
  have hD : 1 ≤ 2*(E+1) := by linarith
  have hs := (Classical.choose_spec (eventual_far_split_scales (m+3) hσ hσ1)) P.N
    ((le_max_right _ _).trans hN) P.longest P.splitDepth P.t P.longest_le_N
    (Nat.sub_le _ _) (P.split_gap hfar).1 (P.split_gap hfar).2 (2*(E+1)) hD hlist.2
  refine {
    Q := P.Q, unit := P.unit, ρ := P.ρ, profile := P.profile, N := P.N,
    s := P.s, lam := P.lam, regular := P.regular, N_pos := P.N_pos,
    a := P.a, h := P.splitDepth, t := P.t, ah := hfar.le, ht := hs.1,
    tN := P.base_right.trans P.base_N, σ := P.σ, J := P.J, i := P.i,
    q := P.q, policy := P.policy, X := P.X, Y := P.Y,
    X_length := P.X_length, Y_length := P.Y_length,
    F := P.list, masks := P.masks, separated := P.separated,
    child_list := ?_, Dq := 1, Dmask := Dmask, E := E, Z := P.Z,
    Dq_nonneg := by norm_num, Dmask_one := ?_, Z_pos := P.Z_pos,
    scale_one := hD, mask_scale := ?_, list_scale := le_rfl,
    κ := 16*P.σ, loss := loss, loss_nonneg := hloss,
    scale_upper := hs.2.1, band_scale := hs.2.2.1,
    large_scale := hs.2.2.2.1, large_frequency := hs.2.2.2.2.1,
    shell_one := hs.2.2.2.2.2.1,
    shell_scale := by simpa only [neg_mul] using hs.2.2.2.2.2.2 }
  · intro b hb
    have hab : P.a ≤ b := by have := (Finset.mem_Icc.mp hb).1; omega
    exact PlanarFalconer.minimal_policy_list_survives P.policy P.q_pos
      (P.base_left.trans hab) P.base_right hab
  · have hh : 1 ≤ max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ)) := le_max_left _ _
    dsimp [Dmask]
    linarith
  · intro b hb
    exact descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PolicyPositiveBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive policy count from its actual Fourier bands -/

namespace Falconer
open Set MeasureTheory

namespace PolicyJetData
variable {m : ℕ}

def atFrequency (P : PolicyJetData m) (v : ℕ) (hv : v ≤ P.t₀) : PolicyJetData m :=
  { P with t := v, base_right := hv }

def positiveSuccessor (P : PolicyJetData m) (v : ℕ) (hv : v ≤ P.t₀) (i : ℕ) : PolicyJetData m :=
  { P with
    a₀ := P.a
    t₀ := v
    t := v
    i := i
    base_left := le_rfl
    base_right := le_rfl
    base_N := hv.trans P.base_N
    separated := by
      intro b hb
      apply P.separated b
      obtain ⟨hb,ha⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨PlanarFalconer.policyDescriptorList_mono P.policy P.base_left hv hb,ha⟩ }

noncomputable def positiveCount (P : PolicyJetData m) (w₀ : Sphere (m+3)) : ℝ :=
  (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
    P.N P.σ P.J P.i P.q P.a P.t P.X P.Y).toReal

noncomputable def maskedLaw (P : PolicyJetData m) (w₀ : Sphere (m+3)) : Measure ℝ :=
  maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
    P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The far reduction for the full recursive symbol supremum -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

noncomputable def envelope (D : JetStateFarData m B) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  jetStateEnvelope (m+1) K L D.Dq D.F D.F D.Q D.ρ (fun t => D.profile (t/D.N))
    D.N D.σ D.J D.i D.masks D.Z
    (D.ρ.restrict (D.Q.descendant D.X).carrier) (D.ρ.restrict (D.Q.descendant D.Y).carrier)
    (profileModelMass D.profile D.N D.a) (profileModelMass D.profile D.N D.a) D.a D.t Ψ

noncomputable def farError (D : JetStateFarData m B) (K : ℕ) (Cerr : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal D.prefactor *
    (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
    ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ

end JetStateFarData

namespace PolicyJetData
variable {m : ℕ}

noncomputable def envelope (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  jetStateEnvelope (m+1) K L 1 P.list P.list P.Q P.ρ (fun t => P.profile (t/P.N))
    P.N P.σ P.J P.i P.masks P.Z
    (P.ρ.restrict (P.Q.descendant P.X).carrier) (P.ρ.restrict (P.Q.descendant P.Y).carrier)
    (profileModelMass P.profile P.N P.a) (profileModelMass P.profile P.N P.a) P.a P.t Ψ

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial term count in the individual-mask inverse expansion -/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [Fintype ι] in
@[simp] theorem card_mulFixed (S : MaskJetExpansion ι d E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) :
    Fintype.card (S.mulFixed c hc).index = Fintype.card S.index := rfl

omit [Fintype ι] in
@[simp] theorem card_pullback (S : MaskJetExpansion ι d E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) :
    Fintype.card (S.pullback g hg).index = Fintype.card S.index := rfl

def inverseMultiplicity (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => ∑ h : Fin (j+1), inverseMultiplicity n (j-h) * n^((h:ℕ)+1)
termination_by j => j
decreasing_by omega

end Falconer.MaskJetExpansion

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family for the inverse's geometric coefficients

Changing which mask receives a derivative changes its jet index, but not
the smooth coefficient or evaluation point. Collapse all mask choices to
one label to obtain a coefficient family independent of the list length.
-/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι τ : Type} {d : ℕ} {E H : Type*}
  [Fintype ι] [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def GeometryCoveredBy (S : MaskJetExpansion ι d E) (T : MaskJetExpansion τ d E) : Prop :=
  ∀ a, ∃ b, (S.term a).coefficient = (T.term b).coefficient ∧
    (S.term a).point = (T.term b).point

end Falconer.MaskJetExpansion

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Starting the inverse expansion with existing individual mask jets

Previously charged derivatives remain in their original occurrences. The
new inverse adds at most twice its index to the total order, and radius
normalization cancels every previously charged power exactly.
-/

namespace Falconer.MaskJetExpansion
open scoped ContDiff
variable {ι : Type} {d : ℕ} {E H X : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def seed (k : ι → MaskJetIndex d) : MaskJetExpansion ι d (Space d) where
  index := Unit
  finite := inferInstance
  term := fun _ => ⟨fun _ => 1,id,k,contDiff_const,contDiff_id⟩

def OrdersExtend (S : MaskJetExpansion ι d E) (k : ι → MaskJetIndex d) : Prop :=
  ∀ a i, (k i).order ≤ ((S.term a).jet i).order

end Falconer.MaskJetExpansion

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SeededInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse acting on already normalized individual jets

Only the additional derivative orders enter the extracted radius weight.
The formula also permits a complex angular multiplier as a separate label.
-/

namespace Falconer
open scoped ContDiff

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def seededRadiusWeight (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (a : ((seed k).inverse m j).index) : ℝ :=
  ∏ i, (r i)⁻¹^(((((seed k).inverse m j).term a).jet i).order-(k i).order)

end MaskJetExpansion
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MaskJetIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometry transport keeps the original individual mask jets -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace MaskJetIndex
variable {d : ℕ}

noncomputable def mapIsometry (j : MaskJetIndex d) (T : Space d ≃ₗᵢ[ℝ] Space d) : MaskJetIndex d where
  order := j.order
  vectors := fun i => T (j.vectors i)
  norm_vectors := fun i => by rw [T.norm_map]; exact j.norm_vectors i

end MaskJetIndex

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inverse step on factorized descriptor symbols

An endpoint is labelled by one angular multiplier and its original finite
set of descriptors. The seed retains every old jet order. A new inverse
adds at most `2*j` to each endpoint's descriptor budget.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

abbrev DescriptorInverseLabel (F : Finset PolicyDescriptor) := Unit ⊕ {b // b ∈ F}

noncomputable def descriptorInverseSeed {m KL KR L : ℕ} {F G : Finset PolicyDescriptor}
    {D : ℝ} (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) :
    DescriptorInverseLabel F ⊕ DescriptorInverseLabel G → MaskJetIndex (m+3) :=
  Sum.elim (Sum.elim (fun _ => MaskJetIndex.zero (m+3)) (fun b => f.jet b))
    (Sum.elim (fun _ => MaskJetIndex.zero (m+3)) (fun b => g.jet b))

namespace DescriptorJetSymbol
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

noncomputable def inverseLeftJets (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ F then
    (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
      (.inl (.inr ⟨b,hb⟩)) else MaskJetIndex.zero (m+3)

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual recursive symbols produced by the inverse

The old descriptor list and spatial multiplier survive unchanged. The
angular multiplier is the geometric inverse coefficient times the newly
differentiated old multiplier, with a fixed normalization. The new finite
smoothness budget is explicit.
-/

namespace Falconer
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

noncomputable def inverseRightJets (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ G then
    (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
      (.inr (.inr ⟨b,hb⟩)) else MaskJetIndex.zero (m+3)

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact values of the descriptor inverse factors

The additional label is the actual smooth angular multiplier. The other
labels are the original ambient descriptor masks, each occurring once.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {m K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def seedJet (f : DescriptorJetSymbol (m+1) K L F D) :
    DescriptorInverseLabel F → MaskJetIndex (m+3) :=
  Sum.elim (fun _ => MaskJetIndex.zero (m+3)) (fun b => f.jet b)

noncomputable def seedRadius (_f : DescriptorJetSymbol (m+1) K L F D)
    (N : ℕ) (σ : ℝ) : DescriptorInverseLabel F → ℝ :=
  Sum.elim (fun _ => D⁻¹) (fun b => descriptorMaskRadius N σ b)

noncomputable def seedMask (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))) :
    DescriptorInverseLabel F → Space (m+3) → Space (m+3) → ℂ :=
  Sum.elim (fun _ _ => f.angular)
    (fun b x z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ))

 theorem seedMask_smooth (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (a : DescriptorInverseLabel F) (x : Space (m+3)) :
    ContDiff ℝ ∞ (f.seedMask Q ρ profile N σ J i S a x) := by
  cases a with
  | inl a => exact f.angular_smooth
  | inr b =>
    exact Complex.ofRealCLM.contDiff.comp
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorSeededInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The seeded inverse identity for actual recursive amplitudes

Both endpoint symbols use their original ambient masks. Spatial factors
are pulled out exactly, and only newly added derivatives pay radius powers.
-/

namespace Falconer
open MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

noncomputable def descriptorInverseRadius
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (N : ℕ) (σ : ℝ) : DescriptorInverseLabel F ⊕ DescriptorInverseLabel G → ℝ :=
  Sum.elim (f.seedRadius N σ) (g.seedRadius N σ)

noncomputable def descriptorInverseWeight
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j N : ℕ) (σ : ℝ)
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index) : ℝ :=
  MaskJetExpansion.seededRadiusWeight m j (descriptorInverseSeed f g)
    (descriptorInverseRadius f g N σ) a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InverseClassExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact inverse expansion in the recursive symbol class

The finite family is constructed from the actual differentiated masks.
Its constants are uniform in both descriptor lists, and the output keeps
the two original spatial multipliers and the remaining smoothness budget.
-/

namespace Falconer
open MeasureTheory
open PlanarFalconer (PolicyDescriptor)

variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}

abbrev DescriptorInverseIndex
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j : ℕ) :=
  ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index

/-- The exact factors delivered by the finite inverse calculation. -/
structure DescriptorInverseSymbols
    (f : DescriptorJetSymbol (m+1) KL L F D)
    (g : DescriptorJetSymbol (m+1) KR L G D) (j R : ℕ) (A B : ℝ) where
  left : DescriptorInverseIndex f g j → DescriptorJetSymbol (m+1) (KL+2*j) R F D
  right : DescriptorInverseIndex f g j → DescriptorJetSymbol (m+1) (KR+2*j) R G D
  left_jet : ∀ a, (left a).jet = f.inverseLeftJets g j a
  right_jet : ∀ a, (right a).jet = f.inverseRightJets g j a
  left_spatial : ∀ a, (left a).spatial = f.spatial
  right_spatial : ∀ a, (right a).spatial = g.spatial
  left_angular : ∀ a, (left a).angular = normalizedAngular A
    (fun z => (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).coefficient z *
      (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
        (.inl (.inl ()))).scaledValue D⁻¹ f.angular z))
  right_angular : ∀ a, (right a).angular = normalizedAngular B
    (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
      (.inr (.inl ()))).scaledValue D⁻¹ g.angular)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseClassIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair integration of the exact inverse symbol family

The finite factors are the actual output symbols. The original endpoint
measures, both normalizing masses, and every descriptor remain explicit.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

noncomputable def coefficient (_T : DescriptorInverseSymbols f g j R A B)
    (N : ℕ) (σ Af Ag U V : ℝ) (a : DescriptorInverseIndex f g j) : ℝ :=
  descriptorInverseWeight f g j N σ a * (U*A) * (V*B) * Af⁻¹ * Ag⁻¹

end DescriptorInverseSymbols
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateSpatialShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial Fourier terms controlled by the exact recursive state

Spatial phases and conjugation preserve the actual descriptor symbol
class. Consequently each separated inverse factor is controlled by its
own next-state supremum, without enlarging the class of angular symbols.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def spatialFourier (f : DescriptorJetSymbol n K L F D)
    (s : ℝ) (ξ : Space (n+2)) : DescriptorJetSymbol n K L F D :=
  f.spatialMultiplier (spatialFourierPhase s ξ) (by fun_prop)
    (fun x => (spatialFourierPhase_norm s ξ x).le)

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateBudgetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding actual states in the fixed recursive derivative budget -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

noncomputable def relax {n K K' L L' : ℕ} {F : Finset PolicyDescriptor} {D D' : ℝ}
    (f : DescriptorJetSymbol n K L F D) (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D') : DescriptorJetSymbol n K' L' F D' where
  jet := f.jet
  order_le := f.order_le.trans hK
  angular := f.angular
  angular_smooth := f.angular_smooth
  angular_derivative := fun t ht w => (f.angular_derivative t (ht.trans hL) w).trans
    (pow_le_pow_left₀ hD hDD' t)
  angular_control := {
    measurable := f.angular_control.measurable
    bound := f.angular_control.bound
    smooth := f.angular_control.smooth
    derivative := by
      intro e t ht x y hy u hu
      exact (f.angular_control.derivative e t (ht.trans hL) x y hy u hu).trans
        (by simpa only [one_mul] using pow_le_pow_left₀ hD hDD' t) }
  spatial := f.spatial
  spatial_measurable := f.spatial_measurable
  spatial_bound := f.spatial_bound

end DescriptorJetSymbol

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_InverseJetShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common recursive budget for the complete finite inverse

Both descriptor lists and original endpoint laws stay fixed. The frequency
coefficient absorbs the added jet orders before the finite sum is bounded.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

abbrev DescriptorInverseFamilyIndex {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F D)
    (g : DescriptorJetSymbol (m+1) K L G D) (k : ℕ) :=
  (j : Fin (k+1)) × DescriptorInverseIndex f g j.val

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps and kernel planes for the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianRowMap (A : Fin h → Space d) : Space d →L[ℝ] Space h :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin h => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (A i)))

@[simp] theorem gaussianRowMap_apply (A : Fin h → Space d) (x : Space d) (i : Fin h) :
    gaussianRowMap A x i = inner ℝ x (A i) := by
  change inner ℝ (A i) x = inner ℝ x (A i)
  exact real_inner_comm _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FrameEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear isometry associated with a finite orthonormal frame -/

namespace Falconer
variable {d h : ℕ}

noncomputable def frameLinearMap (v : Fin h → Space d) : Space h →ₗ[ℝ] Space d :=
  (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.constr ℝ v

@[simp] theorem frameLinearMap_basis (v : Fin h → Space d) (i : Fin h) :
    frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i :=
  (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.constr_basis ℝ v i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphScaleData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript scales satisfy the analytic graph hypotheses

Depths a, p, v and L are normalized by the terminal depth. The actual
radial frequency is supplied by 2^frequency = R^v. All dimensional
constants and lower-scale requirements are explicit.
-/

namespace Falconer

noncomputable def graphDerivativeScale (R σ a p L c₀ C : ℝ) : ℝ :=
  C * (1 + R^σ * max 1 (R^(L-50*σ)) +
    (min c₀ (R^(a-p+10*σ)))⁻¹ + R^(-a)/R^(-p+30*σ))

theorem graph_scale_data (d : ℕ) {R σ a p v L c₀ C frequency : ℝ}
    (hR : 1 ≤ R) (hσ : 0 < σ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt d ≤ C)
    (hh : p-a ≤ v-p+2*σ) (hL : L ≤ v-p+2*σ) (hq : 10*σ ≤ v-p)
    (hfrequency : (2 : ℝ)^frequency = R^v)
    (hlarge : 40*Real.sqrt d ≤ R^(20*σ)) (hlargeπ : 4*Real.pi ≤ R^(20*σ)) :
    let δ := min c₀ (R^(a-p+10*σ))
    let τ := R^(-p+30*σ)
    let D := graphDerivativeScale R σ a p L c₀ C
    0 < δ ∧ δ ≤ 1/2 ∧ 0 < τ ∧ 1 ≤ D ∧ δ⁻¹ ≤ D ∧
      Real.sqrt d*R^(-a) ≤ (τ/4)*D ∧
      2*Real.sqrt d*R^(-p)+8*δ*(Real.sqrt d*R^(-a)) ≤ τ/4 ∧
      4*Real.pi*R^(20*σ) ≤ (2 : ℝ)^frequency*τ ∧
      16*D/((2 : ℝ)^frequency*τ) ≤ (16*C*(4+c₀⁻¹))*R^(-(26*σ)) := by
  let δ := min c₀ (R^(a-p+10*σ))
  let τ := R^(-p+30*σ)
  let S := 1 + R^σ * max 1 (R^(L-50*σ)) + δ⁻¹ + R^(-a)/τ
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hδ : 0 < δ := lt_min hc₀ (Real.rpow_pos_of_pos hR0 _)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hR0 _
  have hδsmall : δ ≤ 1/2 := (min_le_left _ _).trans hcsmall
  have hs₁ : 0 ≤ R^σ * max 1 (R^(L-50*σ)) := by positivity
  have hs₂ : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hs₃ : 0 ≤ R^(-a)/τ := by positivity
  have hSone : 1 ≤ S := by dsimp [S]; linarith
  have hSδ : δ⁻¹ ≤ S := by dsimp [S]; linarith
  have hSsp : R^(-a)/τ ≤ S := by dsimp [S]; linarith
  have hCS : S ≤ C*S := by nlinarith
  have hDone : 1 ≤ graphDerivativeScale R σ a p L c₀ C := hSone.trans hCS
  have hDδ : δ⁻¹ ≤ graphDerivativeScale R σ a p L c₀ C := hSδ.trans hCS
  have hsp : 4*Real.sqrt d*(R^(-a)/τ) ≤ graphDerivativeScale R σ a p L c₀ C := by
    calc
      _ ≤ C*(R^(-a)/τ) := mul_le_mul_of_nonneg_right hCdim (by positivity)
      _ ≤ C*S := mul_le_mul_of_nonneg_left hSsp (zero_le_one.trans hC)
  have hnorm : Real.sqrt d*R^(-a) ≤ (τ/4)*graphDerivativeScale R σ a p L c₀ C := by
    calc
      _ = (τ/4)*(4*Real.sqrt d*(R^(-a)/τ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsp (by positivity)
  have herr : 2*Real.sqrt d*R^(-p)+8*δ*(Real.sqrt d*R^(-a)) ≤ τ/4 := by
    have he := graph_cap_replacement_scale hR hσ.le (Real.sqrt_nonneg (d : ℝ)) hδ.le (min_le_right _ _)
    have hl := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ R^(-p+10*σ) by positivity)
    have hp : R^(20*σ)*R^(-p+10*σ) = τ := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    rw [hp] at hl
    nlinarith
  have hfreq : 4*Real.pi*R^(20*σ) ≤ (2 : ℝ)^frequency*τ := by
    rw [hfrequency]
    have hp : R^(20*σ)*R^(20*σ) = R^(40*σ) := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    calc
      _ ≤ R^(20*σ)*R^(20*σ) := mul_le_mul_of_nonneg_right hlargeπ (by positivity)
      _ = R^(40*σ) := hp
      _ ≤ _ := graph_radial_oscillation_size hR hq
  have hratio : 16*graphDerivativeScale R σ a p L c₀ C / ((2 : ℝ)^frequency*τ) ≤
      (16*C*(4+c₀⁻¹))*R^(-(26*σ)) := by
    rw [hfrequency]
    have hb := graph_nonstationary_ratio_bound hR hc₀ hσ.le hh hL hq
    calc
      _ = (16*C) * (S/(R^v*τ)) := by dsimp [graphDerivativeScale,S,δ,τ]; ring
      _ ≤ (16*C)*((4+c₀⁻¹)*R^(-(26*σ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [S,δ,τ,neg_mul] using hb) (by positivity)
      _ = _ := by ring
  exact ⟨hδ,hδsmall,hτ,hDone,hDδ,hnorm,herr,hfreq,hratio⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphPolicyScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Graph scales in the original integer-depth coordinates -/

namespace Falconer

noncomputable def policyGraphRadius (N a p : ℕ) (σ c₀ : ℝ) : ℝ :=
  min c₀ ((2:ℝ)^((a:ℝ)-p+10*σ*N))

noncomputable def policyGraphWidth (N p : ℕ) (σ : ℝ) : ℝ :=
  (2:ℝ)^(-(p:ℝ)+30*σ*N)

noncomputable def policyGraphScale (N a p L : ℕ) (σ c₀ C : ℝ) : ℝ :=
  graphDerivativeScale 2 (σ*N) a p L c₀ C

 theorem descriptor_graph_scale_identity (N L : ℕ) (σ : ℝ) :
    descriptorDerivativeScale N σ L =
      (2:ℝ)^(σ*N)*max 1 ((2:ℝ)^((L:ℝ)-50*σ*N)) := by
  unfold descriptorDerivativeScale
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N σ,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (-50*σ),
    ← Real.rpow_natCast (2:ℝ) L,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 2 <;> ring_nf

 theorem policy_graph_scale_data (d : ℕ) {N a p t L : ℕ} {σ c₀ C : ℝ}
    (hN : 0 < N) (hσ : 0 < σ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt d ≤ C)
    (hh : (p:ℝ)-a ≤ (t:ℝ)-p+2*σ*N)
    (hL : (L:ℝ) ≤ (t:ℝ)-p+2*σ*N)
    (hq : 10*σ*N ≤ (t:ℝ)-p)
    (hlarge : 40*Real.sqrt d ≤ ((2:ℝ)^N)^(20*σ))
    (hlargeπ : 4*Real.pi ≤ ((2:ℝ)^N)^(20*σ)) :
    0 < policyGraphRadius N a p σ c₀ ∧ policyGraphRadius N a p σ c₀ ≤ 1/2 ∧
    0 < policyGraphWidth N p σ ∧ 1 ≤ policyGraphScale N a p L σ c₀ C ∧
    (policyGraphRadius N a p σ c₀)⁻¹ ≤ policyGraphScale N a p L σ c₀ C ∧
    Real.sqrt d*(2:ℝ)^(-(a:ℝ)) ≤
      (policyGraphWidth N p σ/4)*policyGraphScale N a p L σ c₀ C ∧
    2*Real.sqrt d*(2:ℝ)^(-(p:ℝ))+
      8*policyGraphRadius N a p σ c₀*(Real.sqrt d*(2:ℝ)^(-(a:ℝ))) ≤
        policyGraphWidth N p σ/4 ∧
    4*Real.pi*((2:ℝ)^N)^(20*σ) ≤ (2:ℝ)^t*policyGraphWidth N p σ ∧
    16*policyGraphScale N a p L σ c₀ C/((2:ℝ)^t*policyGraphWidth N p σ) ≤
      (16*C*(4+c₀⁻¹))*((2:ℝ)^N)^(-26*σ) := by
  have hpow (r : ℝ) : ((2:ℝ)^N)^r = (2:ℝ)^(r*N) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N r]
    congr 1
    ring
  have he := graph_scale_data d (R := 2) (σ := σ*N) (a := a) (p := p) (v := t)
    (L := L) (frequency := t) (by norm_num)
    (mul_pos hσ (Nat.cast_pos.mpr hN)) hc₀ hcsmall hC hCdim
    (by nlinarith) (by nlinarith) (by nlinarith) rfl
    (by simpa only [hpow,mul_assoc] using hlarge)
    (by simpa only [hpow,mul_assoc] using hlargeπ)
  simpa only [policyGraphRadius,policyGraphWidth,policyGraphScale,hpow,mul_assoc,
    Real.rpow_natCast,neg_mul] using he

 theorem policy_graph_symbol_scale {N a p L : ℕ} {σ c₀ C E : ℝ}
    (hC : 1 ≤ C) (hc₀ : 0 < c₀) (hE : E ≤ descriptorDerivativeScale N σ L) :
    1+E ≤ policyGraphScale N a p L σ c₀ C := by
  have hE' : E ≤ (2:ℝ)^(σ*N)*max 1 ((2:ℝ)^((L:ℝ)-50*(σ*N))) := by
    simpa only [descriptor_graph_scale_identity,mul_assoc] using hE
  have hi : 0 ≤ (min c₀ ((2:ℝ)^((a:ℝ)-p+10*(σ*N))))⁻¹ :=
    inv_nonneg.mpr (le_min hc₀.le (by positivity))
  have hr : 0 ≤ (2:ℝ)^(-(a:ℝ))/(2:ℝ)^(-(p:ℝ)+30*(σ*N)) := by positivity
  let S := 1+(2:ℝ)^(σ*N)*max 1 ((2:ℝ)^((L:ℝ)-50*(σ*N)))+
    (min c₀ ((2:ℝ)^((a:ℝ)-p+10*(σ*N))))⁻¹+
    (2:ℝ)^(-(a:ℝ))/(2:ℝ)^(-(p:ℝ)+30*(σ*N))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hfirst : 1+E ≤ S := by dsimp [S]; linarith
  exact hfirst.trans (le_mul_of_one_le_left hS hC)

 theorem policyGraphWidth_eq (N p : ℕ) (σ : ℝ) :
    policyGraphWidth N p σ = (1/(2:ℝ)^p)*((2:ℝ)^N)^(30*σ) := by
  unfold policyGraphWidth
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (30*σ)]
  congr 2
  ring

 theorem policyGraphRadius_le (N a p : ℕ) (σ c₀ : ℝ) :
    policyGraphRadius N a p σ c₀ ≤ ((2:ℝ)^a/(2:ℝ)^p)*((2:ℝ)^N)^(10*σ) := by
  apply (min_le_right _ _).trans_eq
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_natCast,Real.rpow_natCast,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) N (10*σ)]
  congr 2
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_JetStateGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The profile graph estimate on the exact factorized state class

This packages the geometric hypotheses of the proved graph estimate. The
child envelope uses exactly the original list with anchors at most p
removed, and the same normalization and smooth multipliers.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped SchwartzMap

structure JetStateGraphData (n k : ℕ) (α B : ℝ) where
  Q : DyadicCube (n+2)
  unit : Q.side = 1
  ρ : Measure (Space (n+2))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  regular : Regularization.RegularizedProfileData Q ρ N s lam profile
  N_pos : 0 < N
  a : ℕ
  p : ℕ
  g : ℕ
  ap : a ≤ p
  pN : p ≤ N
  ag : a ≤ g
  gp : g ≤ p
  σ : ℝ
  σ_nonneg : 0 ≤ σ
  gap : (g:ℝ)-a ≤ 2*σ*N
  X : List (Fin (n+2) → Bool)
  Y : List (Fin (n+2) → Bool)
  X_length : X.length = a
  Y_length : Y.length = a
  v : ℝ
  τ : ℝ
  δ : ℝ
  capBound : ℝ
  Dq : ℝ
  Dmask : ℝ
  Dsymbol : ℝ
  Dgraph : ℝ
  τ_pos : 0 < τ
  δ_pos : 0 < δ
  δ_small : δ ≤ 1/2
  capBound_nonneg : 0 ≤ capBound
  Dq_nonneg : 0 ≤ Dq
  Dmask_one : 1 ≤ Dmask
  Dsymbol_one : 1 ≤ Dsymbol
  Dgraph_one : 1 ≤ Dgraph
  symbol_scale : Dq+Dsymbol ≤ Dgraph
  cap_scale : δ⁻¹ ≤ Dgraph
  endpoint_scale : Real.sqrt (n+2 : ℕ)*(Q.descendant X).side ≤ (τ/4)*Dgraph
  phase_error : 2*Real.sqrt (n+2 : ℕ)*((Q.descendant X).side/(2:ℝ)^(p-a))+
    8*δ*(Real.sqrt (n+2 : ℕ)*(Q.descendant X).side) ≤ τ/4
  frequency : 4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ
  test_scale : 4*τ*((2:ℝ)^(p-a)/(Q.descendant X).side) ≤
    (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ)
  F : Finset PolicyDescriptor
  masks : PolicyDescriptor → Finset (Sphere (n+2))
  J : ℕ
  i : ℕ
  separated : ∀ b ∈ F, ∀ w ∈ masks b, ∀ z ∈ masks b, w ≠ z →
    descriptorMaskRadius N σ b/2 ≤ dist w z
  mask_scale : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask
  list_scale : (F.card:ℝ)*B*Dmask ≤ Dsymbol
  parallel : PolicyDescriptor.parallel g p ∈ F
  left_width : 2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q.descendant X).side/(2:ℝ)^(g-a))) ≤
    angularTestWidth N σ J (i+1) p
  right_width : 2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q.descendant Y).side/(2:ℝ)^(g-a))) ≤
    angularTestWidth N σ J (i+1) p
  caps : Finset (Sphere (n+2))
  partition : Sphere (n+2) → Sphere (n+2) → ℝ
  cap_control : ∀ w ∈ caps, ChartCapControl k (partition w) (w : Space (n+2)) δ capBound
  cap_nonneg : ∀ w ∈ caps, ∀ z, 0 ≤ partition w z
  partition_one : ∀ z, ∑ w ∈ caps, partition w z = 1

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

noncomputable def coefficient (G : JetStateGraphData n k α B) : ℝ :=
  2*11^(n+2)*((2:ℝ)^G.N)^(
    -(profileExcess (d := n+2) G.profile G.N G.p-profileExcess (d := n+2) G.profile G.N G.a)-
    (profileExcess (d := n+2) G.profile G.N G.p-profileExcess (d := n+2) G.profile G.N G.a)+
    PlanarFalconer.height (profileExcess (d := n+2) G.profile G.N) G.a G.p+
    (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*G.σ+4*(((n+2:ℕ):ℝ)+1)*G.lam)

noncomputable def error (G : JetStateGraphData n k α B) (H C W T : ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(G.v-G.a)) *
    ((profileModelMass G.profile G.N G.p/profileModelMass G.profile G.N G.a)*
      (profileModelMass G.profile G.N G.p/profileModelMass G.profile G.N G.a))^2 *
    capGraphError (n+2) k H C W ((2:ℝ)^G.N) T
      (profileModelMass G.profile G.N G.p) (profileModelMass G.profile G.N G.p)
      G.capBound 1 G.Dgraph G.v G.τ G.caps.card
      ((G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
        (G.Q.descendant G.Y).occupiedPaths G.ρ (G.p-G.a)).card

noncomputable abbrev symbol (G : JetStateGraphData n k α B) {K : ℕ}
    (f : DescriptorJetSymbol n K k G.F G.Dq) (A : ℝ) :=
  f.value G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A

noncomputable def childMaximum (G : JetStateGraphData n k α B) (K : ℕ) (A : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  childJetStateMaximum n K k G.Dq (G.F.filter (fun b => G.p < descriptorAnchor b))
    G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A
    G.X G.Y (G.p-G.a) (profileModelMass G.profile G.N G.p) G.p G.v Ψ

end JetStateGraphData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PrefixPolicyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem prefix_policy_geometry (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) :
    let p := policyDepth A N q a t
    a < p ∧ p ≤ t ∧ q ≤ p-a ∧ 2*(p-a) ≤ t-a ∧
      PolicyDescriptor.parallel a p ∈ policyDescriptorList A N q a t := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  dsimp only
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · change PolicyDescriptor.parallel a (policyDepth A N q a t) ∈ originDescriptors A N q a t
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_Ico.mpr ⟨?_,by omega⟩,rfl⟩
    have he : min (policyDepth A N q a t-a) (t-policyDepth A N q a t) =
        policyDepth A N q a t-a := min_eq_left (by omega)
    rw [he]
    omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyPrefixScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual high-prefix shell supplies the graph scales -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor policyDepth)

theorem policy_prefix_graph_scales {m : ℕ} (P : PolicyJetData m)
    (hσ : 0 < P.σ) (hleft : P.a₀ = P.a)
    (hwide : P.a+100*P.q < P.t₀) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N)
    (hprefix : 2*policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀) :
    let p := policyDepth P.policy P.N P.q P.a P.t₀
    P.a < p ∧ p < P.t ∧ p ≤ P.N ∧ PolicyDescriptor.parallel P.a p ∈ P.list ∧
      (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N ∧
      (P.longest:ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N ∧
      10*P.σ*P.N ≤ (P.t:ℝ)-p := by
  let p := policyDepth P.policy P.N P.q P.a P.t₀
  have hg := PlanarFalconer.prefix_policy_geometry P.policy P.q_pos P.base_N hwide hprefix
  have hap : P.a < p := hg.1
  have hpN : p ≤ P.N := hg.2.1.trans P.base_N
  have hpref : 2*(p:ℝ) ≤ (P.a:ℝ)+P.t₀ := by exact_mod_cast hprefix
  have hwideR : (P.a:ℝ)+100*P.q < P.t₀ := by exact_mod_cast hwide
  have hσN : 0 < P.σ*(P.N:ℝ) := mul_pos hσ (Nat.cast_pos.mpr P.N_pos)
  have hfreq : 10*P.σ*P.N < (P.t:ℝ)-p := by nlinarith
  have hpt : p < P.t := by
    have hh : (p:ℝ) < P.t := by nlinarith
    exact_mod_cast hh
  have hlong : P.longest ≤ (P.t₀-P.a)/2 := by
    apply Finset.sup_le
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).1
    rw [hleft] at hb'
    exact PlanarFalconer.policyDescriptor_length_le_half P.policy P.q_pos hb'
  have hlongR : 2*(P.longest:ℝ) ≤ (P.t₀:ℝ)-P.a := by
    have hh : P.a+2*P.longest ≤ P.t₀ := by omega
    have hhR : (P.a:ℝ)+2*P.longest ≤ P.t₀ := by exact_mod_cast hh
    linarith
  refine ⟨hap,hpt,hpN,?_,by nlinarith,by nlinarith,hfreq.le⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_,hap⟩
  simpa only [hleft] using hg.2.2.2.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two policy witnesses used by the same graph estimate -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

namespace PolicyJetData
variable {m : ℕ}

structure GraphGeometry (P : PolicyJetData m) where
  p : ℕ
  g : ℕ
  ap : P.a ≤ p
  pN : p ≤ P.N
  ag : P.a ≤ g
  gp : g ≤ p
  gap : (g:ℝ)-P.a ≤ P.σ*P.N
  depth : (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N
  length : (P.longest:ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N
  frequency : 10*P.σ*P.N ≤ (P.t:ℝ)-p
  parallel : PolicyDescriptor.parallel g p ∈ P.list

def directGeometry (P : PolicyJetData m) (d : PolicyDescriptor)
    (hd : PlanarFalconer.DirectPolicyWitness P.policy P.N P.q P.a₀ P.t₀ P.a P.t P.σ d) :
    P.GraphGeometry where
  p := descriptorAnchor d
  g := max P.a (descriptorAnchor d-descriptorLength d)
  ap := hd.anchor_gt.le
  pN := hd.anchor_lt.le.trans (P.base_right.trans P.base_N)
  ag := le_max_left _ _
  gp := hd.g_lt.le
  gap := hd.g_slack
  depth := by simpa only [Nat.cast_sub hd.anchor_gt.le] using hd.depth_scale
  length := by simpa only [longest,list,hd.maximal] using hd.length_scale
  frequency := hd.frequency_slack
  parallel := hd.companion

noncomputable def prefixGeometry (P : PolicyJetData m) (hσ : 0 < P.σ) (hleft : P.a₀ = P.a)
    (hwide : P.a+100*P.q < P.t₀) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N)
    (hprefix : 2*PlanarFalconer.policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀) :
    P.GraphGeometry := by
  have hs := policy_prefix_graph_scales P hσ hleft hwide hq hhigh hprefix
  exact {
    p := PlanarFalconer.policyDepth P.policy P.N P.q P.a P.t₀
    g := P.a
    ap := hs.1.le
    pN := hs.2.2.1
    ag := le_rfl
    gp := hs.1.le
    gap := by simpa only [sub_self] using mul_nonneg hσ.le (Nat.cast_nonneg P.N)
    depth := hs.2.2.2.2.1
    length := hs.2.2.2.2.2.1
    frequency := hs.2.2.2.2.2.2
    parallel := hs.2.2.2.1 }

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common graph data for the direct and high-prefix witnesses -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def graphDataAt (P : PolicyJetData m) (k : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hσ : 0 < P.σ) (hJ : 0 < P.J) (hi : P.i+1 ≤ P.J)
    (hNlist : Classical.choose (eventual_descriptor_list_scale 3 hB hσ) ≤ P.N)
    (hNwidth : Classical.choose (uniform_graph_parallel_width (m+3) hσ hJ) ≤ P.N)
    (geometry : P.GraphGeometry)
    (c₀ C H : ℝ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt (m+3:ℕ) ≤ C) (hH : 0 ≤ H)
    (hlarge : 40*Real.sqrt (m+3:ℕ) ≤ ((2:ℝ)^P.N)^(20*P.σ))
    (hlargeπ : 4*Real.pi ≤ ((2:ℝ)^P.N)^(20*P.σ))
    (S : Finset (Sphere (m+3))) (η : Sphere (m+3) → Sphere (m+3) → ℝ)
    (hcontrol : ∀ w ∈ S, ChartCapControl k (η w) (w : Space (m+3))
      (policyGraphRadius P.N P.a geometry.p P.σ c₀) H)
    (hnonneg : ∀ w ∈ S, ∀ z, 0 ≤ η w z) (hone : ∀ z, ∑ w ∈ S, η w z = 1) :
    JetStateGraphData (m+1) k (20*P.σ) B := by
  let p := geometry.p
  let g := geometry.g
  let δ := policyGraphRadius P.N P.a p P.σ c₀
  let τ := policyGraphWidth P.N p P.σ
  let E := descriptorListScale B P.N P.σ P.longest P.list
  let Dsymbol := max 1 E
  let Dgraph := policyGraphScale P.N P.a p P.longest P.σ c₀ C
  have hap : P.a ≤ p := geometry.ap
  have hpN : p ≤ P.N := geometry.pN
  have hag : P.a ≤ g := geometry.ag
  have hgp : g ≤ p := geometry.gp
  have hdepth : (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N := geometry.depth
  have hlength : (P.longest:ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N := geometry.length
  have hscale :=
    policy_graph_scale_data (m+3) P.N_pos hσ hc₀ hcsmall hC hCdim
      hdepth hlength geometry.frequency hlarge hlargeπ
  have hδ := hscale.1
  have hδsmall := hscale.2.1
  have hτ := hscale.2.2.1
  have hDgraph := hscale.2.2.2.1
  have hcap := hscale.2.2.2.2.1
  have hendpoint := hscale.2.2.2.2.2.1
  have hphase := hscale.2.2.2.2.2.2.1
  have hfreq := hscale.2.2.2.2.2.2.2.1
  have hlist := (Classical.choose_spec (eventual_descriptor_list_scale 3 hB hσ))
    P.N hNlist P.longest P.list P.list_card
  have hE : E ≤ descriptorDerivativeScale P.N P.σ P.longest := by
    have hh := hlist.2
    have he : 0 ≤ E := by dsimp [E,descriptorListScale]; positivity
    linarith
  have hsymbol : Dsymbol ≤ descriptorDerivativeScale P.N P.σ P.longest :=
    max_le (by linarith [hlist.1]) hE
  have hsymbolGraph : 1+Dsymbol ≤ Dgraph := policy_graph_symbol_scale hC hc₀ hsymbol
  have hside (Z : List (Fin (m+3) → Bool)) (hZ : Z.length = P.a) :
      (P.Q.descendant Z).side = (2:ℝ)^(-(P.a:ℝ)) := by
    rw [P.Q.descendant_side,P.unit,hZ,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div]
  have hsmallside (Z : List (Fin (m+3) → Bool)) (hZ : Z.length = P.a) :
      (P.Q.descendant Z).side/(2:ℝ)^(g-P.a) = 1/(2:ℝ)^g := by
    rw [descendant_common_band_scale P.Q P.unit Z hZ hag,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have hwidth : 2*τ+2*δ*(Real.sqrt (m+3:ℕ)*(1/(2:ℝ)^g)) ≤
      angularTestWidth P.N P.σ P.J (P.i+1) p := by
    have hh := (Classical.choose_spec (uniform_graph_parallel_width (m+3) hσ hJ))
      P.N hNwidth P.a g p (P.i+1) hag hi δ hδ.le
      (policyGraphRadius_le P.N P.a p P.σ c₀)
    simpa only [τ,policyGraphWidth_eq] using hh
  refine {
    Q := P.Q, unit := P.unit, ρ := P.ρ, profile := P.profile, N := P.N,
    s := P.s, lam := P.lam, regular := P.regular, N_pos := P.N_pos,
    a := P.a, p := p, g := g, ap := hap, pN := hpN, ag := hag, gp := hgp,
    σ := P.σ, σ_nonneg := hσ.le, gap := ?_, X := P.X, Y := P.Y,
    X_length := P.X_length, Y_length := P.Y_length, v := P.t,
    τ := τ, δ := δ, capBound := H, Dq := 1,
    Dmask := 8*max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ)),
    Dsymbol := Dsymbol, Dgraph := Dgraph,
    τ_pos := hτ, δ_pos := hδ, δ_small := hδsmall, capBound_nonneg := hH,
    Dq_nonneg := by norm_num, Dmask_one := ?_, Dsymbol_one := le_max_left _ _,
    Dgraph_one := hDgraph, symbol_scale := hsymbolGraph, cap_scale := hcap,
    endpoint_scale := ?_, phase_error := ?_,
    frequency := by simpa only [τ,Real.rpow_natCast] using hfreq, test_scale := ?_,
    F := P.list, masks := P.masks, J := P.J, i := P.i, separated := P.separated,
    mask_scale := ?_, list_scale := le_max_right _ _, parallel := geometry.parallel,
    left_width := ?_, right_width := ?_, caps := S, partition := η,
    cap_control := hcontrol, cap_nonneg := hnonneg, partition_one := hone }
  · have hh := geometry.gap
    dsimp only [g,p]
    linarith [mul_nonneg hσ.le (Nat.cast_nonneg P.N)]
  · have hh : 1 ≤ max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ)) := le_max_left _ _
    linarith
  · simpa only [hside P.X P.X_length] using hendpoint
  · rw [descendant_common_band_scale P.Q P.unit P.X P.X_length hap,
      hside P.X P.X_length]
    simpa only [δ,τ] using hphase
  · have htau : 4*τ*((2:ℝ)^(p-P.a)/(P.Q.descendant P.X).side) =
        4*((2:ℝ)^P.N)^(30*P.σ) := by
      dsimp only [τ]
      rw [P.Q.descendant_side,P.unit,P.X_length,policyGraphWidth_eq]
      have hp : (2:ℝ)^P.a*(2:ℝ)^(p-P.a) = (2:ℝ)^p := by
        rw [← pow_add,Nat.add_sub_of_le hap]
      rw [← hp]
      field_simp
    rw [htau]
    exact Nat.le_ceil _
  · intro b hb
    exact descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)
  · simpa only [hsmallside P.X P.X_length] using hwidth
  · simpa only [hsmallside P.Y P.Y_length] using hwidth

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct policy graph reduction with a uniform remainder -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def graphCoefficient (P : PolicyJetData m) (p : ℕ) : ℝ :=
  2*11^(m+3)*((2:ℝ)^P.N)^(
    -(profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)-
    (profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)+
    PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
    (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*P.σ+4*(((m+3:ℕ):ℝ)+1)*P.lam)

noncomputable def graphChild (P : PolicyJetData m) (K L p : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  childJetStateMaximum (m+1) K L 1
    (P.list.filter (fun b => p < descriptorAnchor b))
    P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z
    P.X P.Y (p-P.a) (profileModelMass P.profile P.N p) p P.t Ψ

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyFarStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual policy far reduction with an arbitrary-power error -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace PolicyJetData
variable {m : ℕ}

noncomputable def nearBound (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
      profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
      childJetStateMaximum (m+1) K L 1
        (P.list.filter (fun b => P.splitDepth < PlanarFalconer.descriptorAnchor b))
        P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z
        P.X P.Y (P.splitDepth-P.a) (profileModelMass P.profile P.N P.splitDepth) P.splitDepth P.t Ψ)

noncomputable def collisionTerm (P : PolicyJetData m) (w₀ : Sphere (m+3))
    (C : ℝ) (b : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
      profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam))*
    (PlanarFalconer.binKernelConstant*farCollisionMaximum w₀ P.Q P.ρ
      (fun t => P.profile (t/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a))

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PolicyJetChildren
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual policy states at the child cells of an angular step -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

def child (P : PolicyJetData m) (p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) : PolicyJetData m where
  Q := P.Q
  unit := P.unit
  ρ := P.ρ
  profile := P.profile
  N := P.N
  s := P.s
  lam := P.lam
  regular := P.regular
  N_pos := P.N_pos
  σ := P.σ
  J := P.J
  i := P.i
  q := P.q
  q_pos := P.q_pos
  policy := P.policy
  a₀ := P.a₀
  t₀ := P.t₀
  a := p
  t := P.t
  base_left := P.base_left.trans hap
  base_right := P.base_right
  base_N := P.base_N
  X := P.X++row.1
  Y := P.Y++row.2
  X_length := by
    rw [List.length_append,P.X_length]
    have hh := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hrow).1).1
    omega
  Y_length := by
    rw [List.length_append,P.Y_length]
    have hh := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hrow).2).1
    omega
  masks := P.masks
  separated := fun b hb => P.separated b
    (PlanarFalconer.remainingPolicyDescriptors_mono P.policy P.N P.q P.a₀ P.t₀ hap hb)
  Z := P.Z
  Z_pos := P.Z_pos

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyBranchCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension-dependent coefficient payments in the scalar branch ledger -/

namespace Falconer
open Set MeasureTheory

def dimensionalBranchReserve (d : ℕ) (lam σ : ℝ) : ℝ := ((d:ℝ)+1)*(lam+σ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct angular branch on actual successor states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def directWeight (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ) : ℝ :=
  ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N p-
    profileExcess (d := m+3) P.profile P.N P.a)+
    PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
    4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε)

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyCommonBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One derivative budget for positive and angular policy steps -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (policyDepth)

def PolicyGraphBound (m K L J : ℕ) (lam σ ε T Z : ℝ) (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ → P.J = J → P.Z = Z → N₀ ≤ P.N →
    P.i+1 ≤ P.J → ∀ geometry : P.GraphGeometry, ∀ M : ℝ, 0 ≤ M →
    (∀ row, ∀ hrow : row ∈
      (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
      P.directWeight geometry.p lam σ ε *
        (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M) →
    P.envelope K L Ψ ≤ M+((2:ℝ)^P.N)^(-T)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyFarCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact collision coefficients and their branch payments -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace PolicyJetData
variable {m : ℕ}

noncomputable def farWeight (P : PolicyJetData m) (b : ℕ) (lam σ ε : ℝ) : ℝ :=
  ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
    profileExcess (d := m+3) P.profile P.N P.a)+
    4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε)

noncomputable def collisionCoefficient (P : PolicyJetData m) (K : ℕ) (B C : ℝ) (b : ℕ) : ℝ :=
  C*(B^K*P.Z⁻¹)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    PlanarFalconer.binKernelConstant.toReal*
    ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
      profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PolicyAngularBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The proved angular steps use the scheduled scalar branches -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent branchCost descriptorAnchor)

namespace PolicyJetData
variable {m : ℕ}

def branchState (P : PolicyJetData m) : BranchState := .H P.a₀ P.t₀ P.a P.t P.i

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicySuffixRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual positive suffix reduction with the scalar branch weight -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (policyDepth)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def suffixWeight (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ) : ℝ :=
  ((2:ℝ)^P.N)^(Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N
    (((m+3:ℕ):ℝ)/2) p P.t+4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε)

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PolicyPositiveBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete positive successors in the weighted branch tree -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent branchCost policyDepth)

namespace PolicyJetData
variable {m : ℕ}

def positiveBranchState (P : PolicyJetData m) : BranchState := .D P.a P.t P.i

/-- Change only the current pair of cells; the retained descriptor set shrinks. -/
def onCells (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (X Y : List (Fin (m+3) → Bool)) (hX : X.length = a) (hY : Y.length = a) : PolicyJetData m :=
  { P with
    a := a, X := X, Y := Y, X_length := hX, Y_length := hY,
    base_left := P.base_left.trans ha,
    separated := fun b hb => P.separated b
      (PlanarFalconer.remainingPolicyDescriptors_mono P.policy P.N P.q P.a₀ P.t₀ ha hb) }

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyFarSuccessors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual positive states of a comparable far collision

The two new endpoint cells lie in the same original endpoint cell. Both
retain the descriptor masks and reset only the positive interval and index.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

theorem partner_lengths (P : PolicyJetData m) (a : ℕ)
    (U : List (Fin (m+3) → Bool)) (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    row.1.length = a-P.a ∧ row.2.length = a-P.a := by
  have hp := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
  exact ⟨(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp.1).1,
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp.2).1⟩

def farPositiveSuccessor (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) : PolicyJetData m :=
  (P.onCells a ha (U++row.1) (U++row.2)
    (by rw [List.length_append,hU,(partner_lengths P a U row hr).1]; omega)
    (by rw [List.length_append,hU,(partner_lengths P a U row hr).2]; omega)).positiveSuccessor
      P.t P.base_right (P.i+1)

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual energies represented by scalar branch states

The context fixes the original measure, masks and profile. The constructors
carry the actual positive count or angular envelope, and the positive case
records the cell separation supplied by the far partition.
-/

namespace Falconer
open Set MeasureTheory

structure PolicyContext (m : ℕ) where
  Q : DyadicCube (m+3)
  ρ : Measure (Space (m+3))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  σ : ℝ
  J : ℕ
  q : ℕ
  policy : ℕ → ℝ
  masks : PlanarFalconer.PolicyDescriptor → Finset (Sphere (m+3))
  Z : ℝ

def PolicyJetData.context {m : ℕ} (P : PolicyJetData m) : PolicyContext m :=
  ⟨P.Q,P.ρ,P.profile,P.N,P.s,P.lam,P.σ,P.J,P.q,P.policy,P.masks,P.Z⟩

inductive PolicyEnergy {m : ℕ} (K L : ℕ) (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3)) :
    PolicyContext m → PlanarFalconer.BranchState → ℝ → Prop
  | positive (P : PolicyJetData m) (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t)
      (lower : 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖)
      (upper : ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side) :
      PolicyEnergy K L Ψ w₀ P.context P.positiveBranchState (P.positiveCount w₀)
  | angular (P : PolicyJetData m) :
      PolicyEnergy K L Ψ w₀ P.context P.branchState (P.envelope K L Ψ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyRecursionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common budget for all actual policy recurrences -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (policyDepth)

def PolicyPositiveBound (m K L J : ℕ) (lam σ ε T Z : ℝ) (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J → P.a₀ = P.a → P.t₀ = P.t → P.a+100*P.q < P.t →
      P.σ*(P.N:ℝ) ≤ P.q →
      2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) ≤ M →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        ((2:ℝ)^P.N)^ε*(positiveCollisionCount w₀ P.Q P.ρ
          (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M) →
      (∀ v, ∀ hv : v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        ∀ p, p = policyDepth P.policy P.N P.q P.a P.t → ∀ hap : P.a ≤ p,
        ∀ row, ∀ hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
        P.directWeight p lam σ ε *
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child p hap row hrow).envelope K L Ψ ≤ M) →
      P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T)

def PolicyFarBound (m K L : ℕ) (lam σ ε T : ℝ) (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ (P : PolicyJetData m), P.lam = lam → P.σ = σ →
      N₀ ≤ P.N → ∀ hsplit : P.a < P.splitDepth, 1 ≤ P.Z →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (P.splitDepth-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (P.splitDepth-P.a),
        P.farWeight P.splitDepth lam σ ε *
          (P.child P.splitDepth hsplit.le row hrow).envelope K L Ψ ≤ M) →
      (∀ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
        ENNReal.ofReal (P.farWeight b lam σ ε)*
          farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
            P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) ≤ ENNReal.ofReal M) →
      P.envelope K L Ψ ≤ 2*M+((2:ℝ)^P.N)^(-T)

def PolicySuffixBound (m J : ℕ) (lam σ ε : ℝ) (N₀ : ℕ) : Prop :=
  ∀ P : PolicyJetData m,
      P.lam = lam → P.σ = σ → P.J = J → N₀ ≤ P.N → P.i ≤ P.J →
      P.a+100*P.q < P.t → P.a+P.t < 2*policyDepth P.policy P.N P.q P.a P.t →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ∀ (w₀ : Sphere (m+3)),
      P.positiveCount w₀ ≤ P.suffixWeight (policyDepth P.policy P.N P.q P.a P.t) lam σ ε *
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a (policyDepth P.policy P.N P.q P.a P.t) P.X P.Y).toReal

structure PolicyRecursionBounds (m K L J : ℕ) (lam σ ε T Z : ℝ)
    (N₀ : ℕ) (Ψ : ℝ → ℝ) : Prop where
  graph : PolicyGraphBound m K L J lam σ ε T Z N₀ Ψ
  positive : PolicyPositiveBound m K L J lam σ ε T Z N₀ Ψ
  far : PolicyFarBound m K L lam σ ε T N₀ Ψ
  suffix : PolicySuffixBound m J lam σ ε N₀

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyEnergySteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the analytic recurrences to actual branch energies -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent policyDepth)

namespace PolicyJetData
variable {m : ℕ}

def ChildrenBound (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ)
    (w₀ : Sphere (m+3)) (s : BranchState) (ε M : ℝ) : Prop :=
  ∀ u l, BranchStep P.policy P.N P.q P.σ s l u →
    ∀ x, PolicyEnergy K L Ψ w₀ P.context u x →
      ((2:ℝ)^P.N)^(branchExponent P.policy
        (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε s l u)*x ≤ M

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_DimensionalBranchBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Branch weights for the ambient-dimensional profile

The excess profile is d-Lipschitz. These estimates retain that factor in
both the terminal potential payment and the accumulated error exponent.
-/

namespace Falconer
open PlanarFalconer

def DimensionalProfileLipschitz (d : ℕ) (A : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∀ j ≤ N, |A i-A j| ≤ (d:ℝ)*|(i:ℝ)-j|/(N:ℝ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyRootApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted estimate on actual positive and angular root states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def PolicyJetData.rootBound {m : ℕ} (P : PolicyJetData m) (σ κ η : ℝ) : ℝ :=
  4^(sourceSmoothingLevels σ κ+1)*
    (((2:ℝ)^P.N)^(2*P.policy P.a-
      PlanarFalconer.potential P.policy P.a P.t (10*sourcePolicyBlock P.N κ)+
      500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η)+
      ((2:ℝ)^P.N)^(-10:ℝ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FlexibleAngularRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the recursive root estimate at the outer graph budgets -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

namespace PolicyJetData
variable {m : ℕ}

def withNormalization (P : PolicyJetData m) (Z : ℝ) (hZ : 0 < Z) : PolicyJetData m :=
  { P with Z := Z, Z_pos := hZ }

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original direction labels in affine gnomonic coordinates -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

noncomputable def gnomonicCoordinates (w : Sphere (n+1)) : Space n :=
  WithLp.toLp 2 (fun i => (w:Space (n+1)) i.succ / (w:Space (n+1)) 0)

@[simp] theorem gnomonicCoordinates_apply (w : Sphere (n+1)) (i : Fin n) :
    gnomonicCoordinates w i = (w:Space (n+1)) i.succ / (w:Space (n+1)) 0 := rfl

end Falconer

/-! # Explicit inverse and cone coordinates for the gnomonic measure formula -/
namespace Falconer
open Set MeasureTheory
open scoped Pointwise

noncomputable def gnomonicRatio {n : ℕ} (z : Space (n+1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.succ/z 0)

@[simp] theorem gnomonicRatio_apply {n : ℕ} (z : Space (n+1)) (i : Fin n) :
    gnomonicRatio z i = z i.succ/z 0 := rfl

noncomputable def gnomonicConePoint {n : ℕ} (r : ℝ) (x : Space n) : Space (n+1) :=
  r • northLift x

@[simp] theorem gnomonicConePoint_zero {n : ℕ} (r : ℝ) (x : Space n) :
    gnomonicConePoint r x 0 = r := by simp [gnomonicConePoint]

@[simp] theorem gnomonicConePoint_succ {n : ℕ} (r : ℝ) (x : Space n) (i : Fin n) :
    gnomonicConePoint r x i.succ = r*x i := by simp [gnomonicConePoint]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small spherical cap has bounded original affine coordinates -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

@[simp] theorem northLift_zero_vector : northLift (0 : Space n) =
    WithLp.toLp 2 (Fin.cons 1 (fun _ => 0)) := rfl

@[simp] theorem northLift_zero_norm : ‖northLift (0 : Space n)‖ = 1 := by
  have hh := northLift_norm_sq (0 : Space n)
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero] at hh
  nlinarith [norm_nonneg (northLift (0 : Space n))]

@[simp] theorem gnomonicChart_zero_coe :
    (gnomonicChart (0 : Space n) : Space (n+1)) = northLift 0 := by
  change ‖northLift (0 : Space n)‖⁻¹ • northLift 0 = _
  rw [northLift_zero_norm,inv_one,one_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Availability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Available radial exponents in the original product measure

These definitions record `prep:availability`. A bad set is a measurable
set of original pairs, and each remaining radial fiber is measured using
the original opposite marginal. No fiber is renormalized.
The closure and bootstrap express parts of `prep:thin-upgrade`.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- Radial direction, assigned zero on the diagonal. The application uses
separated supports, so this arbitrary diagonal value has no effect. -/
noncomputable def radialDirection {d : ℕ} (x y : Space d) : Space d :=
  ‖y - x‖⁻¹ • (y - x)

/-- Both directional cap estimates, using the original opposite probability. -/
def RadialCapBound {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    (G : Set (Space d × Space d)) (N : ℕ) (e q : ℝ) : Prop :=
  (∀ x ∈ (μ : Measure (Space d)).support, ∀ w : Space d, ‖w‖ = 1 →
    ∀ u : ℝ, ((2 : ℝ) ^ N)⁻¹ ≤ u → u ≤ 1 →
    (ν : Measure (Space d)) {y | (x, y) ∈ G ∧ dist (radialDirection x y) w < u} ≤
      ENNReal.ofReal (((2 : ℝ) ^ N) ^ e * u ^ q)) ∧
  (∀ y ∈ (ν : Measure (Space d)).support, ∀ w : Space d, ‖w‖ = 1 →
    ∀ u : ℝ, ((2 : ℝ) ^ N)⁻¹ ≤ u → u ≤ 1 →
    (μ : Measure (Space d)) {x | (x, y) ∈ G ∧ dist (radialDirection y x) w < u} ≤
      ENNReal.ofReal (((2 : ℝ) ^ N) ^ e * u ^ q))

/-- A radial cap exponent available after a power-small deletion of original
pairs. Constants and the starting scale may depend on the desired loss. -/
def CapAvailable {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) (q : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ K : ℕ,
    ∀ N ≥ K, ∃ B : Set (Space d × Space d),
      MeasurableSet B ∧ B ⊆ Γ N ∧
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ N) ^ (-c)) ∧
      RadialCapBound μ ν (Γ N \ B) N e q

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual coordinate isomorphisms for a transverse tuple in arbitrary dimension -/

namespace Falconer
open scoped BigOperators Matrix
variable {d : ℕ}

noncomputable def euclideanColumnMatrix (v : Fin d → Space d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun i j => (v j) i)

noncomputable def euclideanColumnLinear (v : Fin d → Space d) : Space d →ₗ[ℝ] Space d where
  toFun x := ∑ i : Fin d, x i • v i
  map_add' x y := by simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

theorem euclideanColumnLinear_apply (v : Fin d → Space d) (x : Space d) (i : Fin d) :
    euclideanColumnLinear v x i = (euclideanColumnMatrix v *ᵥ WithLp.ofLp x) i := by
  simp only [euclideanColumnLinear,LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    smul_eq_mul,Matrix.mulVec,dotProduct,euclideanColumnMatrix,Matrix.of_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

noncomputable def euclideanDualCoordinates (v : Fin d → Space d) (x : Space d) : Space d :=
  WithLp.toLp 2 ((euclideanColumnMatrix v)⁻¹ *ᵥ WithLp.ofLp x)

theorem euclideanDualCoordinates_column (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (x : Space d) :
    euclideanDualCoordinates v (euclideanColumnLinear v x) = x := by
  have he : WithLp.ofLp (euclideanColumnLinear v x) = euclideanColumnMatrix v *ᵥ WithLp.ofLp x :=
    funext (euclideanColumnLinear_apply v x)
  apply PiLp.ext
  intro i
  change ((euclideanColumnMatrix v)⁻¹ *ᵥ WithLp.ofLp (euclideanColumnLinear v x)) i = x i
  rw [he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hv),Matrix.one_mulVec]

noncomputable def euclideanColumnEquiv (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) : Space d ≃L[ℝ] Space d :=
  (LinearEquiv.ofBijective (euclideanColumnLinear v)
    (let hinj := Function.LeftInverse.injective (euclideanDualCoordinates_column v hv)
     ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩)).toContinuousLinearEquiv

@[simp] theorem euclideanColumnEquiv_apply (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (x : Space d) :
    euclideanColumnEquiv v hv x = euclideanColumnLinear v x := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single additional parallel descriptor at the assembly entry -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

noncomputable def outerList (P : PolicyJetData m) (c : ℕ) : Finset PolicyDescriptor :=
  insert (.parallel 0 c) P.list

noncomputable def outerLongest (P : PolicyJetData m) (c : ℕ) : ℕ :=
  (P.outerList c).sup descriptorLength

theorem outerList_card (P : PolicyJetData m) (c : ℕ) :
    (P.outerList c).card ≤ (P.N+1)^4 := by
  have hN := P.N_pos
  have hbase := P.list_card
  have hcard := Finset.card_insert_le (.parallel 0 c) P.list
  have hone : 1 ≤ (P.N+1)^3 := one_le_pow₀ (by omega)
  have hpow : (P.N+1)^3+1 ≤ (P.N+1)^4 := by
    calc
      _ ≤ (P.N+1)^3+(P.N+1)^3 := by omega
      _ ≤ (P.N+1)^3*(P.N+1) := by nlinarith
      _ = _ := by ring
  exact hcard.trans ((Nat.add_le_add_right hbase 1).trans hpow)

theorem outerLongest_half (P : PolicyJetData m) {c : ℕ} (hc : 2*c ≤ P.N) :
    2*P.outerLongest c ≤ P.N := by
  have hlength (b) (hb : b ∈ P.outerList c) : descriptorLength b ≤ P.N/2 := by
    obtain rfl | hb := Finset.mem_insert.mp hb
    · simp only [descriptorLength,Nat.sub_zero]
      omega
    · have hp := PlanarFalconer.policyDescriptor_twice_length P.policy P.q_pos
        (Finset.mem_filter.mp hb).1
      have hN := P.base_N
      omega
  have hsup : P.outerLongest c ≤ P.N/2 := Finset.sup_le hlength
  omega

theorem outer_geometry (P : PolicyJetData m) {c : ℕ} (ha : P.a = 0) (ht : P.t = P.N)
    (hc : 4*c ≤ P.N) (hσ : 0 ≤ P.σ) (hσsmall : P.σ ≤ 1/100) :
    (c:ℝ)-P.a ≤ (P.t:ℝ)-c+2*P.σ*P.N ∧
    (P.outerLongest c:ℝ) ≤ (P.t:ℝ)-c+2*P.σ*P.N ∧
    10*P.σ*P.N ≤ (P.t:ℝ)-c := by
  have hcr : 4*(c:ℝ) ≤ P.N := by exact_mod_cast hc
  have hlong : 2*(P.outerLongest c:ℝ) ≤ P.N := by
    exact_mod_cast P.outerLongest_half (by omega : 2*c ≤ P.N)
  have hσN := mul_nonneg hσ (Nat.cast_nonneg P.N)
  have hsmall := mul_le_mul_of_nonneg_right hσsmall (Nat.cast_nonneg P.N : (0:ℝ) ≤ P.N)
  rw [ha,ht]
  push_cast
  constructor
  · nlinarith
  constructor <;> nlinarith

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TwoProfileInverseIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability of the two-profile original inverse family -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorInverseSymbols
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

noncomputable def twoProfilePairIntegral (_T : DescriptorInverseSymbols f g j R A B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag s : ℝ) (μ ν : Measure (Space (m+3))) (M P r : ℝ) : ℂ :=
  (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
              g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w
        ∂sphereMeasure (m+3) ∂μ.prod ν

end DescriptorInverseSymbols

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_EndpointWeightedDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted distance law for two different endpoint profiles

Both original marginal laws and their separate normalizations are retained.
The endpoint factors may be the actual descriptor products of different
regularized classes. No common probability law is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def endpointDistanceWeight {d : ℕ} (s : ℝ)
    (B C : Space d → Space d → ℝ) (z : Space d × Space d) : ℝ :=
  (dist z.1 z.2/s)^(-(((d:ℝ)-1)/2)) *
    B z.1 (NormedSpace.normalize (z.1-z.2)) * C z.2 (NormedSpace.normalize (z.1-z.2))

noncomputable def endpointWeightedDistance {d : ℕ} (μ ν : Measure (Space d))
    (M P s : ℝ) (B C : Space d → Space d → ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => ENNReal.ofReal
    ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z))).map (fun z => dist z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SpatialRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable product restrictions stay in the original endpoint jet class -/

namespace Falconer
open Set MeasureTheory

namespace DescriptorJetSymbol

noncomputable def restrictSpatial {n K L : ℕ} {F : Finset PlanarFalconer.PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol n K L F D) (S : Set (Space (n+2))) (hS : MeasurableSet S) :
    DescriptorJetSymbol n K L F D :=
  f.spatialMultiplier (S.indicator (fun _ => (1:ℂ))) (measurable_const.indicator hS)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx])

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterRestrictedConversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer scalar conversion with arbitrary measurable product restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def PolicyJetData.outerRestrictedDistance {m : ℕ} (P Q : PolicyJetData m) (c : ℕ)
    (A₁ A₂ : Set (Space (m+3))) : Measure ℝ :=
  endpointWeightedDistance
    ((P.ρ.restrict (P.Q.descendant P.X).carrier).restrict A₁)
    ((Q.ρ.restrict (Q.Q.descendant Q.X).carrier).restrict A₂)
    (profileModelMass P.profile P.N P.a) (profileModelMass Q.profile Q.N Q.a) 1
    (descriptorAmbientProduct P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i (P.outerList c) P.masks)
    (descriptorAmbientProduct Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i (Q.outerList c) Q.masks)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TwoPolicyEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the exact left and right policy symbols

Each self energy retains its own original regularized measure, descriptor
list, mask family and scalar normalization.
-/

namespace Falconer
open Set MeasureTheory

namespace PolicyJetData
variable {m K L : ℕ}

def diagonal (P : PolicyJetData m) (X : List (Fin (m+3) → Bool))
    (hX : X.length = P.a) : PolicyJetData m :=
  { P with X := X, Y := X, X_length := hX, Y_length := hX }

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FlexibleGraphChild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the recursive estimate to the actual outer graph children -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def rootBoundAt (P : PolicyJetData m) (c : ℕ) (σ κ η : ℝ) : ℝ :=
  4^(sourceSmoothingLevels σ κ+1)*
    (((2:ℝ)^P.N)^(2*P.policy c-
      PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
      500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η)+
      ((2:ℝ)^P.N)^(-10:ℝ))

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_OuterGraphData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Graph data for the single outer entry descriptor -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def outerGraphData (P : PolicyJetData m) (σ : ℝ) (hσeq : P.σ = σ)
    (k : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hσ : 0 < P.σ) (hJ : 0 < P.J) (hi : P.i+1 ≤ P.J)
    (hNlist : Classical.choose (eventual_descriptor_list_scale 4 hB hσ) ≤ P.N)
    (hNwidth : Classical.choose (uniform_graph_parallel_width (m+3) hσ hJ) ≤ P.N)
    (c : ℕ) (ha : P.a = 0) (ht : P.t = P.N) (hc : 4*c ≤ P.N)
    (hσsmall : P.σ ≤ 1/100)
    (hsep : ∀ b ∈ (P.outerList c), ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
      descriptorMaskRadius P.N P.σ b/2 ≤ dist w z)
    (c₀ C H : ℝ) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ 1/2)
    (hC : 1 ≤ C) (hCdim : 4*Real.sqrt (m+3:ℕ) ≤ C) (hH : 0 ≤ H)
    (hlarge : 40*Real.sqrt (m+3:ℕ) ≤ ((2:ℝ)^P.N)^(20*P.σ))
    (hlargeπ : 4*Real.pi ≤ ((2:ℝ)^P.N)^(20*P.σ))
    (S : Finset (Sphere (m+3))) (η : Sphere (m+3) → Sphere (m+3) → ℝ)
    (hcontrol : ∀ w ∈ S, ChartCapControl k (η w) (w : Space (m+3))
      (policyGraphRadius P.N P.a c P.σ c₀) H)
    (hnonneg : ∀ w ∈ S, ∀ z, 0 ≤ η w z) (hone : ∀ z, ∑ w ∈ S, η w z = 1) :
    JetStateGraphData (m+1) k (20*σ) B := by
  let p := c
  let g : ℕ := 0
  let δ := policyGraphRadius P.N P.a p P.σ c₀
  let τ := policyGraphWidth P.N p P.σ
  let E := descriptorListScale B P.N P.σ (P.outerLongest c) (P.outerList c)
  let Dsymbol := max 1 E
  let Dgraph := policyGraphScale P.N P.a p (P.outerLongest c) P.σ c₀ C
  have hap : P.a ≤ p := by dsimp [p]; omega
  have hpN : p ≤ P.N := by dsimp [p]; omega
  have hag : P.a ≤ g := by simp only [ha,g,Nat.le_refl]
  have hgp : g ≤ p := Nat.zero_le _
  have hgeometry := P.outer_geometry ha ht hc hσ.le hσsmall
  have hdepth : (p:ℝ)-P.a ≤ (P.t:ℝ)-p+2*P.σ*P.N := hgeometry.1
  have hlength : ((P.outerLongest c):ℝ) ≤ (P.t:ℝ)-p+2*P.σ*P.N := hgeometry.2.1
  have hscale :=
    policy_graph_scale_data (m+3) P.N_pos hσ hc₀ hcsmall hC hCdim
      hdepth hlength hgeometry.2.2 hlarge hlargeπ
  have hδ := hscale.1
  have hδsmall := hscale.2.1
  have hτ := hscale.2.2.1
  have hDgraph := hscale.2.2.2.1
  have hcap := hscale.2.2.2.2.1
  have hendpoint := hscale.2.2.2.2.2.1
  have hphase := hscale.2.2.2.2.2.2.1
  have hfreq := hscale.2.2.2.2.2.2.2.1
  have hlist := (Classical.choose_spec (eventual_descriptor_list_scale 4 hB hσ))
    P.N hNlist (P.outerLongest c) (P.outerList c) (P.outerList_card c)
  have hE : E ≤ descriptorDerivativeScale P.N P.σ (P.outerLongest c) := by
    have hh := hlist.2
    have he : 0 ≤ E := by dsimp [E,descriptorListScale]; positivity
    linarith
  have hsymbol : Dsymbol ≤ descriptorDerivativeScale P.N P.σ (P.outerLongest c) :=
    max_le (by linarith [hlist.1]) hE
  have hsymbolGraph : 1+Dsymbol ≤ Dgraph := policy_graph_symbol_scale hC hc₀ hsymbol
  have hside (Z : List (Fin (m+3) → Bool)) (hZ : Z.length = P.a) :
      (P.Q.descendant Z).side = (2:ℝ)^(-(P.a:ℝ)) := by
    rw [P.Q.descendant_side,P.unit,hZ,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div]
  have hsmallside (Z : List (Fin (m+3) → Bool)) (hZ : Z.length = P.a) :
      (P.Q.descendant Z).side/(2:ℝ)^(g-P.a) = 1/(2:ℝ)^g := by
    rw [descendant_common_band_scale P.Q P.unit Z hZ hag,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have hwidth : 2*τ+2*δ*(Real.sqrt (m+3:ℕ)*(1/(2:ℝ)^g)) ≤
      angularTestWidth P.N P.σ P.J (P.i+1) p := by
    have hh := (Classical.choose_spec (uniform_graph_parallel_width (m+3) hσ hJ))
      P.N hNwidth P.a g p (P.i+1) hag hi δ hδ.le
      (policyGraphRadius_le P.N P.a p P.σ c₀)
    simpa only [τ,policyGraphWidth_eq] using hh
  refine {
    Q := P.Q, unit := P.unit, ρ := P.ρ, profile := P.profile, N := P.N,
    s := P.s, lam := P.lam, regular := P.regular, N_pos := P.N_pos,
    a := P.a, p := p, g := g, ap := hap, pN := hpN, ag := hag, gp := hgp,
    σ := P.σ, σ_nonneg := hσ.le, gap := ?_, X := P.X, Y := P.Y,
    X_length := P.X_length, Y_length := P.Y_length, v := P.t,
    τ := τ, δ := δ, capBound := H, Dq := 1,
    Dmask := 8*max 1 ((2:ℝ)^(P.outerLongest c)*((2:ℝ)^P.N)^(-50*P.σ)),
    Dsymbol := Dsymbol, Dgraph := Dgraph,
    τ_pos := hτ, δ_pos := hδ, δ_small := hδsmall, capBound_nonneg := hH,
    Dq_nonneg := by norm_num, Dmask_one := ?_, Dsymbol_one := le_max_left _ _,
    Dgraph_one := hDgraph, symbol_scale := hsymbolGraph, cap_scale := hcap,
    endpoint_scale := ?_, phase_error := ?_,
    frequency := by simpa only [τ,Real.rpow_natCast,hσeq] using hfreq, test_scale := ?_,
    F := (P.outerList c), masks := P.masks, J := P.J, i := P.i, separated := hsep,
    mask_scale := ?_, list_scale := le_max_right _ _, parallel := Finset.mem_insert_self _ _,
    left_width := ?_, right_width := ?_, caps := S, partition := η,
    cap_control := hcontrol, cap_nonneg := hnonneg, partition_one := hone }
  · dsimp only [g]
    rw [ha,Nat.cast_zero,sub_self]
    positivity
  · have hh : 1 ≤ max 1 ((2:ℝ)^(P.outerLongest c)*((2:ℝ)^P.N)^(-50*P.σ)) := le_max_left _ _
    linarith
  · simpa only [hside P.X P.X_length] using hendpoint
  · rw [descendant_common_band_scale P.Q P.unit P.X P.X_length hap,
      hside P.X P.X_length]
    simpa only [δ,τ] using hphase
  · have htau : 4*τ*((2:ℝ)^(p-P.a)/(P.Q.descendant P.X).side) =
        4*((2:ℝ)^P.N)^(30*P.σ) := by
      dsimp only [τ]
      rw [P.Q.descendant_side,P.unit,P.X_length,policyGraphWidth_eq]
      have hp : (2:ℝ)^P.a*(2:ℝ)^(p-P.a) = (2:ℝ)^p := by
        rw [← pow_add,Nat.add_sub_of_le hap]
      rw [← hp]
      field_simp
    rw [htau]
    exact Nat.le_ceil _
  · intro b hb
    exact descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)
  · simpa only [hsmallside P.X P.X_length] using hwidth
  · simpa only [hsmallside P.Y P.Y_length] using hwidth

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_TwoGraphChildren
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate self energies for the children of a two-profile graph -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

noncomputable def selfChildMaximum (G : JetStateGraphData n k α B)
    (K : ℕ) (A : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  childJetStateMaximum n K k G.Dq (G.F.filter (fun b => G.p < PlanarFalconer.descriptorAnchor b))
    G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A
    G.X G.X (G.p-G.a) (profileModelMass G.profile G.N G.p) G.p G.v Ψ

noncomputable def childTransform (G : JetStateGraphData n k α B) {K : ℕ}
    (A : ℝ) (f : DescriptorJetSymbol n K k G.F G.Dq)
    (X : List (Fin (n+2) → Bool)) (z : ℝ × Sphere (n+2)) : ℂ :=
  endpointTransform (G.ρ.restrict ((G.Q.descendant G.X).descendant X).carrier)
    (profileModelMass G.profile G.N G.p) (G.symbol f A) z.1 z.2

end JetStateGraphData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_TwoProfileGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph reduction for two original regularized profiles

Only geometric scales are shared. The laws, profiles, descriptor lists,
mask families and endpoint multipliers remain separate.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

structure JetGraphAlignment {n k : ℕ} {α B : ℝ}
    (G H : JetStateGraphData n k α B) : Prop where
  N : H.N = G.N
  a : H.a = G.a
  p : H.p = G.p
  lam : H.lam = G.lam
  σ : H.σ = G.σ
  v : H.v = G.v
  τ : H.τ = G.τ
  δ : H.δ = G.δ
  Dgraph : H.Dgraph = G.Dgraph

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

noncomputable def twoProfileCoefficient (G H : JetStateGraphData n k α B) : ℝ :=
  2*11^(n+2)*((2:ℝ)^G.N)^(
    -(profileExcess (d := n+2) G.profile G.N G.p-profileExcess (d := n+2) G.profile G.N G.a)-
    (profileExcess (d := n+2) H.profile H.N H.p-profileExcess (d := n+2) H.profile H.N H.a)+
    min (PlanarFalconer.height (profileExcess (d := n+2) G.profile G.N) G.a G.p)
      (PlanarFalconer.height (profileExcess (d := n+2) H.profile H.N) H.a H.p)+
    (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*G.σ+4*(((n+2:ℕ):ℝ)+1)*G.lam)

noncomputable def twoProfileError (G H : JetStateGraphData n k α B) (A C W T : ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(G.v-G.a))*
    ((profileModelMass G.profile G.N G.p/profileModelMass G.profile G.N G.a)*
      (profileModelMass H.profile H.N H.p/profileModelMass H.profile H.N H.a))^2*
    capGraphError (n+2) k A C W ((2:ℝ)^G.N) T
      (profileModelMass G.profile G.N G.p) (profileModelMass H.profile H.N H.p)
      G.capBound 1 G.Dgraph G.v G.τ G.caps.card
      ((G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
        (H.Q.descendant H.X).occupiedPaths H.ρ (H.p-H.a)).card

end JetStateGraphData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_TwoGraphScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common graph scale and uniform error for the two outer profiles -/

namespace Falconer
open Set MeasureTheory

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

def withGraphScale (G : JetStateGraphData n k α B) (D : ℝ) (hD : G.Dgraph ≤ D) :
    JetStateGraphData n k α B :=
  { G with
    Dgraph := D
    Dgraph_one := G.Dgraph_one.trans hD
    symbol_scale := G.symbol_scale.trans hD
    cap_scale := G.cap_scale.trans hD
    endpoint_scale := G.endpoint_scale.trans
      (mul_le_mul_of_nonneg_left hD (div_nonneg G.τ_pos.le (by norm_num))) }

end JetStateGraphData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_OuterGraphStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two-profile graph step at the common entry depth -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

namespace PolicyJetData
variable {m : ℕ}

noncomputable def outerCoefficient (P Q : PolicyJetData m) (c : ℕ) : ℝ :=
  2*11^(m+3)*((2:ℝ)^P.N)^(
    -(profileExcess (d := m+3) P.profile P.N c-profileExcess (d := m+3) P.profile P.N P.a)-
    (profileExcess (d := m+3) Q.profile Q.N c-profileExcess (d := m+3) Q.profile Q.N Q.a)+
    min (PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a c)
      (PlanarFalconer.height (profileExcess (d := m+3) Q.profile Q.N) Q.a c)+
    (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*P.σ+4*(((m+3:ℕ):ℝ)+1)*P.lam)

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterRootGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outer graph coefficient combined with the two recursive roots -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def PolicyJetData.rootExponentAt {m : ℕ} (P : PolicyJetData m)
    (c : ℕ) (σ κ η : ℝ) : ℝ :=
  2*P.policy c-PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
    500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PublishedFurstenberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published planar incidence input

Orponen–Shmerkin–Wang, *Kaufman and Falconer estimates for radial projections
and a continuum version of Beck's theorem*, Geom. Funct. Anal. 34 (2024),
Definitions 2.5–2.6 and Theorem 2.7 (arXiv:2209.00348), following
Orponen–Shmerkin, Duke Math. J. 172 (2023), Theorem 1.3 and Remark 1.4.

The proposition below is the separated finite-set specialization in one
bounded, nonvertical line chart needed by `ang:planar-measures`. Only
`0 < b ≤ 1/2` and `b < f < 1` are retained. The chart identifies a line
with its slope and intercept. Equivalence with the published line metric
and replacement of covering counts by cardinalities cost fixed constants;
the epsilon and the small-scale threshold below are chosen after these
constants, not identified with the published theorem's original epsilon.

This is an explicit proposition to be supplied as a hypothesis. It is not
a global axiom, and no proof of this published theorem is claimed here.
-/

namespace Falconer

/-- Points and line parameters both use the Euclidean metric in this chart. -/
def FiniteSeparatedAt (δ : ℝ) (P : Finset (Space 2)) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y

/-- The normalization is by the cardinality of the entire finite set. -/
def NormalizedFiniteBallBound (δ s K : ℝ) (P : Finset (Space 2)) : Prop := by
  classical
  exact ∀ z : Space 2, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ((P.filter (fun x => dist x z ≤ r)).card : ℝ) ≤ K * r ^ s * (P.card : ℝ)

def InBoundedLineChart (P : Finset (Space 2)) : Prop :=
  ∀ x ∈ P, |x 0| ≤ 1 ∧ |x 1| ≤ 1

/-- A point lies in the closed Euclidean δ-neighborhood of the line
with slope `l 0` and intercept `l 1`. -/
def TubeIncident (δ : ℝ) (x l : Space 2) : Prop :=
  |x 1 - l 0 * x 0 - l 1| / Real.sqrt (1 + (l 0) ^ 2) ≤ δ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PlanarIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative planar measure incidence obstruction

This is the measure-to-finite-set step of `ang:planar-measures`. The only
published input is the finite-set specialization of the planar
Furstenberg theorem. All losses from the two original-label sampling steps
are explicit; no geometric gain is assumed.
-/

namespace Falconer
open Set MeasureTheory Real
attribute [local instance] Classical.propDecidable

noncomputable def samplingBallLoss (K B s : ℝ) : ℝ := ((exp 1-1)*K+B)*8^s

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarGainNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorbing the explicit losses in the planar measure obstruction

Only fixed constants, logarithms and ceilings are absorbed here. The
underlying incidence estimate has already been proved from the cited
published input.
-/

namespace Falconer
open Real Filter
open scoped Topology

structure PlanarSamplingReady (δ b f η ε : ℝ) (J : ℕ) : Prop where
  scale_pos : 0 < δ
  scale_small : δ ≤ 1/4
  budget : 1 ≤ -10*log δ
  point_loss : 2*(8*samplingBallLoss (δ^(-η)) (-10*log δ) f/δ^η)^2 ≤ δ^(-ε)
  direction_loss : 8*2^b*(samplingBallLoss (δ^(-η)) (-10*log δ) b)^2/δ^η ≤ δ^(-ε)
  count : (Nat.ceil (δ^(-b)) : ℝ) ≤ δ^(-b-ε/4)
  cover : (δ^(-b-η)) * (2*J+1) ≤ δ^(-b-ε/4)
  tail : (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) *
    exp (-(-10*log δ)) ≤ δ^η/16

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_StartingMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

def FrostmanBallBound {d : ℕ} (μ : Measure (Space d)) (s C : ℝ) : Prop :=
  ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C * r^s)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanRieszEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Riesz energies from the original all-dimensional Frostman bounds

The dyadic potential argument and its scalar scale identity are dimension
independent.
-/

namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

noncomputable def euclideanRieszPotential (μ : Measure (Space d)) (u : ℝ)
    (x : Space d) : ℝ≥0∞ := ∫⁻ y, (edist x y)^(-u) ∂μ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BoundedPotentialCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive compact restriction with bounded measurable potential -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

@[fun_prop] theorem euclideanRieszPotential_measurable (μ : Measure (Space d)) [SFinite μ]
    (u : ℝ) : Measurable (euclideanRieszPotential μ u) := by
  apply Measurable.lintegral_prod_right
  exact (by fun_prop : Measurable (fun p : Space d × Space d => (edist p.1 p.2)^(-u)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRieszKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian projection of a fixed vector: small balls and inverse moments -/
namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d m : ℕ}

@[fun_prop] theorem gaussianRowMap_joint_continuous :
    Continuous (fun p : (Fin m → Space d) × Space d => gaussianRowMap p.1 p.2) := by
  change Continuous (fun p : (Fin m → Space d) × Space d =>
    WithLp.toLp 2 (fun i => inner ℝ (p.1 i) p.2))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => ((continuous_apply i).comp continuous_fst).inner continuous_snd)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive affine changes of scale preserve original radial directions -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialZoom (a : ℝ) (ha : a ≠ 0) (c : Space d) : Space d ≃ₜ Space d where
  toFun x := a • (x-c)
  invFun y := c+a⁻¹ • y
  left_inv x := by simp only [smul_smul,inv_mul_cancel₀ ha,one_smul]; abel
  right_inv y := by simp only [add_sub_cancel_left,smul_smul,mul_inv_cancel₀ ha,one_smul]
  continuous_toFun := (continuous_id.sub continuous_const).const_smul a
  continuous_invFun := continuous_const.add (continuous_id.const_smul a⁻¹)

@[simp] theorem radialZoom_apply (a : ℝ) (ha : a ≠ 0) (c x : Space d) :
    radialZoom a ha c x = a • (x-c) := rfl

@[simp] theorem radialZoom_sub (a : ℝ) (ha : a ≠ 0) (c x y : Space d) :
    radialZoom a ha c x-radialZoom a ha c y = a • (x-y) := by
  simp only [radialZoom_apply,← smul_sub,sub_sub_sub_cancel_right]

noncomputable def zoomPairSet (e : Space d ≃ₜ Space d)
    (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  {p | (e.symm p.1,e.symm p.2) ∈ G}

@[simp] theorem mem_zoomPairSet (e : Space d ≃ₜ Space d) (G : Set (Space d × Space d))
    (z x : Space d) : (e z,e x) ∈ zoomPairSet e G ↔ (z,x) ∈ G := by
  simp only [zoomPairSet,mem_ofPred_eq,e.symm_apply_apply]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original separated pairs with simultaneous projected Frostman bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure ProjectedStartingPair {d : ℕ} (ζ : ProbabilityMeasure (Space d))
    (m : ℕ) (s ε : ℝ) where
  projection : Space d →L[ℝ] Space m
  left : ProbabilityMeasure (Space d)
  right : ProbabilityMeasure (Space d)
  left_compact : IsCompact (left : Measure (Space d)).support
  right_compact : IsCompact (right : Measure (Space d)).support
  left_ac : (left : Measure (Space d)) ≪ (ζ : Measure (Space d))
  right_ac : (right : Measure (Space d)) ≪ (ζ : Measure (Space d))
  constant : ℝ
  constant_pos : 0 < constant
  left_frostman : FrostmanBallBound (left : Measure (Space d)) s constant
  right_frostman : FrostmanBallBound (right : Measure (Space d)) s constant
  projected_left_frostman : FrostmanBallBound ((left : Measure (Space d)).map projection) s constant
  projected_right_frostman : FrostmanBallBound ((right : Measure (Space d)).map projection) s constant
  contractive : ‖projection‖ ≤ 1
  radius : ℝ
  radius_pos : 0 < radius
  lower : ℝ
  lower_pos : 0 < lower
  direction : Space d
  direction_unit : ‖direction‖ = 1
  geometry : ∀ x ∈ (left : Measure (Space d)).support,
    ∀ y ∈ (right : Measure (Space d)).support,
      radius/2 ≤ dist x y ∧ dist x y ≤ 2*radius ∧
      lower ≤ ‖projection (radialDirection x y)‖ ∧
      lower ≤ ‖projection (radialDirection y x)‖ ∧
      dist (radialDirection x y) direction < ε

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerFourPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-edge paths and their sum labels. Injectivity of the labels is the
counting step converting dense neighborhoods into small difference sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

abbrev IntegerPath := Σ _v : ℤ, ℤ × ℤ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerFivePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Five-edge sum labels give the two-sided small-sumset refinement used
to pass from projection collisions to a Cartesian product. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

abbrev IntegerFivePath := Σ _b : ℤ, IntegerPath

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LoomisWhitneyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coordinate splitting for the Loomis–Whitney induction -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

abbrev eraseFinCoordinate {X : Type*} {n : ℕ} (i : Fin (n+1))
    (z : Fin (n+1) → X) : Fin n → X := fun j => z (i.succAbove j)

omit [Fintype X] in
@[simp] theorem remove_coordinate_cons_zero {n : ℕ} (x : X) (y : Fin n → X) :
    eraseFinCoordinate (0 : Fin (n+1)) (Fin.cons x y) = y := by
  ext j
  simp [eraseFinCoordinate]

omit [Fintype X] in
@[simp] theorem remove_coordinate_cons_succ {n : ℕ}
    (i : Fin (n+1)) (x : X) (y : Fin (n+1) → X) :
    eraseFinCoordinate i.succ (Fin.cons x y) = Fin.cons x (eraseFinCoordinate i y) :=
  Fin.cons_comp_succ_succAbove x y i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeightedLoomisStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite weighted Loomis–Whitney induction step -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

def FiniteWeightedLoomis (n : ℕ) (X : Type*) [Fintype X] : Prop :=
  ∀ f : Fin (n+1) → (Fin n → X) → ℝ, (∀ i z, 0 ≤ f i z) →
    (∑ z : Fin (n+1) → X, ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ))) ≤
      ∏ i : Fin (n+1), (∑ y : Fin n → X, f i y)^(1/(n:ℝ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_BorelProductPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite disjoint Borel products in the original ambient space -/
namespace Falconer
open Set MeasureTheory

/-- The finite partition used by the graph regularization, with its actual cardinality. -/
def HasBorelProductPartition {d : ℕ} (S : Set (Space d × Space d)) (K : ℝ) : Prop :=
  ∃ n : ℕ, (n:ℝ) ≤ K ∧ ∃ A B : Fin n → Set (Space d),
    (∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i)) ∧
    (Pairwise fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) ∧
    S = ⋃ i, A i ×ˢ B i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

@[fun_prop] theorem measurable_radialDirection_joint {d : ℕ} :
    Measurable (fun z : Space d × Space d => radialDirection z.1 z.2) := by
  unfold radialDirection
  fun_prop

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyPlateCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual dyadic cell-pair exclusion generated by heavy affine plates -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

def HeavyPlateHits (ρ : Measure (Space d)) (P Q : DyadicCube d) (r m : ℝ) : Prop :=
  ∃ w : Space d, ‖w‖ = 1 ∧ ∃ a : ℝ,
    ENNReal.ofReal m ≤ ρ {x | |inner ℝ w x-a| ≤ r} ∧
    (∃ x ∈ P.carrier, |inner ℝ w x-a| ≤ r) ∧
    (∃ x ∈ Q.carrier, |inner ℝ w x-a| ≤ r)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_OccupiedRadialTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Occupied dyadic trees with a common full-measure source core -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def DyadicCube.emptyTreeCells (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : Set (Space d) :=
  ⋃ n ∈ Finset.range (N+1),
    ⋃ p ∈ cubePaths d n \ Q.occupiedPaths μ n, (Q.descendant p).carrier

noncomputable def DyadicCube.occupiedTreeCore (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : Set (Space d) :=
  Q.carrier \ Q.emptyTreeCells μ N

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PublishedHeavyPlates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published heavy-hyperplane cover used by the coarse-filter construction

P. Shmerkin, *A non-linear version of Bourgain's projection theorem*,
J. Eur. Math. Soc. 25 (2023), 4155--4204, Appendix B, Lemma B.3,
printed pages 4201--4202, DOI 10.4171/JEMS/1283.
Publisher PDF: https://ems.press/content/serial-article-files/32954 .

This is only the hyperplane case k=d-1, at the single scale used in the
application, with heavy threshold delta^(a/8192). The lower-dimensional
concentration hypothesis is retained explicitly. The conclusion covers
each heavy plate in the unit ball by one of finitely many thicker plates.
The constant is allowed to depend on the dimension, a and C. No assertion
about dyadic filters, retained product mass or distance sets is assumed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def heavyPlateExponent (a : ℝ) : ℝ := a/8192

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From radial projection moments to integer cap availability

The radial pushforwards form a Markov kernel. Mathlib's kernel
Radon--Nikodym derivative supplies a jointly measurable version of all
their angular densities, so separate choices of densities are unnecessary.
This connects the published radial-moment input to the truncation step.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The radial projection law, with the pin as its kernel parameter. -/
noncomputable def radialKernel {d : ℕ} (ν : ProbabilityMeasure (Space d)) :
    Kernel (Space d) (Space d) :=
  ((Kernel.id : Kernel (Space d) (Space d)) ×ₖ
    Kernel.const (Space d) (ν : Measure (Space d))).map
      (fun z : Space d × Space d => radialDirection z.1 z.2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_OrderedEndpointIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply interval gains to an ordered subfamily; omitted gaps use the
nonempty-pencil estimate. No gain or profile hypothesis is imposed on a gap. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

def OrderedBlockIntervals (i j : ℕ) : List (ℕ × ℕ) → Prop
  | [] => j ≤ i
  | (a,b)::R => a ≤ i ∧ b ≤ a ∧ OrderedBlockIntervals b j R

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness of normalized Lipschitz scale profiles -/

namespace Falconer
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal

abbrev ProfileDomain := Icc (0:ℝ) 1
abbrev BoundedProfile := ProfileDomain →ᵇ ℝ

end Falconer

end OAI
end


