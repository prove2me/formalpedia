-- Prove2me | Definitions.Def_OAIQ054H000
-- name    : OAIQ054H000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:42:19.035604+00:00
-- url     : https://prove2.me/theorems/bf99da68-5934-496d-840a-ed9d62611bc4
-- title:
--   Definitions bundle OAIQ054H000 of the split of OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 917 declarations of OpenAI's Lean: 537 definitions, 5 inductive types or structures, 51 instances and 324 theorems. The definitions and types are `OAI.ComplexRegularization.differential`, `OAI.ComplexRegularization.regularize`, `OAI.HardSphere.BathSlice.LargeParentMarked`, `OAI.HardSphere.BathSlice.Point`, `OAI.HardSphere.BathSlice.SmallComponent`, `OAI.HardSphere.BathSlice.bad`, `OAI.HardSphere.BathSlice.bathWitnessCover`, `OAI.HardSphere.BathSlice.boxWeight`, `OAI.HardSphere.BathSlice.closeSet`, `OAI.HardSphere.BathSlice.coarseCenter`, `OAI.HardSphere.BathSlice.exceptional`, `OAI.HardSphere.BathSlice.filledRegion`, `OAI.HardSphere.BathSlice.forbidden`, `OAI.HardSphere.BathSlice.gridCorner`, `OAI.HardSphere.BathSlice.largeBoxUnion`, `OAI.HardSphere.BathSlice.liftPoint`, `OAI.HardSphere.BathSlice.liftedCube`, `OAI.HardSphere.BathSlice.microColumn`, `OAI.HardSphere.BathSlice.microCube`, `OAI.HardSphere.BathSlice.microMesh`, `OAI.HardSphere.BathSlice.microPeriod`, `OAI.HardSphere.BathSlice.omitted`, `OAI.HardSphere.BathSlice.parent`, `OAI.HardSphere.BathSlice.retained`, `OAI.HardSphere.BathSlice.rootBox`, `OAI.HardSphere.BathSlice.siteCenter`, `OAI.HardSphere.BathSlice.siteCube`, `OAI.HardSphere.BathSlice.siteCubeEmbedding`, `OAI.HardSphere.BathSlice.siteRep`, `OAI.HardSphere.BathSlice.slice`, `OAI.HardSphere.BathSlice.smallFills`, `OAI.HardSphere.BathSlice.witnessBox`, `OAI.HardSphere.Bridge.GoodLeg`, `OAI.HardSphere.Bridge.LegMeshRegular`, `OAI.HardSphere.Bridge.Noise`, `OAI.HardSphere.Bridge.StrongExcept`, `OAI.HardSphere.Bridge.SuccessExcept`, `OAI.HardSphere.Bridge.TrialCollision`, `OAI.HardSphere.Bridge.TrialConfined`, `OAI.HardSphere.Bridge.TrialCutoff` and 502 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HardSphere, in whole or in part: `HardSphere_Allocation_Allocation`, `HardSphere_Allocation_CoarsePhysical`, `HardSphere_Allocation_NearLift`, `HardSphere_Allocation_PhysicalAssembly`, `HardSphere_Allocation_PhysicalBranchEstimates`, `HardSphere_Allocation_PhysicalDatum`, `HardSphere_Allocation_PhysicalLabelLaw`, `HardSphere_Allocation_PhysicalLifted`, `HardSphere_Allocation_PhysicalPrimary`, `HardSphere_Allocation_PhysicalReference`, `HardSphere_Allocation_PhysicalReferenceRaw`, `HardSphere_Allocation_PhysicalRouteAuxiliary`, `HardSphere_Allocation_PhysicalRouteFactors`, `HardSphere_Allocation_PhysicalRouteGeometry`, `HardSphere_Allocation_PhysicalSupported`, `HardSphere_Allocation_PhysicalTargets`, `HardSphere_Allocation_PhysicalVertex`, `HardSphere_Allocation_RouteFields`, `HardSphere_Allocation_TaggedReference`, `HardSphere_Allocation_WeightedExpose`, `HardSphere_Bridges_ActualReverse`, `HardSphere_Bridges_AffineVolume`, `HardSphere_Bridges_BridgeAssemble`, `HardSphere_Bridges_BridgeAverage`, `HardSphere_Bridges_BridgeBlocks`, `HardSphere_Bridges_BridgeHighMoment`, `HardSphere_Bridges_BridgeMoment`, `HardSphere_Bridges_BridgeNoise`, `HardSphere_Bridges_BridgeReference`, `HardSphere_Bridges_BridgeResidual`, `HardSphere_Bridges_BridgeSplit`, `HardSphere_Bridges_BridgeStrongRegular`, `HardSphere_Bridges_BridgeWiener`, `HardSphere_Bridges_BridgeWindow`, `HardSphere_Bridges_CollisionBudget`, `HardSphere_Bridges_ConfinedLift`, `HardSphere_Bridges_EarlyTorusHit`, `HardSphere_Bridges_ExposedReference`, `HardSphere_Bridges_GaussianDensity`, `HardSphere_Bridges_GaussianMixture`, `HardSphere_Bridges_GaussianPacking`, `HardSphere_Bridges_GroundBridge`, `HardSphere_Bridges_IncrementMoment`, `HardSphere_Bridges_Index`, `HardSphere_Bridges_JointCollision`, `HardSphere_Bridges_LocalReference`, `HardSphere_Bridges_MeshLegHit`, `HardSphere_Bridges_NormalizedPrefix`, `HardSphere_Bridges_PartialIndex`, `HardSphere_Bridges_PeriodShift`, `HardSphere_Bridges_PhysicalEndpoint`, `HardSphere_Bridges_PhysicalFactorChecks`, `HardSphere_Bridges_PhysicalInsertion`, `HardSphere_Bridges_PhysicalPair`, `HardSphere_Bridges_PhysicalSparse`, `HardSphere_Bridges_PhysicalSuccess`, `HardSphere_Bridges_PrefixMap`, `HardSphere_Bridges_ReversePair`, `HardSphere_Bridges_ReverseTime`, `HardSphere_Bridges_RouteAuxiliary`, `HardSphere_Bridges_SegmentMeasurable`, `HardSphere_Bridges_SegmentSimplify`, `HardSphere_Bridges_SelectedReverse`, `HardSphere_Bridges_SupplyIntegral`, `HardSphere_Bridges_TrialCutoff`, `HardSphere_Bridges_TrialHitMeasure`, `HardSphere_Bridges_TrialScalarBound`, `HardSphere_Bridges_WienerStart`, `HardSphere_Collisions_PartialPhysicalLaw`, `HardSphere_Collisions_PhysicalCollisionReference`, `HardSphere_Comparison_Affinity`, `HardSphere_Comparison_ConditionalLikelihood`, `HardSphere_Comparison_ConditionalTagDensity`, `HardSphere_Comparison_ExactFiberLikelihood`, `HardSphere_Comparison_FDerivIntegral`, `HardSphere_Comparison_FiberNormalize`, `HardSphere_Comparison_MixtureMoment`, `HardSphere_Comparison_ParameterTarget`, `HardSphere_Comparison_PhysicalCellReference`, `HardSphere_Comparison_PhysicalObservedLaw`, `HardSphere_Comparison_SumMoment`, `HardSphere_Comparison_TaggedMoment`, `HardSphere_Conditioning_GlobalExposure`, `HardSphere_Conditioning_PairCloseLabels`, `HardSphere_Conditioning_PairFiber`, `HardSphere_Conditioning_PermutationObserved`, `HardSphere_Conditioning_PhysicalObservation`, `HardSphere_Conditioning_PhysicalRoute`, `HardSphere_Conditioning_PrimaryProduct`, `HardSphere_Conditioning_ProductExpose`, `HardSphere_Conditioning_ProductNormalize`, `HardSphere_Conditioning_ReferenceResample`, `HardSphere_Conditioning_RestrictedMeasure`, `HardSphere_Conditioning_RetainedObservation`, `HardSphere_Conditioning_ReverseConfigurationPath`, `HardSphere_Conditioning_RouteMatches`, `HardSphere_Conditioning_RoutePartition`, `HardSphere_Conditioning_SharedRoute`, `HardSphere_Conditioning_SharedTransport`, `HardSphere_Conditioning_SupportedPair`, `HardSphere_Conditioning_SymmetricTag`, `HardSphere_Cutoffs_ChordLift`, `HardSphere_Cutoffs_CubicMoment`, `HardSphere_Cutoffs_DiameterTail`, `HardSphere_Cutoffs_MeshMoment`, `HardSphere_Cutoffs_Near`, `HardSphere_Cutoffs_PathDiameter`, `HardSphere_Cutoffs_PathLift`, `HardSphere_Cutoffs_Regularize`, `HardSphere_Cutoffs_ThreeTorus`, `HardSphere_Density_DensityOperators`, `HardSphere_FormDomain_Basic`, `HardSphere_FormDomain_HilbertJet`, `HardSphere_Fourier_ArgumentAdd`, `HardSphere_Geometry_AddedSites`, `HardSphere_Geometry_AnimalFamily`, `HardSphere_Geometry_AuxiliaryChecks`, `HardSphere_Geometry_BadGraph`, `HardSphere_Geometry_BoxWeight`, `HardSphere_Geometry_CandidateConstant`, `HardSphere_Geometry_CenteredCircleLift`, `HardSphere_Geometry_ConfigurationPath`, `HardSphere_Geometry_CoordinateLine`, `HardSphere_Geometry_CubeCell`, `HardSphere_Geometry_DependentChecks`, `HardSphere_Geometry_DiscreteTorus`, `HardSphere_Geometry_EndpointDanger`, `HardSphere_Geometry_EndpointLift`, `HardSphere_Geometry_EndpointsExterior`, `HardSphere_Geometry_EuclideanTorus`, `HardSphere_Geometry_FilledRegion`, `HardSphere_Geometry_FinsetProd`, `HardSphere_Geometry_FirstVariation`, `HardSphere_Geometry_FreePathExpectation`, `HardSphere_Geometry_FrozenChecks`, `HardSphere_Geometry_GridAllocation`, `HardSphere_Geometry_GridCorner`, `HardSphere_Geometry_HalfShiftCover`, `HardSphere_Geometry_HeadLift`, `HardSphere_Geometry_InjectiveNear`, `HardSphere_Geometry_InnerClmRealRight`, `HardSphere_Geometry_JoinConfiguration`, `HardSphere_Geometry_LabelLift`, `HardSphere_Geometry_LargeParentMarked`, `HardSphere_Geometry_LiftedBadComponent`, `HardSphere_Geometry_LocalCheck`, `HardSphere_Geometry_LocalCloseLabels`, `HardSphere_Geometry_MicroPeriod`, `HardSphere_Geometry_ParentStep`, `HardSphere_Geometry_PathPermutation`, `HardSphere_Geometry_PathSlots`, `HardSphere_Geometry_RealComp`, `HardSphere_Geometry_RoundBox`, `HardSphere_Geometry_SelectedUnitCellPenalty`, `HardSphere_Geometry_SimplePath`, `HardSphere_Geometry_SiteCube`, `HardSphere_Geometry_SmallComponent`, `HardSphere_Geometry_SmoothMultiplier`, `HardSphere_Geometry_SqTwiceSqAbs`, `HardSphere_Geometry_StarOffsets`, `HardSphere_Geometry_TorusLiftBox`, `HardSphere_Geometry_TorusNear`, `HardSphere_Geometry_UniformBath`, `HardSphere_Geometry_Vertex`, `HardSphere_Kernels_ExposedPhysicalPair`, `HardSphere_Kernels_ExposedTrials`, `HardSphere_Kernels_FiniteKernelPi`, `HardSphere_Kernels_ParameterPair`, `HardSphere_Kernels_ParameterSuccess`, `HardSphere_Kernels_TrialKernel`, `HardSphere_Model`, `HardSphere_Orbitals_Bump`, `HardSphere_Orbitals_CellPartition`, `HardSphere_Orbitals_CenteredCell`, `HardSphere_Orbitals_Chi`, `HardSphere_Orbitals_Chi2`, `HardSphere_Orbitals_FreePathLawFiniteDeletion`, `HardSphere_Orbitals_Joint`, `HardSphere_Orbitals_PhysicalOrbitalReference`, `HardSphere_Orbitals_Profile`, `HardSphere_Orbitals_SelectedDeletion`, `HardSphere_PathBounds_ExpNatTail`, `HardSphere_PathBounds_FreeVisitProbability`, `HardSphere_PathBounds_FreeVisitTravel`, `HardSphere_PathBounds_InteractingVisits`, `HardSphere_PathBounds_SingleVisitDefect`, `HardSphere_PathBounds_VisitCounts`, `HardSphere_PathBounds_VisitPacking`, `HardSphere_Paths_AcceptedIntegrand`, `HardSphere_Paths_Admissible`, `HardSphere_Paths_Index`, `HardSphere_Paths_LevelList`, `HardSphere_Paths_LiftedSkeleton`, `HardSphere_Paths_NearPotential`, `HardSphere_Paths_SkeletonHitConstant`, `HardSphere_Paths_TimeGaps`, `HardSphere_Thermodynamics_BridgeScaleTail`, `HardSphere_Thermodynamics_PhysicalScaleData`, `HardSphere_Thermodynamics_ThermodynamicCalibration`, `HardSphere_Thermodynamics_TrialScale`.
--
--   **Imports.** It imports the published bundle `Def_HardSphere`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ054H002`; the statements `OAI.HardSphere.Bridge.physical_failure_sum`, `OAI.HardSphere.CellOrbital.physical_deficiency`, `OAI.HardSphere.Groups.PhysicalRouteAux.path_bounds` and `OAI.HardSphere.Groups.physicalRouteAux_nonempty`.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HardSphere at commit adc7f12

import Mathlib
import Definitions.Def_HardSphere

section
-- module Solutions.OAIQ054_HS.Compat
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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

abbrev Index := Unit ⊕ (Σ n : ℕ, Fin (2 ^ n))
abbrev Noise := Index → ℝ
abbrev Time := unitInterval
instance instMeasurableSpaceContinuousMapElemRealTime : MeasurableSpace C(Time, ℝ) := borel _
instance instBorelSpaceContinuousMapElemRealTime : BorelSpace C(Time, ℝ) := ⟨rfl⟩

def law : Measure Noise := Measure.infinitePi (fun _ : Index ↦ gaussianReal 0 1)
instance instIsProbabilityMeasureNoiseLaw : IsProbabilityMeasure law := by unfold law; infer_instance

def tent (n : ℕ) (k : Fin (2 ^ n)) (t : ℝ) : ℝ :=
  max 0 (1 - |(2 : ℝ) ^ (n + 1) * t - (2 * (k : ℝ) + 1)|)

def tentMap (n : ℕ) (k : Fin (2 ^ n)) : C(Time, ℝ) :=
  ⟨fun t ↦ tent n k t, by unfold tent; fun_prop⟩

def amplitude (n : ℕ) : ℝ := (1/2 : ℝ) * (Real.sqrt 2)⁻¹ ^ n

def level (n : ℕ) (ω : Noise) : C(Time, ℝ) :=
  amplitude n • ∑ k : Fin (2 ^ n), ω (.inr ⟨n, k⟩) • tentMap n k

def path (ω : Noise) : C(Time, ℝ) :=
  ω (.inl ()) • ⟨fun t ↦ t.val, continuous_subtype_val⟩ + ∑' n, level n ω

lemma continuous_level (n : ℕ) : Continuous (level n) := by
  unfold level
  fun_prop

lemma measurable_path : Measurable path := by
  unfold path
  apply Measurable.add
  · exact (by fun_prop : Continuous (fun ω : Noise ↦
      ω (.inl ()) • (⟨fun t : Time ↦ t.val, continuous_subtype_val⟩ : C(Time, ℝ)))).measurable
  · exact Measurable.tsum fun n ↦ (continuous_level n).measurable

def wiener : Measure C(Time, ℝ) := law.map path

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PartialIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

abbrev BridgeIndex := Σ n : ℕ, Fin (2^n)
abbrev BridgeNoise := BridgeIndex → ℝ

def linearPath : C(Time,ℝ) := ⟨fun t ↦ t.val, continuous_subtype_val⟩
def rest (ω : Noise) : BridgeNoise := fun i ↦ ω (.inr i)
def embedRest (η : BridgeNoise) : Noise := Sum.elim (fun _ ↦ 0) η
def bridgeMap (η : BridgeNoise) : C(Time,ℝ) := path (embedRest η)
def bridge (ω : Noise) : C(Time,ℝ) := bridgeMap (rest ω)

lemma measurable_bridgeMap : Measurable bridgeMap := by
  apply measurable_path.comp
  apply Measurable.of_eval
  intro i
  cases i with
  | inl u => exact measurable_const
  | inr i => exact measurable_pi_apply i

lemma measurable_rest : Measurable rest := Measurable.of_eval fun _ ↦ measurable_pi_apply _
lemma measurable_bridge : Measurable bridge := measurable_bridgeMap.comp measurable_rest

def bridgeLaw : Measure C(Time,ℝ) := law.map bridge
instance instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw : IsProbabilityMeasure bridgeLaw := by unfold bridgeLaw; exact Measure.isProbabilityMeasure_map measurable_bridge.aemeasurable

def prefixTime (u : Time) : C(Time,Time) where
  toFun t := ⟨(u:ℝ)*(t:ℝ), mul_nonneg u.property.1 t.property.1,
    (mul_le_of_le_one_left t.property.1 u.property.2).trans t.property.2⟩
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

def suffixTime (u : Time) : C(Time,Time) where
  toFun t := ⟨(u:ℝ)+(1-(u:ℝ))*(t:ℝ), by
    constructor
    · nlinarith [u.property.1,u.property.2,t.property.1]
    · nlinarith [u.property.1,u.property.2,t.property.1,t.property.2]⟩
  continuous_toFun := (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PrefixMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def prefixMap (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (prefixTime u)

def suffixMap (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (suffixTime u) -
    (ContinuousLinearMap.const ℝ Time).comp (ContinuousMap.evalCLM ℝ u)

@[simp] lemma prefixMap_apply (u : Time) (f : C(Time,ℝ)) (t : Time) :
    prefixMap u f t = f (prefixTime u t) := rfl
@[simp] lemma suffixMap_apply (u : Time) (f : C(Time,ℝ)) (t : Time) :
    suffixMap u f t = f (suffixTime u t) - f u := rfl

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere

abbrev HilbertJet (N : ℕ) (L : Length) :=
  PiLp 2 (fun _ : Option (Direction N) ↦ ScalarL2 N L)

lemma scalarL2_norm_exponent : Fact (1 ≤ (2 : ℝ≥0∞)) := inferInstance

attribute [local instance] scalarL2_norm_exponent

abbrev scalarL2_normedAddCommGroup (N : ℕ) (L : Length) :
    NormedAddCommGroup (ScalarL2 N L) := inferInstance

attribute [local instance] scalarL2_normedAddCommGroup

abbrev scalarL2_addCommMonoid (N : ℕ) (L : Length) : AddCommMonoid (ScalarL2 N L) :=
  (scalarL2_normedAddCommGroup N L).toAddCommMonoid

abbrev scalarL2_innerProductSpace (N : ℕ) (L : Length) :
    InnerProductSpace ℂ (ScalarL2 N L) := inferInstance

attribute [local instance] scalarL2_innerProductSpace

abbrev scalarL2_module (N : ℕ) (L : Length) : Module ℂ (ScalarL2 N L) :=
  (scalarL2_innerProductSpace N L).toNormedSpace.toModule

attribute [local instance] scalarL2_module

lemma scalarL2_completeSpace (N : ℕ) (L : Length) : CompleteSpace (ScalarL2 N L) :=
  (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

end HardSphere
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma coordDerivative_add {N : ℕ} {L : Length} {a : ℝ}
    (f g : SmoothTest N L a) (p : Direction N) :
    coordDerivative N L (f.toFun + g.toFun) p =
      coordDerivative N L f.toFun p + coordDerivative N L g.toFun p := by
  funext X
  simp only [coordDerivative, Pi.add_apply]
  rw [fderiv_fun_add (f.smooth.differentiable (by simp)).differentiableAt
    (g.smooth.differentiable (by simp)).differentiableAt]
  rfl

lemma coordDerivative_smul {N : ℕ} {L : Length} {a : ℝ}
    (c : ℂ) (f : SmoothTest N L a) (p : Direction N) :
    coordDerivative N L (c • f.toFun) p = c • coordDerivative N L f.toFun p := by
  funext X
  simp only [coordDerivative, Pi.smul_apply]
  rw [fderiv_fun_const_smul (f.smooth.differentiable (by simp)).differentiableAt c]
  rfl

lemma coordDerivative_zero (N : ℕ) (L : Length) (p : Direction N) :
    coordDerivative N L 0 p = 0 := by
  funext X
  simp [coordDerivative]

def SmoothTest.zero (N : ℕ) (L : Length) (a : ℝ) : SmoothTest N L a where
  toFun := 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  support_allowed := by simp
  memLp := MemLp.zero
  partial_memLp := by
    intro p
    rw [coordDerivative_zero]
    exact MemLp.zero

def SmoothTest.add {N : ℕ} {L : Length} {a : ℝ}
    (f g : SmoothTest N L a) : SmoothTest N L a where
  toFun := f.toFun + g.toFun
  smooth := f.smooth.add g.smooth
  compact := f.compact.add g.compact
  support_allowed := (tsupport_add _ _).trans (union_subset f.support_allowed g.support_allowed)
  memLp := f.memLp.add g.memLp
  partial_memLp := by
    intro p
    rw [coordDerivative_add]
    exact (f.partial_memLp p).add (g.partial_memLp p)

def SmoothTest.smul {N : ℕ} {L : Length} {a : ℝ}
    (c : ℂ) (f : SmoothTest N L a) : SmoothTest N L a where
  toFun := c • f.toFun
  smooth := f.smooth.const_smul c
  compact := f.compact.smul_left
  support_allowed := (tsupport_smul_subset_right (fun _ ↦ c) f.toFun).trans f.support_allowed
  memLp := f.memLp.const_smul c
  partial_memLp := by
    intro p
    rw [coordDerivative_smul]
    exact (f.partial_memLp p).const_smul c

@[simp] lemma SmoothTest.jet_zero (N : ℕ) (L : Length) (a : ℝ) :
    (SmoothTest.zero N L a).jet = 0 := by
  apply Prod.ext
  · rfl
  · funext p
    change MemLp.toLp (coordDerivative N L 0 p) ((SmoothTest.zero N L a).partial_memLp p) = 0
    simp only [coordDerivative_zero, MemLp.toLp_zero]

@[simp] lemma SmoothTest.jet_add {N : ℕ} {L : Length} {a : ℝ}
    (f g : SmoothTest N L a) : (f.add g).jet = f.jet + g.jet := by
  apply Prod.ext
  · rfl
  · funext p
    change _ = (f.partial_memLp p).toLp _ + (g.partial_memLp p).toLp _
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr ((f.add g).partial_memLp p)
      ((f.partial_memLp p).add (g.partial_memLp p)) ?_
    exact Filter.Eventually.of_forall (congrFun (coordDerivative_add f g p))

@[simp] lemma SmoothTest.jet_smul {N : ℕ} {L : Length} {a : ℝ}
    (c : ℂ) (f : SmoothTest N L a) : (f.smul c).jet = c • f.jet := by
  apply Prod.ext
  · rfl
  · funext p
    change _ = c • (f.partial_memLp p).toLp _
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr ((f.smul c).partial_memLp p)
      ((f.partial_memLp p).const_smul c) ?_
    exact Filter.Eventually.of_forall (congrFun (coordDerivative_smul c f p))

def smoothGraph (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (Jet N L) where
  carrier := Set.range (SmoothTest.jet (N := N) (L := L) (a := a))
  zero_mem' := ⟨SmoothTest.zero N L a, SmoothTest.jet_zero N L a⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.add g, f.jet_add g⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact ⟨f.smul c, f.jet_smul c⟩

def dirichletSubmodule (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (Jet N L) :=
  (smoothGraph N L a).topologicalClosure

@[simp] lemma mem_dirichletSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ dirichletSubmodule N L a ↔ u ∈ dirichletDomain N L a := Iff.rfl

def permuteConfiguration {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (X : Configuration N L) : Configuration N L := fun i ↦ X (σ i)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

@[simp] lemma torusDistance_comm (L : Length) (x y : Torus L) :
    torusDistance L x y = torusDistance L y x := by
  simp only [torusDistance, dist_comm]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_HilbertJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

attribute [local instance] scalarL2_addCommMonoid scalarL2_module scalarL2_completeSpace

def optionJetEquiv (N : ℕ) (L : Length) :
    (Option (Direction N) → ScalarL2 N L) ≃L[ℂ] Jet N L where
  toLinearEquiv := LinearEquiv.piOptionEquivProd ℂ
  continuous_toFun := (continuous_apply none).prodMk
    (continuous_pi fun i ↦ continuous_apply (some i))
  continuous_invFun := continuous_pi fun i ↦ by
    cases i with
    | none => exact continuous_fst
    | some p => exact (continuous_apply p).comp continuous_snd

def hilbertJetEquiv (N : ℕ) (L : Length) : HilbertJet N L ≃L[ℂ] Jet N L :=
  (PiLp.continuousLinearEquiv _ ℂ _).trans (optionJetEquiv N L)

@[simp] lemma hilbertJetEquiv_fst {N : ℕ} {L : Length} (u : HilbertJet N L) :
    (hilbertJetEquiv N L u).1 = u.ofLp none := rfl
@[simp] lemma hilbertJetEquiv_snd {N : ℕ} {L : Length} (u : HilbertJet N L) (p : Direction N) :
    (hilbertJetEquiv N L u).2 p = u.ofLp (some p) := rfl

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

instance configurationBorel (N : ℕ) (L : Length) : BorelSpace (Configuration N L) := by
  unfold Configuration
  exact Pi.borelSpace

abbrev ConfigurationPath (N : ℕ) (L : Length) := C(Time, Configuration N L)
instance configurationPathMeasurable (N : ℕ) (L : Length) : MeasurableSpace (ConfigurationPath N L) := borel _
instance configurationPathBorel (N : ℕ) (L : Length) : BorelSpace (ConfigurationPath N L) := ⟨rfl⟩

def staysAllowed (N : ℕ) (L : Length) (a : ℝ) : Set (ConfigurationPath N L) :=
  {f | Set.range f ⊆ allowed N L a}

abbrev CoordinatePaths (N : ℕ) := Direction N → C(Time,ℝ)

def coordinateWiener (N : ℕ) : Measure (CoordinatePaths N) := Measure.pi (fun _ ↦ wiener)

def freeTrajectory (N : ℕ) (L : Length) (s : ℝ) (w : CoordinatePaths N)
    (X : Configuration N L) : ConfigurationPath N L :=
  ⟨fun t i j ↦ X i j + ((Real.sqrt (2*s) * w (i,j) t : ℝ) : AddCircle L.val), by
    continuity⟩

def freePathLaw (N : ℕ) (L : Length) (s : ℝ) : Measure (ConfigurationPath N L) :=
  ((coordinateWiener N).prod (volume : Measure (Configuration N L))).map
    (fun p ↦ freeTrajectory N L s p.1 p.2)

end HardSphere

namespace L2Multiplier
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def apply (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp u).mul hf).toLp (f * u)

lemma coe_apply (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    apply f hf u =ᵐ[μ] fun x ↦ f x * u x :=
  MemLp.coeFn_toLp _

def linearMap (f : α → ℂ) (hf : MemLp f ∞ μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := apply f hf
  map_add' u v := by
    apply Lp.ext
    filter_upwards [coe_apply f hf (u + v), coe_apply f hf u, coe_apply f hf v,
      Lp.coeFn_add u v, Lp.coeFn_add (apply f hf u) (apply f hf v)] with x huv hu hv h1 h2
    simp only [huv, h1, h2, Pi.add_apply, hu, hv, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [coe_apply f hf (c • u), coe_apply f hf u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (apply f hf u)] with x h1 h2 h3 h4
    simp only [h1, h3, h4, Pi.smul_apply, h2, smul_eq_mul, RingHom.id_apply]
    ring

lemma norm_apply_le (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    ‖apply f hf u‖ ≤ lpNorm f ∞ μ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_apply f hf u, ae_le_lpNorm_exponent_top hf] with x hx hfx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hfx (norm_nonneg _)

def clm (f : α → ℂ) (hf : MemLp f ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (linearMap f hf).mkContinuous (lpNorm f ∞ μ) (norm_apply_le f hf)

end L2Multiplier

namespace HardSphere
open Wiener
open scoped ComplexConjugate

abbrev FreePathL2 (N : ℕ) (L : Length) (t : ℝ) :=
  Lp ℂ 2 (freePathLaw N L t)

end HardSphere

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NormalizedPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

open Wiener

@[simp] lemma prefixTime_one (u : Time) : prefixTime u 1=u := by
  apply Subtype.ext
  simp [prefixTime]

@[simp] lemma prefixTime_zero (u : Time) : prefixTime u 0=0 := by
  apply Subtype.ext
  simp [prefixTime]

@[simp] lemma suffixTime_zero (u : Time) : suffixTime u 0=u := by
  apply Subtype.ext
  simp [suffixTime]

@[simp] lemma suffixTime_one (u : Time) : suffixTime u 1=1 := by
  apply Subtype.ext
  simp [suffixTime]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ReverseTime
attribute [-instance] _root_.OAI.HardSphere.configurationPathBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere.Wiener

def reverseTime : C(Time,Time) where
  toFun t := ⟨1-(t:ℝ), sub_nonneg.mpr t.property.2, by linarith [t.property.1]⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk _

@[simp] lemma reverseTime_reverse (t : Time) : reverseTime (reverseTime t) = t := by
  apply Subtype.ext
  change 1-(1-(t:ℝ)) = (t:ℝ)
  ring
@[simp] lemma reverseTime_zero : reverseTime 0 = 1 := by apply Subtype.ext; norm_num [reverseTime]
@[simp] lemma reverseTime_one : reverseTime 1 = 0 := by apply Subtype.ext; norm_num [reverseTime]

def reverseIncrements : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ reverseTime -
    (ContinuousLinearMap.const ℝ Time).comp (ContinuousMap.evalCLM ℝ 1)

@[simp] lemma reverseIncrements_apply (f : C(Time,ℝ)) (t : Time) :
    reverseIncrements f t = f (reverseTime t) - f 1 := rfl

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ReverseConfigurationPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

def reverseConfigurationPath (N : ℕ) (L : Length) (ω : ConfigurationPath N L) :
    ConfigurationPath N L := ω.comp reverseTime

@[simp] lemma reverseConfigurationPath_apply (N : ℕ) (L : Length)
    (ω : ConfigurationPath N L) (s : Time) :
    reverseConfigurationPath N L ω s = ω (reverseTime s) := rfl

@[simp] lemma reverseConfigurationPath_reverse (N : ℕ) (L : Length)
    (ω : ConfigurationPath N L) :
    reverseConfigurationPath N L (reverseConfigurationPath N L ω) = ω := by
  ext s i j
  simp only [reverseConfigurationPath_apply,reverseTime_reverse]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLine
attribute [-instance] _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
@[simp] lemma project_representative (N : ℕ) (L : Length) (X : Configuration N L) :
    project N L (representative N L X) = X := by
  funext i j
  exact AddCircle.coe_equivIco

@[simp] lemma project_add {N : ℕ} {L : Length} (X Y : LiftedConfiguration N) :
    project N L (X + Y) = project N L X + project N L Y := by
  funext i j
  exact map_add (QuotientAddGroup.mk' _) _ _

@[simp] lemma project_sub {N : ℕ} {L : Length} (X Y : LiftedConfiguration N) :
    project N L (X - Y) = project N L X - project N L Y := by
  funext i j
  exact map_sub (QuotientAddGroup.mk' _) _ _

lemma continuous_project (N : ℕ) (L : Length) : Continuous (project N L) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (AddCircle.continuous_mk' L.val).comp
    ((continuous_apply j).comp (continuous_apply i))

lemma isQuotientMap_project (N : ℕ) (L : Length) :
    Topology.IsQuotientMap (project N L) := by
  have hcircle : Function.Surjective (fun t : ℝ ↦ (t : AddCircle L.val)) := by
    intro x
    exact ⟨(AddCircle.equivIco L.val 0 x).val, AddCircle.coe_equivIco⟩
  have hopen : IsOpenMap (fun X : Fin 3 → ℝ ↦ fun j ↦ (X j : AddCircle L.val)) :=
    IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall (fun _ ↦ hcircle))
  have hsurj : Function.Surjective
      (fun X : Fin 3 → ℝ ↦ fun j ↦ (X j : AddCircle L.val)) := by
    intro X
    exact ⟨fun j ↦ (AddCircle.equivIco L.val 0 (X j)).val,
      funext (fun _ ↦ AddCircle.coe_equivIco)⟩
  exact (IsOpenMap.piMap (fun _ : Fin N ↦ hopen)
    (Filter.Eventually.of_forall (fun _ ↦ hsurj))).isQuotientMap
      (continuous_project N L) (fun X ↦ ⟨representative N L X, project_representative N L X⟩)

lemma continuous_of_continuous_lift {N : ℕ} {L : Length}
    {E : Type*} [TopologicalSpace E] {f : Configuration N L → E}
    (hf : Continuous (fun X : LiftedConfiguration N ↦ f (project N L X))) :
    Continuous f :=
  (isQuotientMap_project N L).continuous_iff.mpr hf

lemma fderiv_lift_eq {N : ℕ} {L : Length} (f : Configuration N L → ℂ)
    {X Y : LiftedConfiguration N} (hXY : project N L X = project N L Y) :
    fderiv ℝ (fun Z ↦ f (project N L Z)) X =
      fderiv ℝ (fun Z ↦ f (project N L Z)) Y := by
  have hfun : (fun Z ↦ f (project N L (Z + (X - Y)))) =
      (fun Z ↦ f (project N L Z)) := by
    funext Z
    rw [project_add, project_sub, hXY, sub_self, add_zero]
  have h := congrArg (fun g : LiftedConfiguration N → ℂ ↦ fderiv ℝ g Y) hfun
  have he := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun Z ↦ f (project N L Z)) (x := Y) (X - Y)
  rw [he] at h
  simpa only [show Y + (X - Y) = X by abel] using h

lemma coordDerivative_project {N : ℕ} {L : Length} (f : Configuration N L → ℂ)
    (p : Direction N) (X : LiftedConfiguration N) :
    coordDerivative N L f p (project N L X) =
      fderiv ℝ (fun Y ↦ f (project N L Y)) X
        (Pi.single p.1 (Pi.single p.2 1)) := by
  unfold coordDerivative
  rw [fderiv_lift_eq f (project_representative N L (project N L X))]

lemma continuous_coordDerivative {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X))) (p : Direction N) :
    Continuous (coordDerivative N L f p) := by
  apply continuous_of_continuous_lift
  simp_rw [coordDerivative_project]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

open scoped ComplexConjugate

lemma coordDerivative_mul {N : ℕ} {L : Length} {f g : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (hg : Differentiable ℝ (fun X : LiftedConfiguration N ↦ g (project N L X)))
    (p : Direction N) :
    coordDerivative N L (f * g) p = f * coordDerivative N L g p + g * coordDerivative N L f p := by
  funext X
  simp only [coordDerivative, Pi.mul_apply]
  rw [fderiv_fun_mul hf.differentiableAt hg.differentiableAt]
  simp only [add_apply, smul_apply,
    smul_eq_mul, project_representative, Pi.add_apply, Pi.mul_apply]
  rfl

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ChordLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff

variable (L : ℝ) [hL : Fact (0<L)]

def chordLift (x : ℝ) : ℝ := (L/Real.pi*Real.sin (Real.pi/L*x))^2

lemma chordLift_periodic : Function.Periodic (chordLift L) L := by
  intro x
  dsimp [chordLift]
  have h : Real.pi/L*(x+L)=Real.pi/L*x+Real.pi := by
    field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  rw [h,Real.sin_add_pi]
  ring

def chord (x : AddCircle L) : ℝ := (chordLift_periodic L).lift x

@[simp] lemma chord_coe (x : ℝ) : chord L (x : AddCircle L)=chordLift L x :=
  (chordLift_periodic L).lift_coe x

omit hL in
lemma chordLift_smooth : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (chordLift L) := by
  change ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : ℝ ↦ (L/Real.pi*Real.sin (Real.pi/L*x))^2)
  fun_prop

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ThreeTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

abbrev ThreeTorus := Fin 3 → AddCircle L

def pairQ (y x : ThreeTorus L) : ℝ := ∑ j : Fin 3, chord L (y j-x j)

def qLift (z : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, chordLift L (z j)

@[simp] lemma pairQ_coe (y x : Fin 3 → ℝ) :
    pairQ L (fun j ↦ (y j : AddCircle L)) (fun j ↦ (x j : AddCircle L))=qLift L (y-x) := by
  unfold pairQ qLift
  apply Finset.sum_congr rfl
  intro j _
  change chord L ((y j : AddCircle L)-(x j : AddCircle L))=chordLift L (y j-x j)
  have he : ((y j-x j : ℝ) : AddCircle L)=(y j : AddCircle L)-(x j : AddCircle L) :=
    map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples L)) _ _
  rw [← he,chord_coe]

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_FDerivIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace CompactParameterIntegral

variable {E A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {μ : Measure A} [IsFiniteMeasureOnCompacts μ]

lemma hasFDerivAt_integral {F : E × A → B}
    (hF : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) F) {K : Set A} (hK : IsCompact K) (y : E) :
    HasFDerivAt (fun z : E ↦ ∫ x in K, F (z,x) ∂μ)
      (∫ x in K, (fderiv ℝ F (y,x)).comp (ContinuousLinearMap.inl ℝ E A) ∂μ) y := by
  let D : E × A → E →L[ℝ] B := fun z ↦
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E A)
  have hD : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) D :=
    (hF.fderiv_right (by simp)).clm_comp contDiff_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall y 1).prod hK).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z x ↦ F (z,x)) (F' := fun z x ↦ D (z,x)) (μ := μ.restrict K)
    (bound := fun _ ↦ C) (s := Metric.closedBall y 1) (Metric.closedBall_mem_nhds _ (by norm_num))
    (Eventually.of_forall fun z ↦ (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (ContinuousOn.integrableOn_compact hK (hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn)
    (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro z hz
    exact hC (z,x) ⟨hz,hx⟩
  · exact Eventually.of_forall fun x z _ ↦ by
      have hh0 : HasFDerivAt (fun v : E ↦ (v,x)) (ContinuousLinearMap.inl ℝ E A) z :=
        (hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_const (𝕜 := ℝ) x z)
      exact ((hF.differentiable (by simp)) (z,x)).hasFDerivAt.comp z hh0

lemma contDiff_integral_nat (n : ℕ) {F : E × A → B}
    (hF : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) F) {K : Set A} (hK : IsCompact K) :
    ContDiff ℝ n (fun z : E ↦ ∫ x in K, F (z,x) ∂μ) := by
  induction n generalizing B with
  | zero =>
    exact contDiff_zero.mpr (show Differentiable ℝ (fun z : E ↦ ∫ x in K, F (z,x) ∂μ) from
      fun y ↦ (hasFDerivAt_integral hF hK y).differentiableAt).continuous
  | succ n ih =>
    rw [show ((n+1:ℕ):WithTop ℕ∞)=(n:WithTop ℕ∞)+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun y ↦ (hasFDerivAt_integral hF hK y).differentiableAt,by simp,?_⟩
    have hd : fderiv ℝ (fun z : E ↦ ∫ x in K, F (z,x) ∂μ)=
        fun z ↦ ∫ x in K, (fderiv ℝ F (z,x)).comp (ContinuousLinearMap.inl ℝ E A) ∂μ := by
      funext z
      exact (hasFDerivAt_integral hF hK z).fderiv
    rw [hd]
    exact ih ((hF.fderiv_right (by simp)).clm_comp contDiff_const)

lemma contDiff_integral {F : E × A → B}
    (hF : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) F) {K : Set A} (hK : IsCompact K) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun z : E ↦ ∫ x in K, F (z,x) ∂μ) :=
  contDiff_infty.mpr fun n ↦ contDiff_integral_nat n hF hK

end CompactParameterIntegral

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
structure SmoothMultiplier (N : ℕ) (L : Length) where
  toFun : Configuration N L → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ toFun (project N L X))
  memLp_top : MemLp toFun ∞ (volume : Measure (Configuration N L))
  partial_memLp_top : ∀ p : Direction N, MemLp (coordDerivative N L toFun p) ∞ volume

def SmoothMultiplier.mul {N : ℕ} {L : Length} (f g : SmoothMultiplier N L) :
    SmoothMultiplier N L where
  toFun := f.toFun * g.toFun
  smooth := f.smooth.mul g.smooth
  memLp_top := g.memLp_top.mul f.memLp_top
  partial_memLp_top := by
    intro p
    rw [coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp))]
    exact ((g.partial_memLp_top p).mul f.memLp_top).add
      ((f.partial_memLp_top p).mul g.memLp_top)

def SmoothMultiplier.onScalar {N : ℕ} {L : Length} (f : SmoothMultiplier N L) :
    ScalarL2 N L →L[ℂ] ScalarL2 N L := L2Multiplier.clm f.toFun f.memLp_top

def SmoothMultiplier.onJet {N : ℕ} {L : Length} (f : SmoothMultiplier N L) :
    Jet N L →L[ℂ] Jet N L :=
  (f.onScalar.comp (.fst ℂ _ _)).prod (.pi fun p ↦
    f.onScalar.comp ((ContinuousLinearMap.proj p).comp (ContinuousLinearMap.snd ℂ _ _)) +
    (L2Multiplier.clm _ (f.partial_memLp_top p)).comp (.fst ℂ _ _))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusLiftBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def SmoothMultiplier.ofSmooth {n : ℕ} {L : Length} (f : Configuration n L → ℂ)
    (hs : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun X : LiftedConfiguration n ↦ f (project n L X))) :
    SmoothMultiplier n L where
  toFun := f
  smooth := hs
  memLp_top := (continuous_of_continuous_lift hs.continuous).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  partial_memLp_top := fun p ↦ (continuous_coordDerivative hs p).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InnerClmRealRight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal

def SmoothMultiplier.derivativeScalar {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (p : Direction N) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  L2Multiplier.clm _ (f.partial_memLp_top p)

@[simp] lemma SmoothMultiplier.onJet_fst {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (u : Jet N L) : (f.onJet u).1 = f.onScalar u.1 := rfl

@[simp] lemma SmoothMultiplier.onJet_snd {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (u : Jet N L) (p : Direction N) :
    (f.onJet u).2 p = f.onScalar (u.2 p) + f.derivativeScalar p u.1 := rfl

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FinsetProd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def SmoothMultiplier.finsetProd {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (A : Finset S) (w : S → SmoothMultiplier n L) : SmoothMultiplier n L :=
  .ofSmooth (fun X ↦ ∏ s∈A, (w s).toFun X) (contDiff_prod fun s _ ↦ (w s).smooth)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HeadLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def SmoothMultiplier.orbital {L : Length} (w : SmoothMultiplier 1 L) (x : Torus L) : ℂ :=
  w.toFun (fun _ ↦ x)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LabelLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def labelLift (n : ℕ) (i : Fin n) : LiftedConfiguration n →L[ℝ] LiftedConfiguration 1 :=
  .pi fun _ ↦ .proj i

def SmoothMultiplier.liftLabel {L : Length} (w : SmoothMultiplier 1 L) (n : ℕ) (i : Fin n) :
    SmoothMultiplier n L := .ofSmooth (fun X ↦ w.orbital (X i)) (w.smooth.comp (labelLift n i).contDiff)

def SmoothMultiplier.sum {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) : SmoothMultiplier n L :=
  .ofSmooth (fun X ↦ ∑ s, (w s).toFun X) (ContDiff.sum fun s _ ↦ (w s).smooth)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RealComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def SmoothMultiplier.realComp {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ) : SmoothMultiplier n L :=
  .ofSmooth (fun X ↦ (φ (f.toFun X).re : ℂ))
    (Complex.ofRealCLM.contDiff.comp (hφ.comp (Complex.reCLM.contDiff.comp f.smooth)))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Near
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory

namespace HardSphere.TightCutoff
open PeriodicCutoff
noncomputable section
variable (L : ℝ) [hL : Fact (0<L)]

def angle (r : ℝ) (y x : ThreeTorus L) : ℝ :=
  Real.pi/2*Real.smoothTransition ((pairQ L y x-(5/4)*r^2)/((1/4)*r^2))

def angleLift (r : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.pi/2*Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2))

omit hL in
lemma angleLift_smooth (r : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (angleLift L r) := by
  have hq : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (qLift L) := by
    apply ContDiff.sum
    intro j _
    exact (chordLift_smooth L).comp (contDiff_apply ℝ ℝ j)
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((hq.sub contDiff_const).div_const _))

end
end HardSphere.TightCutoff

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Bump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def bump (L : Length) (δ : ℝ) (x y : Torus L) : ℝ :=
  Real.cos (TightCutoff.angle L.val δ y x)

def centerLift (L : Length) (x : Torus L) : Fin 3 → ℝ :=
  fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val

lemma centerLift_coe (L : Length) (x : Torus L) :
    (fun j ↦ (centerLift L x j : AddCircle L.val))=x := by
  ext j
  exact AddCircle.coe_equivIco

lemma bump_project (L : Length) (δ : ℝ) (x : Torus L) (R : LiftedConfiguration 1) :
    bump L δ x (project 1 L R 0)=
      Real.cos (TightCutoff.angleLift L.val δ (R 0-centerLift L x)) := by
  unfold bump TightCutoff.angle TightCutoff.angleLift
  change Real.cos (Real.pi / 2 * Real.smoothTransition
    ((pairQ L.val (fun j ↦ (R 0 j : AddCircle L.val)) x-(5/4)*δ^2)/((1/4)*δ^2))) = _
  conv_lhs => rw [← centerLift_coe L x, pairQ_coe]

lemma bump_smooth (L : Length) (δ : ℝ) (x : Torus L) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun R : LiftedConfiguration 1 ↦ (bump L δ x (project 1 L R 0) : ℂ)) := by
  simp_rw [bump_project]
  exact Complex.ofRealCLM.contDiff.comp ((Real.contDiff_cos.comp
    (TightCutoff.angleLift_smooth L.val δ)).comp ((contDiff_apply ℝ (Fin 3 → ℝ) 0).sub contDiff_const))

def raw (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier 1 L :=
  .ofSmooth (fun X ↦ (bump L δ x (X 0) : ℂ)) (bump_smooth L δ x)

def mass (L : Length) (δ : ℝ) (x : Torus L) : ℝ := ∫ y : Torus L, (bump L δ x y)^2

def normalized (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier 1 L :=
  .ofSmooth (fun X ↦ (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(raw L δ x).toFun X)
    (contDiff_const.mul (raw L δ x).smooth)

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def chi (L : Length) (δ : ℝ) (x y : Torus L) : ℝ := bump L (8*δ) x y ^ 2

def count {n : ℕ} (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) : ℝ :=
  ∑ i, chi L δ x (X i)

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def chiOne (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier 1 L :=
  (raw L (8*δ) x).mul (raw L (8*δ) x)

def countMultiplier (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier n L :=
  SmoothMultiplier.sum (fun i : Fin n ↦ (chiOne L δ x).liftLabel n i)

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def profile (h t : ℝ) : ℝ := 1-Real.smoothTransition (t/h-1)

lemma profile_smooth (h : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (profile h) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const h).sub contDiff_const))

def cutoff (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ) : SmoothMultiplier n L :=
  (countMultiplier n L δ x).realComp (profile h) (profile_smooth h)

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

abbrev EuclideanTorus (L : Length) := PiLp 2 (fun _ : Fin 3 ↦ AddCircle L.val)

def euclideanTorusPoint (L : Length) (x : Torus L) : EuclideanTorus L := WithLp.toLp 2 x

def spatialSiteDistance (L : Length) (A : Finset (Torus L)) (x : Torus L) : ℝ :=
  Metric.infDist (euclideanTorusPoint L x) (euclideanTorusPoint L '' (A:Set (Torus L)))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CenteredCircleLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma otherLabels_nonempty (i : ι) : (Finset.univ.erase i).Nonempty := by
  obtain ⟨j,hj⟩ := exists_ne i
  exact ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩⟩

lemma nearestLabel_exists (L : Length) (X : ι→Torus L) (i : ι) :
    ∃ j : ι, j≠i ∧ ∀ k : ι, k≠i → torusDistance L (X i) (X j)≤torusDistance L (X i) (X k) := by
  obtain ⟨j,hj,hm⟩ := (Finset.univ.erase i).exists_min_image
    (fun j ↦ torusDistance L (X i) (X j)) (otherLabels_nonempty i)
  exact ⟨j,(Finset.mem_erase.mp hj).1,fun k hk ↦ hm k (Finset.mem_erase.mpr ⟨hk,Finset.mem_univ _⟩)⟩

def nearestLabel (L : Length) (X : ι→Torus L) (i : ι) : ι :=
  Classical.choose (nearestLabel_exists L X i)

def nearestParticleDistance (L : Length) (X : ι→Torus L) (i : ι) : ℝ :=
  torusDistance L (X i) (X (nearestLabel L X i))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InjectiveNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma torusDistance_continuous_pair (L : Length) :
    Continuous (fun p : Torus L×Torus L ↦ torusDistance L p.1 p.2) := by
  unfold torusDistance
  fun_prop

attribute [local irreducible] torusDistance nearestParticleDistance

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathDiameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def intervalTime (a b s : Time) : Time :=
  ⟨(1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) a.property.1) (mul_nonneg s.property.1 b.property.1)
    · nlinarith [a.property.1,a.property.2,b.property.1,b.property.2,
        s.property.1,s.property.2,mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr a.property.2),
        mul_nonneg s.property.1 (sub_nonneg.mpr b.property.2)]⟩

lemma intervalTime_continuous (a b : Time) : Continuous (intervalTime a b) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] lemma intervalTime_zero (a b : Time) : intervalTime a b 0=a := by
  apply Subtype.ext
  simp [intervalTime]
@[simp] lemma intervalTime_one (a b : Time) : intervalTime a b 1=b := by
  apply Subtype.ext
  simp [intervalTime]

def diameterMap {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) : C(Time×Time,ℝ) :=
  ⟨fun p ↦ torusDistance L (ω (intervalTime a b p.1) 0) (ω (intervalTime a b p.2) 0), by
    apply (torusDistance_continuous_pair L).comp (f := fun p : Time×Time ↦ (ω (intervalTime a b p.1) 0,ω (intervalTime a b p.2) 0))
    exact ((continuous_apply 0).comp (ω.continuous.comp ((intervalTime_continuous a b).comp continuous_fst))).prodMk
      ((continuous_apply 0).comp (ω.continuous.comp ((intervalTime_continuous a b).comp continuous_snd)))⟩

def intervalDiameter {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) : ℝ :=
  ‖diameterMap a b ω‖

lemma diameterMap_continuous (L : Length) (a b : Time) : Continuous (diameterMap (L:=L) a b) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath 1 L × (Time×Time) ↦
    torusDistance L (p.1 (intervalTime a b p.2.1) 0) (p.1 (intervalTime a b p.2.2) 0))
  apply (torusDistance_continuous_pair L).comp (f := fun p : ConfigurationPath 1 L×(Time×Time) ↦ (p.1 (intervalTime a b p.2.1) 0,p.1 (intervalTime a b p.2.2) 0))
  apply Continuous.prodMk
  · exact (continuous_apply 0).comp (continuous_fst.eval ((intervalTime_continuous a b).comp (continuous_fst.comp continuous_snd)))
  · exact (continuous_apply 0).comp (continuous_fst.eval ((intervalTime_continuous a b).comp (continuous_snd.comp continuous_snd)))

lemma intervalDiameter_continuous (L : Length) (a b : Time) :
    Continuous (intervalDiameter (L:=L) a b) := (diameterMap_continuous L a b).norm

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def meshTime {m : ℕ} (j : Fin m) (s : Time) : Time :=
  ⟨((j:ℝ)+(s:ℝ))/(m:ℝ), by
    have hm : (0:ℝ) < m := by exact_mod_cast j.pos
    refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) s.property.1) hm.le,(div_le_one hm).mpr ?_⟩
    have hj : (j:ℝ)+1≤(m:ℝ) := by exact_mod_cast j.isLt
    linarith [s.property.2]⟩

lemma meshTime_continuous {m : ℕ} (j : Fin m) : Continuous (meshTime j) := by
  apply Continuous.subtype_mk
  fun_prop

def meshSegment {m : ℕ} {L : Length} (j : Fin m) (ω : ConfigurationPath 1 L) : ConfigurationPath 1 L :=
  ⟨fun s ↦ ω (meshTime j s),ω.continuous.comp (meshTime_continuous j)⟩

lemma meshSegment_continuous {m : ℕ} (L : Length) (j : Fin m) :
    Continuous (meshSegment (L:=L) j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath 1 L×Time ↦ p.1 (meshTime j p.2))
  exact continuous_fst.eval ((meshTime_continuous j).comp continuous_snd)

@[simp] lemma meshSegment_one {L : Length} (ω : ConfigurationPath 1 L) :
    meshSegment (0:Fin 1) ω=ω := by
  apply ContinuousMap.ext
  intro s
  change ω (meshTime (0:Fin 1) s)=ω s
  congr 1
  apply Subtype.ext
  simp [meshTime]

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Fourier_ArgumentAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere.FreeFourier
lemma argument_add (L : ℝ) (n : ℤ) (x y : AddCircle L) :
    fourier n (x+y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

end HardSphere.FreeFourier

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def meshProduct {L : Length} (m : ℕ) (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :=
  ∏ j : Fin m, F (meshSegment j ω)

@[simp] lemma meshProduct_one {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :
    meshProduct 1 F ω=F ω := by simp [meshProduct]

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def meshSum {L : Length} (m : ℕ) (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :=
  ∑ j : Fin m, F (meshSegment j ω)

@[simp] lemma meshSum_one {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :
    meshSum 1 F ω=F ω := by simp [meshSum]

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_WienerStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener

@[simp] lemma freeTrajectory_zero (N : ℕ) (L : Length)
    (w : CoordinatePaths N) (X : Configuration N L) :
    freeTrajectory N L 0 w X=ContinuousMap.const Time X := by
  ext t i j
  simp [freeTrajectory]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Regularize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace ComplexRegularization

def regularize (ε : ℝ) (z : ℂ) : ℂ := (Real.sqrt (‖z‖ ^ 2 + ε ^ 2) - ε : ℝ)

def differential (ε : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (Real.sqrt (‖z‖ ^ 2 + ε ^ 2))⁻¹ • (Complex.ofRealCLM.comp (innerSL ℝ z))

lemma smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (regularize ε) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sqrt ((contDiff_norm_sq ℝ).add contDiff_const)
  intro z
  positivity

lemma zero {ε : ℝ} (hε : 0 ≤ ε) : regularize ε 0 = 0 := by
  simp [regularize, Real.sqrt_sq hε]

lemma hasFDerivAt {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    HasFDerivAt (regularize ε) (differential ε z) z := by
  have hn : ‖z‖ ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).sqrt hn).sub_const ε)
  have hd : differential ε z = Complex.ofRealCLM.comp
      ((1 / (2 * Real.sqrt (‖z‖ ^ 2 + ε ^ 2))) • (2 • innerSL ℝ z)) := by
    ext w
    simp [differential, two_smul, div_eq_mul_inv, mul_inv_rev]
    ring

  rw [hd]
  exact h

lemma sqroot_ge_norm (ε : ℝ) (z : ℂ) : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + ε ^ 2) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ε])

lemma differential_apply_le (ε : ℝ) (z w : ℂ) :
    ‖differential ε z w‖ ≤ ‖w‖ := by
  by_cases hz : z = 0
  · simp [hz, differential]
  have hp : 0 < Real.sqrt (‖z‖ ^ 2 + ε ^ 2) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (sqroot_ge_norm ε z)
  simp only [differential, smul_apply, ContinuousLinearMap.comp_apply,
    norm_smul, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos hp, innerSL_apply_apply]
  change _ * ‖inner ℝ z w‖ ≤ _
  apply le_trans (mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) z w) (by positivity :
    0 ≤ (Real.sqrt (‖z‖ ^ 2 + ε ^ 2))⁻¹))
  rw [← div_eq_inv_mul, div_le_iff₀ hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (sqroot_ge_norm ε z) (norm_nonneg w)

lemma differential_le (ε : ℝ) (z : ℂ) : ‖differential ε z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simpa only [one_mul] using differential_apply_le ε z w

lemma fderiv_eq {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    fderiv ℝ (regularize ε) z = differential ε z := (hasFDerivAt hε z).fderiv

lemma tendsto_differential (z : ℂ) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ differential (e n) z) atTop (𝓝 (differential 0 z)) := by
  by_cases hz : z = 0
  · simp only [hz, differential, map_zero, ContinuousLinearMap.comp_zero, smul_zero]
    exact tendsto_const_nhds
  have hp : Real.sqrt (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
    simp [Real.sqrt_sq (norm_nonneg z), hz]
  exact (((tendsto_const_nhds.add (he.pow 2)).sqrt.inv₀ hp).smul tendsto_const_nhds)

end ComplexRegularization

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Joint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def joint {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L) (h : ℝ) (A : Finset S) :
    SmoothMultiplier n L := SmoothMultiplier.finsetProd A (fun s ↦ cutoff n L (1/100) (c s) h)

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_JoinConfiguration
attribute [-instance] _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

def joinConfiguration (m n : ℕ) (L : Length)
    (p : Configuration m L × Configuration n L) : Configuration (m+n) L :=
  Fin.addCases p.1 p.2

def splitConfiguration (m n : ℕ) (L : Length) (X : Configuration (m+n) L) :
    Configuration m L × Configuration n L :=
  (fun i ↦ X (Fin.castAdd n i),fun i ↦ X (Fin.natAdd m i))

lemma joinConfiguration_continuous (m n : ℕ) (L : Length) :
    Continuous (joinConfiguration m n L) := by
  apply continuous_pi
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [joinConfiguration,Fin.addCases_left,Function.comp_def] using
      ((continuous_apply i).comp continuous_fst)
  | right i => simpa only [joinConfiguration,Fin.addCases_right,Function.comp_def] using
      ((continuous_apply i).comp continuous_snd)

@[simp] lemma split_joinConfiguration (m n : ℕ) (L : Length)
    (p : Configuration m L × Configuration n L) :
    splitConfiguration m n L (joinConfiguration m n L p)=p := by
  ext <;> simp [splitConfiguration,joinConfiguration]

@[simp] lemma join_splitConfiguration (m n : ℕ) (L : Length) (X : Configuration (m+n) L) :
    joinConfiguration m n L (splitConfiguration m n L X)=X := by
  ext i j
  induction i using Fin.addCases <;> simp [splitConfiguration,joinConfiguration]

def joinConfigurationPath (m n : ℕ) (L : Length)
    (p : ConfigurationPath m L × ConfigurationPath n L) : ConfigurationPath (m+n) L :=
  ⟨fun t ↦ joinConfiguration m n L (p.1 t,p.2 t),
    (joinConfiguration_continuous m n L).comp (p.1.continuous.prodMk p.2.continuous)⟩

def splitConfigurationPath (m n : ℕ) (L : Length) (ω : ConfigurationPath (m+n) L) :
    ConfigurationPath m L × ConfigurationPath n L :=
  (⟨fun t i ↦ ω t (Fin.castAdd n i),by fun_prop⟩,
   ⟨fun t i ↦ ω t (Fin.natAdd m i),by fun_prop⟩)

@[simp] lemma split_joinConfigurationPath (m n : ℕ) (L : Length)
    (p : ConfigurationPath m L × ConfigurationPath n L) :
    splitConfigurationPath m n L (joinConfigurationPath m n L p)=p := by
  ext <;> simp [splitConfigurationPath,joinConfigurationPath,joinConfiguration]

@[simp] lemma join_splitConfigurationPath (m n : ℕ) (L : Length)
    (ω : ConfigurationPath (m+n) L) :
    joinConfigurationPath m n L (splitConfigurationPath m n L ω)=ω := by
  apply ContinuousMap.ext
  intro t
  exact join_splitConfiguration m n L (ω t)

end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_FreePathLawFiniteDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

@[simp] lemma joinConfigurationPath_apply (m n : ℕ) (L : Length)
    (p : ConfigurationPath m L × ConfigurationPath n L) (t : Time) :
    joinConfigurationPath m n L p t=joinConfiguration m n L (p.1 t,p.2 t) := rfl

end
end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FreePathExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

def oneConfiguration {L : Length} (y : Torus L) : Configuration 1 L := fun _ ↦ y

def onePathAt {n : ℕ} {L : Length} (i : Fin n) (ω : ConfigurationPath n L) : ConfigurationPath 1 L :=
  ⟨fun s ↦ oneConfiguration (ω s i), by unfold oneConfiguration; fun_prop⟩

@[simp] lemma onePathAt_reverse {n : ℕ} {L : Length} (i : Fin n) (ω : ConfigurationPath n L) :
    onePathAt i (reverseConfigurationPath n L ω)=reverseConfigurationPath 1 L (onePathAt i ω) := rfl

@[simp] lemma onePathAt_single {L : Length} (ω : ConfigurationPath 1 L) : onePathAt 0 ω=ω := by
  ext s i j
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rfl

@[simp] lemma onePathAt_join_left {m n : ℕ} {L : Length} (i : Fin m)
    (p : ConfigurationPath m L × ConfigurationPath n L) :
    onePathAt (Fin.castAdd n i) (joinConfigurationPath m n L p)=onePathAt i p.1 := by
  ext s j k
  simp [onePathAt,oneConfiguration,joinConfigurationPath,joinConfiguration]

@[simp] lemma onePathAt_join_right {m n : ℕ} {L : Length} (i : Fin n)
    (p : ConfigurationPath m L × ConfigurationPath n L) :
    onePathAt (Fin.natAdd m i) (joinConfigurationPath m n L p)=onePathAt i p.2 := by
  ext s j k
  simp [onePathAt,oneConfiguration,joinConfigurationPath,joinConfiguration]

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CubeCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open scoped BigOperators

abbrev CubeCell (K : ℕ) := Fin K × Fin K × Fin K

end HardSphere

end
end
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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HalfShiftCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere.GridGeometry

lemma floor_grid_periodic {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l) (b : ℝ) :
    Function.Periodic (fun x : ℝ ↦ (⌊(x-b)/l⌋ : ZMod j)) L := by
  intro x
  have he : (x+L-b)/l=(x-b)/l+(j:ℝ) := by rw [hL]; field_simp; ring
  change (⌊(x+L-b)/l⌋ : ZMod j)=(⌊(x-b)/l⌋ : ZMod j)
  rw [he,Int.floor_add_natCast,Int.cast_add]
  simp

noncomputable def index {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l) (b : ℝ) :
    AddCircle L → ZMod j := (floor_grid_periodic hl hL b).lift

end HardSphere.GridGeometry

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedUnitCellPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open scoped BigOperators

noncomputable def unitIndex {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) : Fin K :=
  ⟨⌊((AddCircle.equivIco L.val 0) x).val⌋₊, by
    apply (Nat.floor_lt (by simpa only [zero_add] using ((AddCircle.equivIco L.val 0) x).property.1)).mpr
    simpa only [zero_add,hL] using ((AddCircle.equivIco L.val 0) x).property.2⟩

lemma measurable_unitIndex {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) :
    Measurable (unitIndex hL) := by
  apply measurable_to_countable'
  intro v
  have hm := (measurable_subtype_coe.comp (AddCircle.measurableEquivIco L.val 0).measurable).nat_floor
  have he : unitIndex hL ⁻¹' {v}=(fun x ↦ ⌊((AddCircle.equivIco L.val 0) x).val⌋₊) ⁻¹' {v.val} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,unitIndex]
  rw [he]
  exact hm (measurableSet_singleton _)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SqTwiceSqAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

abbrev EuclideanConfiguration (ι : Type*) := EuclideanSpace ℝ (ι×Fin 3)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCloseLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

variable {n : ℕ} [Nontrivial (Fin n)]

def localCloseLabels (L : Length) (s : ℝ) (v : Torus L) (X : Configuration n L) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ torusDistance L (X i) v≤5 ∧ nearestParticleDistance L X i ≤ s)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PairCloseLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def pairCloseLabels {m : ℕ} (L : Length) (s : ℝ) (v : Torus L)
    (Y : Configuration m L) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i ↦ torusDistance L (Y i) v≤5 ∧
    ∃ j, j≠i ∧ torusDistance L (Y i) (Y j)≤ s)

attribute [local irreducible] torusDistance nearestParticleDistance

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BadGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def badGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj x y := x∈B ∧ y∈B ∧ G.Adj x y
  symm := ⟨by intro x y h; exact ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.2.2⟩

def badComponent (G : SimpleGraph V) (B : Finset V) (x : V) : Finset V :=
  B.filter (fun y ↦ (badGraph G B).Reachable x y)

def badComponents (G : SimpleGraph V) (B : Finset V) : Finset (Finset V) :=
  B.image (badComponent G B)

lemma mem_badComponent (G : SimpleGraph V) (B : Finset V) (x y : V) :
    y∈badComponent G B x ↔ y∈B ∧ (badGraph G B).Reachable x y :=
  Finset.mem_filter

lemma mem_own_badComponent (G : SimpleGraph V) (B : Finset V) {x : V} (hx : x∈B) :
    x∈badComponent G B x := (mem_badComponent G B x x).mpr ⟨hx,.refl x⟩

lemma badComponent_subset (G : SimpleGraph V) (B : Finset V) (x : V) :
    badComponent G B x ⊆ B := Finset.filter_subset _ _

lemma reachable_inside_component (G : SimpleGraph V) (B : Finset V) {x y : V}
    (hy : (badGraph G B).Reachable x y) :
    (badGraph G (badComponent G B x)).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy ⊢
  induction hy with
  | refl => exact .refl
  | @tail y z hxy hyz ih =>
    apply ih.tail
    have hreach : (badGraph G B).Reachable x y :=
      (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hxy
    refine ⟨(mem_badComponent G B x y).mpr ⟨hyz.1,hreach⟩,
      (mem_badComponent G B x z).mpr ⟨hyz.2.1,hreach.trans hyz.reachable⟩,hyz.2.2⟩

abbrev ExploreState (V : Type u) := Finset V × Finset V

def rootedAnimals (G : SimpleGraph V) (r : V) (m : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun F ↦ r∈F ∧ F.card=m ∧ ∀ y∈F, (badGraph G F).Reachable r y)

end HardSphere.Lattice
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice
abbrev Vertex := Fin 3 → ℤ

def step (x : Vertex) (i : Fin 3) : Vertex := Function.update x i (x i+1)

lemma step_apply_same (x : Vertex) (i : Fin 3) : step x i i=x i+1 := by
  simp [step]
lemma step_apply_ne (x : Vertex) {i j : Fin 3} (h : j≠i) : step x i j=x j := by
  simp [step,h]
lemma step_comm (x : Vertex) (i j : Fin 3) : step (step x i) j=step (step x j) i := by
  ext k
  by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [step,Function.update_apply]

variable {A : Type*} [AddCommGroup A]

def cubicalPotential (f : Fin 3 → Vertex → A) (l : ℤ) (x : Vertex) : A :=
  ∑ k∈Finset.range (x 0-l).toNat, f 0 (Function.update x 0 (l+(k:ℤ)))

lemma update_step_zero (x : Vertex) (k : ℤ) :
    Function.update (step x 0) 0 k=Function.update x 0 k := by simp [step]
lemma step_update_zero (x : Vertex) (k : ℤ) :
    step (Function.update x 0 k) 0=Function.update x 0 (k+1) := by simp [step]
lemma update_step_other (x : Vertex) (k : ℤ) {j : Fin 3} (hj : j≠0) :
    Function.update (step x j) 0 k=step (Function.update x 0 k) j := by
  ext i
  by_cases hi : i=0 <;> by_cases hij : i=j <;> simp_all [step,Function.update_apply]

theorem cubicalPotential_step (f : Fin 3 → Vertex → A) (l : ℤ)
    (hl : ∀ i x, x 0≤l → f i x=0)
    (hsq : ∀ i j x, f i x+f j (step x i)=f j x+f i (step x j))
    (x : Vertex) (i : Fin 3) :
    cubicalPotential f l (step x i)-cubicalPotential f l x=f i x := by
  by_cases hi : i=0
  · subst i
    by_cases hx : l≤x 0
    · have hn : (step x 0 0-l).toNat=(x 0-l).toNat+1 := by
        rw [step_apply_same]
        omega
      simp only [cubicalPotential,hn,update_step_zero,Finset.sum_range_succ]
      have hcast : l+((x 0-l).toNat:ℤ)=x 0 := by omega
      rw [hcast,Function.update_eq_self]
      abel
    · have hx' : x 0≤l := by omega
      have hlen : (x 0-l).toNat=0 := by omega
      have hlen' : (step x 0 0-l).toNat=0 := by rw [step_apply_same]; omega
      simp [cubicalPotential,hlen,hlen',hl 0 x hx']
  · have hi0 : 0≠i := Ne.symm hi
    by_cases hx : l≤x 0
    · have hbase : f i (Function.update x 0 l)=0 := hl i _ (by simp)
      have hcast : l+((x 0-l).toNat:ℤ)=x 0 := by omega
      simp only [cubicalPotential,step_apply_ne x hi0,← Finset.sum_sub_distrib]
      calc
        _ = ∑ k∈Finset.range (x 0-l).toNat,
            (f i (Function.update x 0 (l+((k+1:ℕ):ℤ)))-
             f i (Function.update x 0 (l+(k:ℤ)))) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [update_step_other x _ hi]
          have h := hsq 0 i (Function.update x 0 (l+(k:ℤ)))
          rw [step_update_zero] at h
          simp only [Nat.cast_add,Nat.cast_one]
          rw [show l+((k:ℤ)+1)=l+(k:ℤ)+1 by omega]
          exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h.symm)
        _ = f i (Function.update x 0 (l+((x 0-l).toNat:ℤ)))-
            f i (Function.update x 0 (l+(0:ℤ))) := by
          exact Finset.sum_range_sub (fun k : ℕ ↦ f i (Function.update x 0 (l+(k:ℤ)))) _
        _ = f i x := by rw [hcast,add_zero,Function.update_eq_self,hbase,sub_zero]
    · have hlen : (x 0-l).toNat=0 := by omega
      have hx' : x 0≤l := by omega
      simp [cubicalPotential,step_apply_ne x hi0,hlen,hl i x hx']

def nearestStep (x y : Vertex) : Prop :=
  ∃ i : Fin 3, |x i-y i|=1 ∧ ∀ j, j≠i → x j=y j

def starStep (x y : Vertex) : Prop := x≠y ∧ ∀ i, |x i-y i|≤1

lemma nearestStep_symm {x y : Vertex} (h : nearestStep x y) : nearestStep y x := by
  obtain ⟨i,hi,hrest⟩ := h
  exact ⟨i,by simpa only [abs_sub_comm] using hi,fun j hj ↦ (hrest j hj).symm⟩
lemma nearestStep_step (x : Vertex) (i : Fin 3) : nearestStep x (step x i) := by
  refine ⟨i,?_,fun j hj ↦ (step_apply_ne x hj).symm⟩
  rw [step_apply_same]
  norm_num
lemma nearestStep_eq_step {x y : Vertex} (h : nearestStep x y) :
    ∃ i, y=step x i ∨ x=step y i := by
  obtain ⟨i,hi,hrest⟩ := h
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hi with hp|hm
  · refine ⟨i,Or.inr ?_⟩
    ext j
    by_cases hj : j=i
    · subst j; rw [step_apply_same]; omega
    · rw [step_apply_ne y hj]; exact hrest j hj
  · refine ⟨i,Or.inl ?_⟩
    ext j
    by_cases hj : j=i
    · subst j; rw [step_apply_same]; omega
    · rw [step_apply_ne x hj]; exact (hrest j hj).symm

def withinReach (e : Vertex → Vertex → Prop) (D : Set Vertex) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (fun u v ↦ u∈D ∧ v∈D ∧ e u v) x y

def NNConnected (D : Set Vertex) : Prop :=
  ∀ x∈D, ∀ y∈D, withinReach nearestStep D x y

def starConnected (D : Set Vertex) : Prop :=
  ∀ x∈D, ∀ y∈D, withinReach starStep D x y

def NNComplementComponent (A B : Set Vertex) : Prop :=
  Disjoint A B ∧ NNConnected B ∧
    ∀ x∈B, ∀ y, y∉A → nearestStep x y → y∈B

def nnBoundary (A B : Set Vertex) : Set Vertex :=
  {x | x∈B ∧ ∃ a∈A, nearestStep a x}

lemma boundary_of_cross {A B : Set Vertex} (hB : NNComplementComponent A B)
    {x y : Vertex} (hx : x∈B) (hy : y∉B) (hxy : nearestStep x y) :
    x∈nnBoundary A B := by
  refine ⟨hx,y,?_,nearestStep_symm hxy⟩
  by_contra hya
  exact hy (hB.2.2 x hx y hya hxy)

def unitCube (x : Vertex) : Set Vertex := {y | ∀ i, x i≤y i ∧ y i≤x i+1}

lemma unitCube_self (x : Vertex) : x∈unitCube x := by intro i; omega
lemma unitCube_step (x : Vertex) (i : Fin 3) : step x i∈unitCube x := by
  intro j
  by_cases hj : j=i
  · subst j; rw [step_apply_same]; omega
  · rw [step_apply_ne x hj]; omega
lemma unitCube_step_step (x : Vertex) {i j : Fin 3} (hij : i≠j) :
    step (step x i) j∈unitCube x := by
  intro k
  by_cases hk : k=i
  · subst k
    rw [step_apply_ne _ hij,step_apply_same]
    omega
  · by_cases hkj : k=j
    · subst k
      rw [step_apply_same,step_apply_ne _ hk]
      omega
    · rw [step_apply_ne _ hkj,step_apply_ne _ hk]; omega

lemma unitCube_star {x y z : Vertex} (hy : y∈unitCube x) (hz : z∈unitCube x)
    (hyz : y≠z) : starStep y z := by
  refine ⟨hyz,fun i ↦ abs_le.mpr ?_⟩
  have h := hy i
  have h' := hz i
  constructor <;> omega

def edgeLabel (B S : Set Vertex) (x y : Vertex) : ZMod 2 :=
  (if x∈S then 1 else 0)*(1-if y∈B then 1 else 0)+
  (if y∈S then 1 else 0)*(1-if x∈B then 1 else 0)

def cubeFlag (S : Set Vertex) (x : Vertex) : ZMod 2 :=
  if ∃ y∈S, y∈unitCube x then 1 else 0

def indicatorTwo (B : Set Vertex) (x : Vertex) : ZMod 2 := if x∈B then 1 else 0

lemma edgeLabel_symm (B S : Set Vertex) (x y : Vertex) :
    edgeLabel B S x y=edgeLabel B S y x := by unfold edgeLabel; ring

lemma edgeLabel_zero_of_same {B S : Set Vertex} (hSB : S⊆B) {x y : Vertex}
    (hxy : x∈B ↔ y∈B) : edgeLabel B S x y=0 := by
  by_cases hx : x∈B
  · simp [edgeLabel,hx,hxy.mp hx]
  · have hy : y∉B := fun h ↦ hx (hxy.mpr h)
    have hsx : x∉S := fun h ↦ hx (hSB h)
    have hsy : y∉S := fun h ↦ hy (hSB h)
    simp [edgeLabel,hsx,hsy]

lemma cubeFlag_eq {A B S : Set Vertex} (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) {x y : Vertex}
    (hy : y∈nnBoundary A B) (hyc : y∈unitCube x) :
    cubeFlag S x=indicatorTwo S y := by
  by_cases hys : y∈S
  · simp [cubeFlag,indicatorTwo,hys,show ∃ z∈S,z∈unitCube x from ⟨y,hys,hyc⟩]
  · have he : ¬∃ z∈S,z∈unitCube x := by
      rintro ⟨z,hzs,hzc⟩
      by_cases hzy : z=y
      · exact hys (hzy ▸ hzs)
      · exact hys ((hcoh z (hS hzs) y hy (unitCube_star hzc hyc hzy)).mp hzs)
    simp [cubeFlag,indicatorTwo,hys,he]

lemma edgeLabel_unitCube {A B S : Set Vertex} (hB : NNComplementComponent A B)
    (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) {x u v : Vertex}
    (hu : u∈unitCube x) (hv : v∈unitCube x) (huv : nearestStep u v) :
    edgeLabel B S u v=cubeFlag S x*(indicatorTwo B v-indicatorTwo B u) := by
  have hSB : S⊆B := fun _ hz ↦ (hS hz).1
  by_cases hub : u∈B <;> by_cases hvb : v∈B
  · simp [edgeLabel,indicatorTwo,hub,hvb]
  · have hsv : v∉S := fun h ↦ hvb (hSB h)
    have hf := cubeFlag_eq hS hcoh (boundary_of_cross hB hub hvb huv) hu
    rw [hf]
    by_cases hus : u∈S
    · norm_num [edgeLabel,indicatorTwo,hub,hvb,hsv,hus]
      decide
    · simp [edgeLabel,indicatorTwo,hub,hvb,hsv,hus]
  · have hsu : u∉S := fun h ↦ hub (hSB h)
    have hf := cubeFlag_eq hS hcoh
      (boundary_of_cross hB hvb hub (nearestStep_symm huv)) hv
    rw [hf]
    by_cases hvs : v∈S <;> norm_num [edgeLabel,indicatorTwo,hub,hvb,hsu,hvs]
  · have hsu : u∉S := fun h ↦ hub (hSB h)
    have hsv : v∉S := fun h ↦ hvb (hSB h)
    simp [edgeLabel,indicatorTwo,hub,hvb,hsu,hsv]

lemma edgeLabel_square {A B S : Set Vertex} (hB : NNComplementComponent A B)
    (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) (x : Vertex) (i j : Fin 3) :
    edgeLabel B S x (step x i)+edgeLabel B S (step x i) (step (step x i) j)=
    edgeLabel B S x (step x j)+edgeLabel B S (step x j) (step (step x j) i) := by
  by_cases hij : i=j
  · subst j; rfl
  have htop := unitCube_step_step x hij
  have htop' := unitCube_step_step x (Ne.symm hij)
  rw [edgeLabel_unitCube hB hS hcoh (unitCube_self x) (unitCube_step x i) (nearestStep_step x i),
    edgeLabel_unitCube hB hS hcoh (unitCube_step x i) htop (nearestStep_step _ j),
    edgeLabel_unitCube hB hS hcoh (unitCube_self x) (unitCube_step x j) (nearestStep_step x j),
    edgeLabel_unitCube hB hS hcoh (unitCube_step x j) htop' (nearestStep_step _ i),
    step_comm x i j]
  ring

lemma zmod_two_neg (z : ZMod 2) : -z=z := by fin_cases z <;> rfl

lemma starStep_symm {x y : Vertex} (h : starStep x y) : starStep y x :=
  ⟨Ne.symm h.1,fun i ↦ by simpa only [abs_sub_comm] using h.2 i⟩

lemma withinReach_preserves {D : Set Vertex} {e : Vertex → Vertex → Prop}
    {W : Type*} (q : Vertex → W)
    (hstep : ∀ x∈D, ∀ y∈D, e x y → q x=q y)
    {x y : Vertex} (h : withinReach e D x y) : q x=q y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head h' _ ih => exact (hstep _ h'.1 _ h'.2.1 h'.2.2).trans ih

lemma exists_boundary_potential {A B S : Set Vertex} (hA : A.Finite)
    (hB : NNComplementComponent A B) (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) :
    ∃ q : Vertex → ZMod 2, ∀ x y, nearestStep x y →
      q y-q x=edgeLabel B S x y := by
  obtain ⟨b,hb⟩ := (hA.image (fun x : Vertex ↦ x 0)).bddBelow
  have hmin (a : Vertex) (ha : a∈A) : b≤a 0 :=
    hb (Set.mem_image_of_mem _ ha)
  let l : ℤ := b-2
  let f : Fin 3 → Vertex → ZMod 2 := fun i x ↦ edgeLabel B S x (step x i)
  have hSB : S⊆B := fun _ hz ↦ (hS hz).1
  have hl : ∀ i x, x 0≤l → f i x=0 := by
    intro i x hx
    have hx0 : x 0<b := by dsimp [l] at hx; omega
    have hs0 : step x i 0<b := by
      by_cases hi : i=0
      · subst i; rw [step_apply_same]; dsimp [l] at hx; omega
      · rw [step_apply_ne x (Ne.symm hi)]; exact hx0
    have hxa : x∉A := fun ha ↦ (not_le.mpr hx0) (hmin x ha)
    have hsa : step x i∉A := fun ha ↦ (not_le.mpr hs0) (hmin _ ha)
    apply edgeLabel_zero_of_same hSB
    exact ⟨fun h ↦ hB.2.2 x h _ hsa (nearestStep_step x i),
      fun h ↦ hB.2.2 _ h x hxa (nearestStep_symm (nearestStep_step x i))⟩
  have hsq : ∀ i j x, f i x+f j (step x i)=f j x+f i (step x j) :=
    fun i j x ↦ edgeLabel_square hB hS hcoh x i j
  refine ⟨cubicalPotential f l,?_⟩
  intro x y hxy
  obtain ⟨i,hi|hi⟩ := nearestStep_eq_step hxy
  · subst y
    exact cubicalPotential_step f l hl hsq x i
  · subst x
    have h := cubicalPotential_step f l hl hsq y i
    calc
      _ = -(cubicalPotential f l (step y i)-cubicalPotential f l y) := by abel
      _ = -edgeLabel B S y (step y i) := by rw [h]
      _ = edgeLabel B S (step y i) y := by rw [zmod_two_neg,edgeLabel_symm]

theorem nnBoundary_starConnected {A B : Set Vertex} (hA : A.Finite)
    (hAc : NNConnected A) (hB : NNComplementComponent A B) :
    starConnected (nnBoundary A B) := by
  intro r hr y hy
  let S : Set Vertex := {z | z∈nnBoundary A B ∧ withinReach starStep (nnBoundary A B) r z}
  have hS : S⊆nnBoundary A B := fun _ hz ↦ hz.1
  have hSB : S⊆B := fun _ hz ↦ hz.1.1
  have hrs : r∈S := ⟨hr,Relation.ReflTransGen.refl⟩
  have hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S) := by
    intro u hu v hv huv
    exact ⟨fun hs ↦ ⟨hv,hs.2.tail ⟨hu,hv,huv⟩⟩,
      fun hs ↦ ⟨hu,hs.2.tail ⟨hv,hu,starStep_symm huv⟩⟩⟩
  obtain ⟨q,hq⟩ := exists_boundary_potential hA hB hS hcoh
  have hAnotB : ∀ a∈A, a∉B := fun _ ha hb ↦ Set.disjoint_left.mp hB.1 ha hb
  have hAcst : ∀ a∈A, ∀ a'∈A, q a=q a' := by
    intro a ha a' ha'
    apply withinReach_preserves q (D := A) _ (hAc a ha a' ha')
    intro u hu v hv huv
    have he := edgeLabel_zero_of_same hSB (show u∈B ↔ v∈B by
      simp only [hAnotB u hu,hAnotB v hv])
    exact (sub_eq_zero.mp ((hq u v huv).trans he)).symm
  have hBcst : ∀ a∈B, ∀ a'∈B, q a=q a' := by
    intro a ha a' ha'
    apply withinReach_preserves q (D := B) _ (hB.2.1 a ha a' ha')
    intro u hu v hv huv
    have he := edgeLabel_zero_of_same hSB (show u∈B ↔ v∈B by
      simp only [hu,hv])
    exact (sub_eq_zero.mp ((hq u v huv).trans he)).symm
  obtain ⟨a,ha,har⟩ := hr.2
  obtain ⟨a',ha',hay⟩ := hy.2
  have haS : a∉S := fun h ↦ hAnotB a ha (hSB h)
  have ha'S : a'∉S := fun h ↦ hAnotB a' ha' (hSB h)
  have hedge : edgeLabel B S a r=1 := by
    simp [edgeLabel,hrs,haS,hAnotB a ha]
  have hyedge : edgeLabel B S a' y=1 := by
    calc
      _ = q y-q a' := (hq a' y hay).symm
      _ = q r-q a := by rw [hBcst y hy.1 r hr.1,hAcst a' ha' a ha]
      _ = 1 := (hq a r har).trans hedge
  have hys : y∈S := by
    by_contra hys
    simp [edgeLabel,ha'S,hys] at hyedge
  exact hys.2

def avoidingStep (C : Finset Vertex) (x y : Vertex) : Prop :=
  x∉C ∧ y∉C ∧ nearestStep x y

def avoidingReach (C : Finset Vertex) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (avoidingStep C) x y

def exterior (C : Finset Vertex) : Set Vertex :=
  {x | x∉C ∧ Set.Infinite {y | avoidingReach C x y}}

def fill (C : Finset Vertex) : Set Vertex := (exterior C)ᶜ

def exteriorShell (C : Finset Vertex) : Set Vertex :=
  {x | x∈exterior C ∧ ∃ c∈C, starStep c x}

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_StarOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice
variable {A : Type*} [AddCommGroup A]

lemma exteriorShell_good (C : Finset Vertex) (B : Set Vertex)
    (hcomponent : ∀ c∈C, ∀ x∈B, starStep c x → x∈C) : exteriorShell C⊆Bᶜ := by
  rintro x ⟨hx, c,hc,hcx⟩ hxB
  exact hx.1 (hcomponent c hc x hxB hcx)

lemma withinReach_symm {D : Set Vertex} {e : Vertex → Vertex → Prop}
    (he : ∀ x y, e x y → e y x) {x y : Vertex} (h : withinReach e D x y) :
    withinReach e D y x := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact .single ⟨h.2.1,h.1,he _ _ h.2.2⟩
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

lemma withinReach_mono {D E : Set Vertex} {e : Vertex → Vertex → Prop}
    (hDE : D⊆E) {x y : Vertex} (h : withinReach e D x y) :
    withinReach e E x y := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact .single ⟨hDE h.1,hDE h.2.1,h.2.2⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma nearestStep_update (x : Vertex) (i : Fin 3) (k : ℤ) :
    nearestStep (Function.update x i k) (Function.update x i (k+1)) := by
  refine ⟨i,?_,?_⟩
  · simp
  · intro j hj
    simp [hj]

lemma withinReach_axis_le {D : Set Vertex} (x : Vertex) (i : Fin 3)
    (a b : ℤ) (hab : a≤b)
    (hD : ∀ k, a≤k → k≤b → Function.update x i k∈D) :
    withinReach nearestStep D (Function.update x i a) (Function.update x i b) := by
  have hpath : ∀ n : ℕ, (n:ℤ)≤b-a →
      withinReach nearestStep D (Function.update x i a) (Function.update x i (a+(n:ℤ))) := by
    intro n
    induction n with
    | zero => intro _; simp only [Nat.cast_zero,add_zero]; exact .refl
    | succ n ih =>
      intro hn
      have hn' : (n:ℤ)≤b-a := by omega
      have hprev := ih hn'
      have hu := hD (a+(n:ℤ)) (by omega) (by omega)
      have hv := hD (a+((n+1:ℕ):ℤ)) (by omega) (by omega)
      apply hprev.tail
      refine ⟨hu,hv,?_⟩
      convert nearestStep_update x i (a+(n:ℤ)) using 1; push_cast; abel_nf
  have hc : a+((b-a).toNat:ℤ)=b := by omega
  simpa only [hc] using hpath (b-a).toNat (by omega)

lemma withinReach_axis {D : Set Vertex} (x : Vertex) (i : Fin 3)
    (a b : ℤ)
    (hD : ∀ k, min a b≤k → k≤ max a b → Function.update x i k∈D) :
    withinReach nearestStep D (Function.update x i a) (Function.update x i b) := by
  rcases le_total a b with hab|hba
  · apply withinReach_axis_le x i a b hab
    simpa only [min_eq_left hab,max_eq_right hab] using hD
  · apply withinReach_symm (fun _ _ ↦ nearestStep_symm)
    apply withinReach_axis_le x i b a hba
    simpa only [min_eq_right hba,max_eq_left hba] using hD

def intervalBox (x y : Vertex) : Set Vertex :=
  {z | ∀ i, min (x i) (y i)≤z i ∧ z i≤ max (x i) (y i)}

def mixVertex (x y : Vertex) (n : ℕ) : Vertex := fun i ↦ if i.val<n then y i else x i

lemma mixVertex_zero (x y : Vertex) : mixVertex x y 0=x := by ext i; simp [mixVertex]
lemma mixVertex_three (x y : Vertex) : mixVertex x y 3=y := by
  ext i
  simp only [mixVertex,ite_eq_left i.isLt]
lemma mixVertex_box (x y : Vertex) (n : ℕ) : mixVertex x y n∈intervalBox x y := by
  intro i
  by_cases hi : i.val<n <;> simp [mixVertex,hi]
lemma mixVertex_succ (x y : Vertex) (n : ℕ) (hn : n<3) :
    mixVertex x y (n+1)=Function.update (mixVertex x y n) ⟨n,hn⟩ (y ⟨n,hn⟩) := by
  ext i
  by_cases hi : i=⟨n,hn⟩
  · subst i; simp [mixVertex]
  · have hin : i.val≠n := fun h ↦ hi (Fin.ext h)
    have hlt : (i.val<n+1) ↔ (i.val<n) := by omega
    simp only [Function.update_of_ne hi,mixVertex,hlt]

theorem intervalBox_reach (x y : Vertex) : withinReach nearestStep (intervalBox x y) x y := by
  have hpath : ∀ n : ℕ, n≤3 → withinReach nearestStep (intervalBox x y) x (mixVertex x y n) := by
    intro n
    induction n with
    | zero => intro _; rw [mixVertex_zero]; exact .refl
    | succ n ih =>
      intro hn
      have hn' : n<3 := by omega
      let i : Fin 3 := ⟨n,hn'⟩
      have hprev := ih (by omega)
      rw [mixVertex_succ x y n hn']
      apply hprev.trans
      have hold : mixVertex x y n i=x i := by simp [mixVertex,i]
      have haxis := withinReach_axis (D := intervalBox x y) (mixVertex x y n) i (x i) (y i) ?_
      · simpa only [withinReach,← hold,Function.update_eq_self,i] using haxis
      · intro k hk₁ hk₂ j
        by_cases hj : j=i
        · subst j
          simpa using And.intro hk₁ hk₂
        · rw [Function.update_of_ne hj]
          exact mixVertex_box x y n j
  simpa only [mixVertex_three] using hpath 3 (by omega)

lemma box_reach {D : Set Vertex} (x y : Vertex) (hD : intervalBox x y⊆D) :
    withinReach nearestStep D x y := withinReach_mono hD (intervalBox_reach x y)

lemma withinReach_end {D : Set Vertex} {e : Vertex → Vertex → Prop} {x y : Vertex}
    (hx : x∈D) (h : withinReach e D x y) : y∈D := by
  rcases h.cases_tail with he|⟨z,_,hzy⟩
  · exact he ▸ hx
  · exact hzy.2.1

lemma withinReach_invariant {D E : Set Vertex} {e : Vertex → Vertex → Prop}
    (hclosed : ∀ u∈E, ∀ v∈D, e u v → v∈E)
    {x y : Vertex} (hx : x∈E) (h : withinReach e D x y) : withinReach e E x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h' _ ih =>
    have hv := hclosed _ hx _ h'.2.1 h'.2.2
    exact (ih hv).head ⟨hx,hv,h'.2.2⟩

lemma avoidingReach_symm (C : Finset Vertex) {x y : Vertex}
    (h : avoidingReach C x y) : avoidingReach C y x :=
  withinReach_symm (D := (↑C)ᶜ) (fun _ _ ↦ nearestStep_symm) h

lemma exterior_of_reach (C : Finset Vertex) {x y : Vertex}
    (hx : x∈exterior C) (hxy : avoidingReach C x y) : y∈exterior C := by
  have hy : y∉C := withinReach_end (D := (↑C)ᶜ) hx.1 hxy
  refine ⟨hy,hx.2.mono ?_⟩
  intro z hz
  exact (avoidingReach_symm C hxy).trans hz

def integerBox (M : ℤ) : Finset Vertex :=
  Fintype.piFinset fun _ : Fin 3 ↦ Finset.Icc (-M) M

lemma mem_integerBox (M : ℤ) (x : Vertex) : x∈integerBox M ↔ ∀ i, |x i|≤M := by
  simp only [integerBox,Fintype.mem_piFinset,Finset.mem_Icc,abs_le]

lemma finite_coordinate_bound (C : Finset Vertex) :
    ∃ M : ℤ, 0≤M ∧ ∀ c∈C, ∀ i, |c i|≤M := by
  let s : Finset ℤ := C.biUnion (fun c ↦ Finset.univ.image (fun i : Fin 3 ↦ |c i|))
  obtain ⟨M,hM⟩ := s.finite_toSet.exists_le
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro c hc i
  apply (hM _ ?_).trans (le_max_left M 0)
  exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

lemma outside_box_reach (C : Finset Vertex) (M : ℤ) (hM : 0≤M)
    (hC : ∀ c∈C, ∀ i, |c i|≤M) (x : Vertex) (hx : x∉integerBox M) :
    avoidingReach C x (fun _ ↦ M+1) := by
  have hex : ∃ i, M < |x i| := by
    by_contra hn
    push Not at hn
    exact hx ((mem_integerBox M x).mpr hn)
  obtain ⟨i,hi⟩ := hex
  let r : Vertex := fun _ ↦ M+1
  let z : Vertex := Function.update r i (x i)
  have hxz : withinReach nearestStep ((↑C : Set Vertex)ᶜ) x z := by
    apply box_reach
    intro u hu huc
    have hui := hu i
    have hzi : z i=x i := by simp [z]
    rw [hzi,min_self,max_self] at hui
    have hueq : u i=x i := le_antisymm hui.2 hui.1
    have hbound := hC u huc i
    rw [hueq] at hbound
    omega
  have hzr : withinReach nearestStep ((↑C : Set Vertex)ᶜ) z r := by
    obtain ⟨j,hj⟩ : ∃ j : Fin 3, j≠i := exists_ne i
    apply box_reach
    intro u hu huc
    have huj := hu j
    have hzj : z j=M+1 := by simp [z,r,Function.update_of_ne hj]
    change min (z j) (M+1)≤u j ∧ u j≤ max (z j) (M+1) at huj
    rw [hzj,min_self,max_self] at huj
    have hueq : u j=M+1 := le_antisymm huj.2 huj.1
    have hbound := hC u huc j
    rw [hueq,abs_of_nonneg (by omega : 0≤M+1)] at hbound
    omega
  exact hxz.trans hzr

lemma exterior_reach_anchor (C : Finset Vertex) (M : ℤ) (hM : 0≤M)
    (hC : ∀ c∈C, ∀ i, |c i|≤M) {x : Vertex} (hx : x∈exterior C) :
    avoidingReach C x (fun _ ↦ M+1) := by
  obtain ⟨y,hxy,hy⟩ := hx.2.exists_notMem_finset (integerBox M)
  exact hxy.trans (outside_box_reach C M hM hC y hy)

theorem exterior_avoidingReach (C : Finset Vertex) {x y : Vertex}
    (hx : x∈exterior C) (hy : y∈exterior C) : avoidingReach C x y := by
  obtain ⟨M,hM,hC⟩ := finite_coordinate_bound C
  exact (exterior_reach_anchor C M hM hC hx).trans
    (avoidingReach_symm C (exterior_reach_anchor C M hM hC hy))

def doubleVertex (x : Vertex) : Vertex := fun i ↦ 2*x i

def thickCube (c : Vertex) : Set Vertex := {z | ∀ i, |z i-2*c i|≤1}

def thicken (C : Finset Vertex) : Finset Vertex :=
  C.biUnion fun c ↦ Fintype.piFinset fun i : Fin 3 ↦ Finset.Icc (2*c i-1) (2*c i+1)

lemma mem_thicken (C : Finset Vertex) (z : Vertex) :
    z∈thicken C ↔ ∃ c∈C, z∈thickCube c := by
  simp only [thicken,Finset.mem_biUnion,Fintype.mem_piFinset,Finset.mem_Icc]
  constructor
  · rintro ⟨c,hc,hz⟩
    refine ⟨c,hc,fun i ↦ abs_le.mpr ?_⟩
    have h := hz i
    constructor <;> omega
  · rintro ⟨c,hc,hz⟩
    refine ⟨c,hc,fun i ↦ ?_⟩
    have h := abs_le.mp (hz i)
    constructor <;> omega

lemma double_mem_cube (c : Vertex) : doubleVertex c∈thickCube c := by
  intro i; simp [doubleVertex]

lemma thickCube_subset (C : Finset Vertex) {c : Vertex} (hc : c∈C) :
    thickCube c⊆(↑(thicken C) : Set Vertex) := fun z hz ↦ (mem_thicken C z).mpr ⟨c,hc,hz⟩

lemma thickCube_NNConnected (c : Vertex) : NNConnected (thickCube c) := by
  intro x hx y hy
  apply box_reach
  intro z hz i
  have hx' := abs_le.mp (hx i)
  have hy' := abs_le.mp (hy i)
  have hz' := hz i
  apply abs_le.mpr
  constructor <;> omega

lemma thicken_adjacent_centers (C : Finset Vertex) {c d : Vertex}
    (hc : c∈C) (hd : d∈C) (hcd : starStep c d) :
    withinReach nearestStep (↑(thicken C)) (doubleVertex c) (doubleVertex d) := by
  let m : Vertex := c+d
  have hmC : m∈thickCube c := by
    intro i
    change |c i+d i-2*c i|≤1
    rw [show c i+d i-2*c i=d i-c i by ring,abs_sub_comm]
    exact hcd.2 i
  have hmD : m∈thickCube d := by
    intro i
    change |c i+d i-2*d i|≤1
    rw [show c i+d i-2*d i=c i-d i by ring]
    exact hcd.2 i
  exact (withinReach_mono (thickCube_subset C hc)
    (thickCube_NNConnected c _ (double_mem_cube c) m hmC)).trans
    (withinReach_mono (thickCube_subset C hd)
      (thickCube_NNConnected d m hmD _ (double_mem_cube d)))

lemma thicken_star_reach (C : Finset Vertex) {c d : Vertex}
    (h : withinReach starStep (↑C) c d) :
    withinReach nearestStep (↑(thicken C)) (doubleVertex c) (doubleVertex d) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact thicken_adjacent_centers C h.1 h.2.1 h.2.2
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma thicken_NNConnected (C : Finset Vertex) (hC : starConnected (↑C)) :
    NNConnected (↑(thicken C)) := by
  intro x hx y hy
  obtain ⟨c,hc,hcx⟩ := (mem_thicken C x).mp hx
  obtain ⟨d,hd,hdy⟩ := (mem_thicken C y).mp hy
  exact (withinReach_mono (thickCube_subset C hc)
    (thickCube_NNConnected c x hcx _ (double_mem_cube c))).trans
    ((thicken_star_reach C (hC c hc d hd)).trans
      (withinReach_mono (thickCube_subset C hd)
        (thickCube_NNConnected d _ (double_mem_cube d) y hdy)))

def complementComponent (A : Set Vertex) (r : Vertex) : Set Vertex :=
  {x | x∉A ∧ withinReach nearestStep Aᶜ r x}

lemma complementComponent_spec (A : Set Vertex) (r : Vertex) :
    NNComplementComponent A (complementComponent A r) := by
  have hclosed : ∀ x∈complementComponent A r, ∀ y, y∉A → nearestStep x y →
      y∈complementComponent A r := by
    intro x hx y hy hxy
    exact ⟨hy,hx.2.tail ⟨hx.1,hy,hxy⟩⟩
  refine ⟨Set.disjoint_left.mpr (fun _ ha hb ↦ hb.1 ha),?_,hclosed⟩
  intro x hx y hy
  apply withinReach_invariant (D := Aᶜ) (fun u hu v hv huv ↦ hclosed u hu v hv huv) hx
  exact (withinReach_symm (fun _ _ ↦ nearestStep_symm) hx.2).trans hy.2

lemma double_mem_thicken_iff (C : Finset Vertex) (x : Vertex) :
    doubleVertex x∈thicken C ↔ x∈C := by
  constructor
  · intro hx
    obtain ⟨c,hc,hcx⟩ := (mem_thicken C _).mp hx
    have he : x=c := by
      ext i
      have h := abs_le.mp (hcx i)
      dsimp [doubleVertex] at h
      omega
    exact he ▸ hc
  · intro hx
    exact (mem_thicken C _).mpr ⟨x,hx,double_mem_cube x⟩

lemma double_step (x : Vertex) (i : Fin 3) :
    doubleVertex (step x i)=step (step (doubleVertex x) i) i := by
  ext j
  by_cases hj : j=i
  · subst j
    simp only [doubleVertex,step_apply_same]
    ring
  · simp [doubleVertex,step,hj]

lemma splitPoint_not_thicken (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : x∉C) (hy : step x i∉C) : step (doubleVertex x) i∉thicken C := by
  intro hm
  obtain ⟨c,hc,hcm⟩ := (mem_thicken C _).mp hm
  have hrest : ∀ j, j≠i → c j=x j := by
    intro j hj
    have h := abs_le.mp (hcm j)
    rw [step_apply_ne _ hj] at h
    dsimp [doubleVertex] at h
    omega
  have hi := abs_le.mp (hcm i)
  rw [step_apply_same] at hi
  dsimp [doubleVertex] at hi
  have hci : c i=x i ∨ c i=x i+1 := by omega
  rcases hci with hci|hci
  · have he : c=x := by
      ext j
      by_cases hj : j=i
      · subst j; exact hci
      · exact hrest j hj
    exact hx (he ▸ hc)
  · have he : c=step x i := by
      ext j
      by_cases hj : j=i
      · subst j; rw [step_apply_same]; exact hci
      · rw [step_apply_ne _ hj]; exact hrest j hj
    exact hy (he ▸ hc)

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RoundBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
namespace HardSphere.Lattice
variable {A : Type*} [AddCommGroup A]

lemma double_avoiding_step (C : Finset Vertex) {x y : Vertex}
    (hx : x∉C) (hy : y∉C) (hxy : nearestStep x y) :
    withinReach nearestStep ((↑(thicken C))ᶜ) (doubleVertex x) (doubleVertex y) := by
  have hpos : ∀ u (i : Fin 3), u∉C → step u i∉C →
      withinReach nearestStep ((↑(thicken C))ᶜ) (doubleVertex u) (doubleVertex (step u i)) := by
    intro u i hu hui
    have hu' : doubleVertex u∉thicken C := by simpa only [double_mem_thicken_iff] using hu
    have hui' : doubleVertex (step u i)∉thicken C := by simpa only [double_mem_thicken_iff] using hui
    have hm := splitPoint_not_thicken C u i hu hui
    have hs : nearestStep (step (doubleVertex u) i) (doubleVertex (step u i)) := by
      rw [double_step]; exact nearestStep_step _ _
    exact (Relation.ReflTransGen.single ⟨hu',hm,nearestStep_step _ i⟩).tail ⟨hm,hui',hs⟩
  obtain ⟨i,hi|hi⟩ := nearestStep_eq_step hxy
  · subst y; exact hpos x i hx hy
  · subst x; exact withinReach_symm (fun _ _ ↦ nearestStep_symm) (hpos y i hy hx)

lemma double_avoidingReach (C : Finset Vertex) {x y : Vertex}
    (h : avoidingReach C x y) :
    withinReach nearestStep ((↑(thicken C))ᶜ) (doubleVertex x) (doubleVertex y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact double_avoiding_step C h.1 h.2.1 h.2.2
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def roundBox (z : Vertex) : Set Vertex := {x | ∀ i, |2*x i-z i|≤1}

lemma roundBox_nonempty (z : Vertex) : (roundBox z).Nonempty := by
  refine ⟨fun i ↦ z i/2,fun i ↦ abs_le.mpr ?_⟩
  dsimp only
  constructor <;> omega

lemma roundBox_NNConnected (z : Vertex) : NNConnected (roundBox z) := by
  intro x hx y hy
  apply box_reach
  intro u hu i
  have hxi := abs_le.mp (hx i)
  have hyi := abs_le.mp (hy i)
  have hui := hu i
  apply abs_le.mpr
  constructor <;> omega

lemma roundBox_overlap {z w : Vertex} (hzw : ∀ i, |z i-w i|≤1) :
    (roundBox z ∩ roundBox w).Nonempty := by
  refine ⟨fun i ↦ max (z i) (w i)/2,?_,?_⟩ <;> intro i
  · have h := abs_le.mp (hzw i)
    dsimp only
    apply abs_le.mpr
    constructor <;> omega
  · have h := abs_le.mp (hzw i)
    dsimp only
    apply abs_le.mpr
    constructor <;> omega

lemma nearestStep_starBound {x y : Vertex} (h : nearestStep x y) :
    ∀ i, |x i-y i|≤1 := by
  obtain ⟨j,hj,hrest⟩ := h
  intro i
  by_cases hi : i=j
  · subst i; exact hj.le
  · rw [hrest i hi,sub_self,abs_zero]; omega

lemma roundBox_avoids (C : Finset Vertex) {z : Vertex} (hz : z∉thicken C) :
    roundBox z⊆((↑C : Set Vertex)ᶜ) := by
  intro x hx hxc
  apply hz
  apply (mem_thicken C z).mpr
  refine ⟨x,hxc,fun i ↦ ?_⟩
  rw [abs_sub_comm]
  exact hx i

lemma round_nearest_reach {D : Set Vertex} {z w x y : Vertex}
    (hz : roundBox z⊆D) (hw : roundBox w⊆D)
    (hzw : ∀ i, |z i-w i|≤1) (hx : x∈roundBox z) (hy : y∈roundBox w) :
    withinReach nearestStep D x y := by
  obtain ⟨m,hmz,hmw⟩ := roundBox_overlap hzw
  exact (withinReach_mono hz (roundBox_NNConnected z x hx m hmz)).trans
    (withinReach_mono hw (roundBox_NNConnected w m hmw y hy))

lemma round_avoidingReach (C : Finset Vertex) {z w : Vertex}
    (h : withinReach nearestStep ((↑(thicken C))ᶜ) z w)
    (hz : z∉thicken C) {x y : Vertex} (hx : x∈roundBox z) (hy : y∈roundBox w) :
    avoidingReach C x y := by
  induction h using Relation.ReflTransGen.trans_induction_on generalizing x y with
  | refl => exact withinReach_mono (roundBox_avoids C hz) (roundBox_NNConnected _ x hx y hy)
  | single h =>
    exact round_nearest_reach (roundBox_avoids C h.1) (roundBox_avoids C h.2.1)
      (nearestStep_starBound h.2.2) hx hy
  | @trans a b c hab hbc ih₁ ih₂ =>
    have hb : b∉thicken C := withinReach_end hz hab
    obtain ⟨m,hm⟩ := roundBox_nonempty b
    exact (ih₁ hz hx hm).trans (ih₂ hb hm hy)

lemma mem_round_double (x : Vertex) : x∈roundBox (doubleVertex x) := by
  intro i; simp [doubleVertex]

lemma round_component_exterior (C : Finset Vertex) {r z x : Vertex}
    (hr : r∈exterior C) (hz : z∈complementComponent (↑(thicken C)) (doubleVertex r))
    (hx : x∈roundBox z) : x∈exterior C := by
  apply exterior_of_reach C hr
  exact round_avoidingReach C hz.2 (by simpa only [double_mem_thicken_iff] using hr.1)
    (mem_round_double r) hx

lemma round_boundary_shell (C : Finset Vertex) {r z : Vertex} (hr : r∈exterior C)
    (hz : z∈nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r))) :
    roundBox z⊆exteriorShell C := by
  intro x hx
  refine ⟨round_component_exterior C hr hz.1 hx,?_⟩
  obtain ⟨a,ha,haz⟩ := hz.2
  obtain ⟨c,hc,hca⟩ := (mem_thicken C a).mp ha
  refine ⟨c,hc,?_,?_⟩
  · intro he
    exact (round_component_exterior C hr hz.1 hx).1 (he ▸ hc)
  · intro i
    have ha' := abs_le.mp (hca i)
    have hz' := abs_le.mp (nearestStep_starBound haz i)
    have hx' := abs_le.mp (hx i)
    apply abs_le.mpr
    constructor <;> omega

lemma withinReach_first_entry {D A : Set Vertex} {x y : Vertex}
    (h : withinReach nearestStep D x y) (hxD : x∈D) (hx : x∉A) (hy : y∈A) :
    ∃ u v, withinReach nearestStep (D∩Aᶜ) x u ∧ u∈D ∧ u∉A ∧ v∈A ∧ nearestStep u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hx hy).elim
  | @head z w hzw _ ih =>
    by_cases hw : w∈A
    · exact ⟨z,w,.refl,hxD,hx,hw,hzw.2.2⟩
    · obtain ⟨u,v,hu,huD,huA,hvA,huv⟩ := ih hzw.2.1 hw
      exact ⟨u,v,hu.head ⟨⟨hxD,hx⟩,⟨hzw.2.1,hw⟩,hzw.2.2⟩,huD,huA,hvA,huv⟩

lemma shell_covered_by_boundary (C : Finset Vertex) {r x : Vertex}
    (hr : r∈exterior C) (hx : x∈exteriorShell C) :
    ∃ z∈nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r)),
      x∈roundBox z := by
  obtain ⟨c,hc,hcx⟩ := hx.2
  let m : Vertex := x+c
  let D : Set Vertex := {z | ∀ i, |z i-2*x i|≤1}
  have hstart : doubleVertex x∈D := by intro i; simp [doubleVertex]
  have hm : m∈thicken C := by
    apply (mem_thicken C m).mpr
    refine ⟨c,hc,fun i ↦ ?_⟩
    change |x i+c i-2*c i|≤1
    rw [show x i+c i-2*c i=x i-c i by ring,abs_sub_comm]
    exact hcx.2 i
  have hxnot : doubleVertex x∉thicken C := by simpa only [double_mem_thicken_iff] using hx.1.1
  have hp : withinReach nearestStep D (doubleVertex x) m := by
    apply box_reach
    intro z hz i
    have hi := abs_le.mp (hcx.2 i)
    have hz' := hz i
    change min (2*x i) (x i+c i)≤z i ∧ z i≤ max (2*x i) (x i+c i) at hz'
    apply abs_le.mpr
    constructor <;> omega
  obtain ⟨u,v,hu,huD,huA,hvA,huv⟩ := withinReach_first_entry hp hstart hxnot hm
  have hb : u∈complementComponent (↑(thicken C)) (doubleVertex r) := by
    refine ⟨huA,?_⟩
    exact (double_avoidingReach C (exterior_avoidingReach C hr hx.1)).trans
      (withinReach_mono (fun _ hz ↦ hz.2) hu)
  refine ⟨u,⟨hb,v,hvA,nearestStep_symm huv⟩,fun i ↦ ?_⟩
  rw [abs_sub_comm]
  exact huD i

lemma round_boundary_reach (C : Finset Vertex) {r z w : Vertex} (hr : r∈exterior C)
    (h : withinReach starStep
      (nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r))) z w)
    (hz : z∈nnBoundary (↑(thicken C)) (complementComponent (↑(thicken C)) (doubleVertex r)))
    {x y : Vertex} (hx : x∈roundBox z) (hy : y∈roundBox w) :
    withinReach nearestStep (exteriorShell C) x y := by
  induction h using Relation.ReflTransGen.trans_induction_on generalizing x y with
  | refl => exact withinReach_mono (round_boundary_shell C hr hz) (roundBox_NNConnected _ x hx y hy)
  | single h =>
    exact round_nearest_reach (round_boundary_shell C hr h.1) (round_boundary_shell C hr h.2.1)
      h.2.2.2 hx hy
  | @trans a b c hab hbc ih₁ ih₂ =>
    have hb := withinReach_end hz hab
    obtain ⟨m,hm⟩ := roundBox_nonempty b
    exact (ih₁ hz hx hm).trans (ih₂ hb hm hy)

theorem exteriorShell_NNConnected (C : Finset Vertex) (hC : starConnected (↑C)) :
    NNConnected (exteriorShell C) := by
  intro x hx y hy
  obtain ⟨z,hz,hxz⟩ := shell_covered_by_boundary C hx.1 hx
  obtain ⟨w,hw,hyw⟩ := shell_covered_by_boundary C hx.1 hy
  have hc := nnBoundary_starConnected (thicken C).finite_toSet (thicken_NNConnected C hC)
    (complementComponent_spec (↑(thicken C)) (doubleVertex x))
  exact round_boundary_reach C hx.1 (hc z hz w hw) hz hxz hyw

lemma nearestStep_ne {x y : Vertex} (h : nearestStep x y) : x≠y := by
  intro he
  obtain ⟨i,hi,_⟩ := h
  simp [he] at hi

lemma nearestStep_star {x y : Vertex} (h : nearestStep x y) : starStep x y :=
  ⟨nearestStep_ne h,nearestStep_starBound h⟩

lemma mem_fill_of_mem (C : Finset Vertex) {x : Vertex} (hx : x∈C) : x∈fill C :=
  fun h ↦ h.1 hx

def detourRegion (Γ : Set Vertex) (Cs : Finset (Finset Vertex)) : Set Vertex :=
  {x | x∈Γ ∨ ∃ C∈Cs, x∈exteriorShell C}

def goodDetourRegion (Γ B : Set Vertex) (Cs : Finset (Finset Vertex)) : Set Vertex :=
  detourRegion Γ Cs ∩ Bᶜ

theorem good_detour_reach (Γ B : Set Vertex) (Cs : Finset (Finset Vertex))
    (hCs : ∀ C∈Cs, starConnected (↑C))
    (hbad : ∀ C∈Cs, (↑C : Set Vertex)⊆B)
    (hmax : ∀ C∈Cs, ∀ c∈C, ∀ x∈B, starStep c x → x∈C)
    (hcover : ∀ x∈Γ, x∈B → ∃ C∈Cs, x∈C)
    {v w : Vertex} (hvΓ : v∈Γ) (_hwΓ : w∈Γ)
    (hv : ∀ C∈Cs, v∈exterior C) (hw : ∀ C∈Cs, w∈exterior C)
    (hwalk : withinReach nearestStep Γ v w) :
    withinReach nearestStep (goodDetourRegion Γ B Cs) v w := by
  let D := goodDetourRegion Γ B Cs
  have hvGood : v∉B := by
    intro hvB
    obtain ⟨C,hC,hvC⟩ := hcover v hvΓ hvB
    exact (hv C hC).1 hvC
  have hvD : v∈D := ⟨Or.inl hvΓ,hvGood⟩
  let R : Set Vertex := {x | x∈D ∧ withinReach nearestStep D v x}
  have hvR : v∈R := ⟨hvD,.refl⟩
  have hstep : ∀ x∈R, ∀ y∈D, nearestStep x y → y∈R := by
    intro x hx y hy hxy
    exact ⟨hy,hx.2.tail ⟨hx.1,hy,hxy⟩⟩
  have hRext : ∀ C∈Cs, ∀ x∈R, x∈exterior C := by
    intro C hC x hx
    apply exterior_of_reach C (hv C hC)
    apply withinReach_mono (D := D) _ hx.2
    intro y hy hyC
    exact hy.2 (hbad C hC hyC)
  have hshellD : ∀ C∈Cs, exteriorShell C⊆D := by
    intro C hC x hx
    exact ⟨Or.inr ⟨C,hC,hx⟩,exteriorShell_good C B (hmax C hC) hx⟩
  let active : Finset Vertex → Prop := fun C ↦ ∃ z∈exteriorShell C, z∈R
  have hactive : ∀ C∈Cs, active C → exteriorShell C⊆R := by
    intro C hC hact x hx
    obtain ⟨z,hz,hzR⟩ := hact
    have hp := withinReach_mono (hshellD C hC) ((exteriorShell_NNConnected C (hCs C hC)) z hz x hx)
    exact ⟨hshellD C hC hx,hzR.2.trans hp⟩
  let E : Set Vertex := {x | x∈R ∨ ∃ C∈Cs, active C ∧ x∈fill C}
  have hE : ∀ x∈E, ∀ y∈Γ, nearestStep x y → y∈E := by
    intro x hx y hy hxy
    rcases hx with hx|⟨C,hC,hact,hxfill⟩
    · by_cases hyB : y∈B
      · obtain ⟨C,hC,hyC⟩ := hcover y hy hyB
        have hxshell : x∈exteriorShell C :=
          ⟨hRext C hC x hx,y,hyC,nearestStep_star (nearestStep_symm hxy)⟩
        exact Or.inr ⟨C,hC,⟨x,hxshell,hx⟩,mem_fill_of_mem C hyC⟩
      · exact Or.inl (hstep x hx y ⟨Or.inl hy,hyB⟩ hxy)
    · by_cases hyfill : y∈fill C
      · exact Or.inr ⟨C,hC,hact,hyfill⟩
      · have hyext : y∈exterior C := by simpa only [fill,Set.mem_compl_iff,not_not] using hyfill
        have hxC : x∈C := by
          by_contra hxC
          exact hxfill (exterior_of_reach C hyext (.single ⟨hyext.1,hxC,nearestStep_symm hxy⟩))
        have hyshell : y∈exteriorShell C := ⟨hyext,x,hxC,nearestStep_star hxy⟩
        exact Or.inl (hactive C hC hact hyshell)
  have hpE := withinReach_invariant (D := Γ) hE (show v∈E from Or.inl hvR) hwalk
  have hwE := withinReach_end (show v∈E from Or.inl hvR) hpE
  rcases hwE with hwR|⟨C,hC,_,hwfill⟩
  · exact hwR.2
  · exact (hwfill (hw C hC)).elim

def nearestGraph : SimpleGraph Vertex where
  Adj := nearestStep
  symm := ⟨by intro x y h; exact nearestStep_symm h⟩
  loopless := ⟨by intro x h; exact nearestStep_ne h rfl⟩

def restrictedNearestGraph (D : Set Vertex) : SimpleGraph Vertex where
  Adj x y := x∈D ∧ y∈D ∧ nearestStep x y
  symm := ⟨by intro x y h; exact ⟨h.2.1,h.1,nearestStep_symm h.2.2⟩⟩
  loopless := ⟨by intro x h; exact nearestStep_ne h.2.2 rfl⟩

lemma withinReach_simple_path {D : Set Vertex} {v w : Vertex} (hv : v∈D)
    (h : withinReach nearestStep D v w) :
    ∃ p : nearestGraph.Walk v w, p.IsPath ∧ ∀ x∈p.support, x∈D := by
  have hr : (restrictedNearestGraph D).Reachable v w :=
    (SimpleGraph.reachable_iff_reflTransGen v w).mpr h
  obtain ⟨q⟩ := hr
  let f : restrictedNearestGraph D →g nearestGraph :=
    ⟨id,fun {_ _} h ↦ h.2.2⟩
  have hs : ∀ {u z : Vertex} (p : (restrictedNearestGraph D).Walk u z),
      u∈D → ∀ x∈p.support, x∈D := by
    intro u z p
    induction p with
    | nil =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
      subst x
      exact hu
    | @cons u v z huv p ih =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact hu
      · exact ih huv.2.1 x hx
  refine ⟨q.toPath.val.map f,SimpleGraph.Walk.IsPath.map (fun _ _ h ↦ h) q.toPath.isPath,?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
  change y=x at he
  subst x
  exact hs q.toPath.val hv y hy

theorem simple_good_detour (Γ B : Set Vertex) (Cs : Finset (Finset Vertex))
    (hCs : ∀ C∈Cs, starConnected (↑C))
    (hbad : ∀ C∈Cs, (↑C : Set Vertex)⊆B)
    (hmax : ∀ C∈Cs, ∀ c∈C, ∀ x∈B, starStep c x → x∈C)
    (hcover : ∀ x∈Γ, x∈B → ∃ C∈Cs, x∈C)
    (hmeet : ∀ C∈Cs, ∃ x∈Γ, x∈C)
    {v w : Vertex} (hvΓ : v∈Γ) (hwΓ : w∈Γ)
    (hv : ∀ C∈Cs, v∈exterior C) (hw : ∀ C∈Cs, w∈exterior C)
    (hwalk : withinReach nearestStep Γ v w) :
    ∃ p : nearestGraph.Walk v w, p.IsPath ∧
      ∀ x∈p.support, x∉B ∧ (x∈Γ ∨ ∃ C∈Cs, (∃ z∈Γ, z∈C) ∧ x∈exteriorShell C) := by
  have hvD : v∈goodDetourRegion Γ B Cs := by
    refine ⟨Or.inl hvΓ,?_⟩
    intro hvB
    obtain ⟨C,hC,hvC⟩ := hcover v hvΓ hvB
    exact (hv C hC).1 hvC
  obtain ⟨p,hp,hpD⟩ := withinReach_simple_path hvD
    (good_detour_reach Γ B Cs hCs hbad hmax hcover hvΓ hwΓ hv hw hwalk)
  refine ⟨p,hp,fun x hx ↦ ⟨(hpD x hx).2,?_⟩⟩
  rcases (hpD x hx).1 with hxΓ|⟨C,hC,hxC⟩
  · exact Or.inl hxΓ
  · exact Or.inr ⟨C,hC,hmeet C hC,hxC⟩

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LiftedBadComponent
attribute [-instance] _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

def liftedBadComponent (B : Set Vertex) (z : Vertex) : Set Vertex :=
  {w | z ∈ B ∧ w ∈ B ∧ withinReach starStep B z w}

def FiniteBadComponents (B : Set Vertex) : Prop :=
  ∀ z ∈ B, (liftedBadComponent B z).Finite

def IsBadComponent (B : Set Vertex) (C : Finset Vertex) : Prop :=
  ∃ z ∈ B, (↑C : Set Vertex) = liftedBadComponent B z

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

abbrev Point := Fin 3 → ℝ

def liftPoint (L : Length) (x : Point) : Torus L := fun j ↦ (x j : AddCircle L.val)

def liftedCube (h : ℝ) (z : Vertex) : Set Point :=
  Set.Icc (fun j ↦ h * (z j : ℝ) - 1/2) (fun j ↦ h * ((z j : ℝ) + 1) - 1/2)

def microCube (L : Length) (h : ℝ) (z : Vertex) : Set (Torus L) :=
  liftPoint L '' liftedCube h z

def forbidden {n : ℕ} {L : Length} (r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  {x | ∃ j, torusDistance L x (Y j) ≤ r}

def slice {n : ℕ} {L : Length} (r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  (forbidden r Y)ᶜ

def bad {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set Vertex :=
  {z | ∃ x ∈ microCube L h z, x ∈ forbidden r Y}

def exceptional {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Prop :=
  Y ∉ allowed n L r ∨ ¬ FiniteBadComponents (bad h r Y)

def omitted {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  {x | exceptional h r Y ∨
    ∃ C : Finset Vertex, IsBadComponent (bad h r Y) C ∧
      ∃ z ∈ fill C, x ∈ microCube L h z}

def retained {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  (omitted h r Y)ᶜ

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_DiscreteTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice
abbrev DiscreteTorus (K : ℕ) := Fin 3 → ZMod K

def torusProjection (K : ℕ) (x : Vertex) : DiscreteTorus K := fun i ↦ (x i : ZMod K)

def rangeStep (a : ℕ) (x y : Vertex) : Prop := x≠y ∧ ∀ i, |x i-y i|≤a

def torusRangeStep (K a : ℕ) (x y : DiscreteTorus K) : Prop :=
  x≠y ∧ ∃ d : Vertex, (∀ i, |d i|≤a) ∧ ∀ i, y i=x i+(d i : ZMod K)

lemma rangeStep_symm {a : ℕ} {x y : Vertex} (h : rangeStep a x y) : rangeStep a y x :=
  ⟨h.1.symm,fun i ↦ by rw [abs_sub_comm]; exact h.2 i⟩

lemma torusRangeStep_symm {K a : ℕ} {x y : DiscreteTorus K} (h : torusRangeStep K a x y) :
    torusRangeStep K a y x := by
  obtain ⟨hne,d,hd,he⟩ := h
  refine ⟨hne.symm,-d,fun i ↦ by simpa using hd i,fun i ↦ ?_⟩
  simp only [Pi.neg_apply,Int.cast_neg,he i]
  abel

def forbiddenCuts {K : ℕ} (S : Finset (DiscreteTorus K)) (a : ℕ) (i : Fin 3) : Finset (ZMod K) :=
  S.biUnion fun x ↦ (Finset.Icc 1 a).image fun j : ℕ ↦ x i+(j : ZMod K)

lemma forbiddenCuts_card {K : ℕ} (S : Finset (DiscreteTorus K)) (a : ℕ) (i : Fin 3) :
    (forbiddenCuts S a i).card≤a*S.card := by
  calc
    _ ≤ ∑ x∈S, ((Finset.Icc 1 a).image fun j : ℕ ↦ x i+(j : ZMod K)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x∈S, a := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using
        (Finset.card_image_le (s := Finset.Icc 1 a) (f := fun j : ℕ ↦ x i+(j : ZMod K)))
    _ = a*S.card := by simp [Nat.mul_comm]

lemma exists_vacant_cut {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (hsmall : a*S.card<K) (i : Fin 3) : ∃ c : ZMod K, c∉forbiddenCuts S a i := by
  by_contra hn
  push Not at hn
  have he : forbiddenCuts S a i=Finset.univ := Finset.eq_univ_of_forall hn
  have hc := forbiddenCuts_card S a i
  rw [he,Finset.card_univ,ZMod.card K] at hc
  omega

lemma cut_coordinate_bound {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (i : Fin 3) {c : ZMod K} (hc : c∉forbiddenCuts S a i) {x : DiscreteTorus K} (hx : x∈S) :
    (x i-c).val+a<K := by
  have hv := ZMod.val_lt (x i-c)
  by_contra hn
  have hj₁ : 1≤K-(x i-c).val := by omega
  have hj₂ : K-(x i-c).val≤a := by omega
  apply hc
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hx,Finset.mem_image.mpr ⟨K-(x i-c).val,Finset.mem_Icc.mpr ⟨hj₁,hj₂⟩,?_⟩⟩
  rw [Nat.cast_sub hv.le,ZMod.natCast_self,ZMod.natCast_zmod_val]
  abel

def cutLift {K : ℕ} (cut : DiscreteTorus K) (x : DiscreteTorus K) : Vertex :=
  fun i ↦ (cut i).val+(x i-cut i).val

lemma cutLift_projection {K : ℕ} [NeZero K] (cut x : DiscreteTorus K) :
    torusProjection K (cutLift cut x)=x := by
  ext i
  simp only [torusProjection,cutLift,Int.cast_add,Int.cast_natCast,ZMod.natCast_zmod_val]
  abel

lemma small_multiple_zero {K : ℕ} {z : ℤ} (hz : (z : ZMod K)=0) (hsmall : |z|<K) : z=0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((ZMod.intCast_zmod_eq_zero_iff_dvd z K).mp hz)
  rw [← Int.natCast_natAbs] at hsmall
  simpa only [Int.natAbs_natCast] using (show z.natAbs<K by exact_mod_cast hsmall)

lemma cutLift_edge {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (cut : DiscreteTorus K) (hcut : ∀ i, cut i∉forbiddenCuts S a i)
    {x y : DiscreteTorus K} (hx : x∈S) (hy : y∈S) (hxy : torusRangeStep K a x y) :
    rangeStep a (cutLift cut x) (cutLift cut y) := by
  obtain ⟨hne,d,hd,he⟩ := hxy
  refine ⟨fun h ↦ hne (by simpa only [cutLift_projection] using congrArg (torusProjection K) h),?_⟩
  intro i
  have hx' := cut_coordinate_bound S a i (hcut i) hx
  have hy' := cut_coordinate_bound S a i (hcut i) hy
  have hd' := abs_le.mp (hd i)
  have hprojX := congrFun (cutLift_projection cut x) i
  have hprojY := congrFun (cutLift_projection cut y) i
  change ((cutLift cut x i : ℤ) : ZMod K)=x i at hprojX
  change ((cutLift cut y i : ℤ) : ZMod K)=y i at hprojY
  have hzero : ((cutLift cut y i-cutLift cut x i-d i : ℤ) : ZMod K)=0 := by
    push_cast
    rw [hprojX,hprojY,he i]
    abel
  have hsmall : |cutLift cut y i-cutLift cut x i-d i|<K := by
    dsimp only [cutLift]
    apply abs_lt.mpr
    constructor <;> omega
  have heq := small_multiple_zero hzero hsmall
  rw [show cutLift cut x i-cutLift cut y i= -d i by omega,abs_neg]
  exact hd i

theorem small_set_lift {K : ℕ} [NeZero K] (S : Finset (DiscreteTorus K)) (a : ℕ)
    (hsmall : a*S.card<K) :
    ∃ f : DiscreteTorus K → Vertex,
      (∀ x, torusProjection K (f x)=x) ∧
      (∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y)) := by
  choose cut hcut using exists_vacant_cut S a hsmall
  exact ⟨cutLift cut,cutLift_projection cut,fun _ hx _ hy hxy ↦ cutLift_edge S a cut hcut hx hy hxy⟩

lemma connected_coordinate_span {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Preconnected) (f : V → Vertex) (a : ℕ)
    (hedge : ∀ x y, G.Adj x y → ∀ i, |f x i-f y i|≤a) (x y : V) (i : Fin 3) :
    |f x i-f y i|≤a*(Fintype.card V-1) := by
  obtain ⟨p⟩ := hG x y
  let q := p.toPath
  have hlen := q.isPath.length_lt
  have hwalk : ∀ {u v : V} (w : G.Walk u v), |f u i-f v i|≤(a:ℤ)*w.length := by
    intro u v w
    induction w with
    | nil => simp
    | @cons u v w huv p ih =>
      calc
        |f u i-f w i| ≤ |f u i-f v i|+|f v i-f w i| := abs_sub_le _ _ _
        _ ≤ (a:ℤ)+(a:ℤ)*p.length := add_le_add (hedge u v huv i) ih
        _ = (a:ℤ)*(SimpleGraph.Walk.cons huv p).length := by simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]; ring
  have hlen' : (q.val.length:ℤ)<Fintype.card V := by exact_mod_cast hlen
  exact (hwalk q.val).trans (mul_le_mul_of_nonneg_left (by omega) (by positivity))

def torusRangeGraph (K a : ℕ) : SimpleGraph (DiscreteTorus K) where
  Adj := torusRangeStep K a
  symm := ⟨by intro x y h; exact torusRangeStep_symm h⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def periodicLift (K a : ℕ) (S : Finset (DiscreteTorus K)) (r : Vertex) : Set Vertex :=
  {x | torusProjection K x∈S ∧ Relation.ReflTransGen
    (fun u v ↦ torusProjection K u∈S ∧ torusProjection K v∈S ∧ rangeStep a u v) r x}

lemma short_projection_ne {K a : ℕ} (hK : 2*a<K) {x y : Vertex} (h : rangeStep a x y) :
    torusProjection K x≠torusProjection K y := by
  intro he
  apply h.1
  ext i
  apply sub_eq_zero.mp
  apply small_multiple_zero
  · simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun he i)
  · exact (h.2 i).trans_lt (by exact_mod_cast (show a<K by omega))

lemma rangeStep_projection {K a : ℕ} (hK : 2*a<K) {x y : Vertex} (h : rangeStep a x y) :
    torusRangeStep K a (torusProjection K x) (torusProjection K y) := by
  refine ⟨short_projection_ne hK h,y-x,fun i ↦ ?_,fun i ↦ ?_⟩
  · simp only [Pi.sub_apply,abs_sub_comm]; exact h.2 i
  · simp only [Pi.sub_apply,torusProjection,Int.cast_sub]; abel

lemma lift_offset_step {K a : ℕ} (hK : 2*a<K) (S : Finset (DiscreteTorus K))
    (f : DiscreteTorus K → Vertex) (hf : ∀ x, torusProjection K (f x)=x)
    (hedge : ∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y))
    {x y : Vertex} (hx : torusProjection K x∈S) (hy : torusProjection K y∈S)
    (hxy : rangeStep a x y) : y-f (torusProjection K y)=x-f (torusProjection K x) := by
  have hxy' := hedge _ hx _ hy (rangeStep_projection hK hxy)
  ext i
  have hxproj := congrFun (hf (torusProjection K x)) i
  have hyproj := congrFun (hf (torusProjection K y)) i
  change ((f (torusProjection K x) i:ℤ):ZMod K)=(x i:ZMod K) at hxproj
  change ((f (torusProjection K y) i:ℤ):ZMod K)=(y i:ZMod K) at hyproj
  have hzero : ((y i-f (torusProjection K y) i-(x i-f (torusProjection K x) i):ℤ):ZMod K)=0 := by
    push_cast
    rw [hxproj,hyproj]
    simp
  have hbd := abs_le.mp (hxy.2 i)
  have hbd' := abs_le.mp (hxy'.2 i)
  have hK' : (2:ℤ)*a<K := by exact_mod_cast hK
  have heq := small_multiple_zero hzero (show |y i-f (torusProjection K y) i-(x i-f (torusProjection K x) i)|<K by
    apply abs_lt.mpr; constructor <;> omega)
  dsimp only [Pi.sub_apply]
  omega

lemma lift_offset_reach {K a : ℕ} (hK : 2*a<K) (S : Finset (DiscreteTorus K))
    (f : DiscreteTorus K → Vertex) (hf : ∀ x, torusProjection K (f x)=x)
    (hedge : ∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y))
    {r x : Vertex} (hx : x∈periodicLift K a S r) :
    x-f (torusProjection K x)=r-f (torusProjection K r) := by
  rcases hx with ⟨hmem,hreach⟩
  clear hmem
  induction hreach with
  | refl => rfl
  | @tail u v _ huv ih => exact (lift_offset_step hK S f hf hedge huv.1 huv.2.1 huv.2.2).trans ih

lemma translated_projection {K : ℕ} (f : DiscreteTorus K → Vertex)
    (hf : ∀ x, torusProjection K (f x)=x) (r : Vertex) (x : DiscreteTorus K) :
    torusProjection K (f x+(r-f (torusProjection K r)))=x := by
  ext i
  have h₁ := congrFun (hf x) i
  have h₂ := congrFun (hf (torusProjection K r)) i
  change ((f x i:ℤ):ZMod K)=x i at h₁
  change ((f (torusProjection K r) i:ℤ):ZMod K)=(r i:ZMod K) at h₂
  simp only [torusProjection,Pi.add_apply,Pi.sub_apply,Int.cast_add,Int.cast_sub,h₁,h₂,
    sub_self,add_zero]

lemma rangeStep_translate {a : ℕ} {x y : Vertex} (h : rangeStep a x y) (t : Vertex) :
    rangeStep a (x+t) (y+t) := by
  refine ⟨fun he ↦ h.1 (add_right_cancel he),fun i ↦ ?_⟩
  simpa only [Pi.add_apply,add_sub_add_right_eq_sub] using h.2 i

lemma translated_reach {K a : ℕ} (S : Finset (DiscreteTorus K))
    (hS : ((torusRangeGraph K a).induce (↑S)).Preconnected)
    (f : DiscreteTorus K → Vertex) (hf : ∀ x, torusProjection K (f x)=x)
    (hedge : ∀ x∈S, ∀ y∈S, torusRangeStep K a x y → rangeStep a (f x) (f y))
    (r : Vertex) (hr : torusProjection K r∈S) (x : DiscreteTorus K) (hx : x∈S) :
    f x+(r-f (torusProjection K r))∈periodicLift K a S r := by
  refine ⟨by simpa only [translated_projection f hf] using hx,?_⟩
  have hp := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (hS ⟨torusProjection K r,hr⟩ ⟨x,hx⟩)
  have hmap : ∀ {u v : ↑(↑S : Set (DiscreteTorus K))},
      Relation.ReflTransGen ((torusRangeGraph K a).induce (↑S)).Adj u v →
      Relation.ReflTransGen
        (fun u v ↦ torusProjection K u∈S ∧ torusProjection K v∈S ∧ rangeStep a u v)
        (f u.val+(r-f (torusProjection K r))) (f v.val+(r-f (torusProjection K r))) := by
    intro u v huv
    induction huv using Relation.ReflTransGen.trans_induction_on with
    | refl => exact .refl
    | @single u v huv =>
      apply Relation.ReflTransGen.single
      refine ⟨?_,?_,rangeStep_translate (hedge u.val u.property v.val v.property huv) _⟩
      · simpa only [translated_projection f hf,Finset.mem_coe] using u.property
      · simpa only [translated_projection f hf,Finset.mem_coe] using v.property
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have h := hmap hp
  rw [show f (torusProjection K r)+(r-f (torusProjection K r))=r by abel] at h
  exact h

theorem small_periodic_lifts {K a : ℕ} [NeZero K] (hK : 2*a<K)
    (S : Finset (DiscreteTorus K)) (hsmall : a*S.card<K)
    (hS : ((torusRangeGraph K a).induce (↑S)).Preconnected)
    (r : Vertex) (hr : torusProjection K r∈S) :
    ∃ C : Finset Vertex,
      (↑C : Set Vertex)=periodicLift K a S r ∧
      Set.BijOn (torusProjection K) (↑C) (↑S) ∧
      (∀ x∈C, ∀ y∈C, ∀ i, |x i-y i|≤a*((S.card:ℤ)-1)) := by
  obtain ⟨f,hf,hedge⟩ := small_set_lift S a hsmall
  let g : DiscreteTorus K → Vertex := fun x ↦ f x+(r-f (torusProjection K r))
  let C : Finset Vertex := S.image g
  have hproj : ∀ x, torusProjection K (g x)=x := translated_projection f hf r
  have heq : (↑C : Set Vertex)=periodicLift K a S r := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact translated_reach S hS f hf hedge r hr u hu
    · intro hx
      refine Finset.mem_image.mpr ⟨torusProjection K x,hx.1,?_⟩
      have he := lift_offset_reach hK S f hf hedge hx
      dsimp only [g]
      rw [← he]
      abel
  refine ⟨C,heq,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro x hx
      rw [heq] at hx
      exact hx.1
    · intro x hx y hy hxy
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
      rw [hproj,hproj] at hxy
      exact congrArg g hxy
    · intro x hx
      exact ⟨g x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,hproj x⟩
  · intro x hx y hy i
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    have hspan := connected_coordinate_span ((torusRangeGraph K a).induce (↑S)) hS
      (fun x ↦ f x.val) a (fun x y h i ↦ (hedge x.val x.property y.val y.property h).2 i)
      ⟨u,hu⟩ ⟨v,hv⟩ i
    simpa only [g,Pi.add_apply,add_sub_add_right_eq_sub,Fintype.card_coe,Finset.coe_sort_coe] using hspan

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FilledRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

def filledRegion (L : Length) (h : ℝ) (C : Finset Vertex) : Set (Torus L) :=
  ⋃ z ∈ fill C, microCube L h z

def witnessBox (h : ℝ) (c : Point) : Finset Vertex :=
  Finset.Icc (fun j ↦ ⌊(c j + 1/2) / h⌋ - 3)
    (fun j ↦ ⌊(c j + 1/2) / h⌋ + 3)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

def gridCorner (L : Length) (h : ℝ) (z : Vertex) : Torus L :=
  liftPoint L (fun i ↦ h*(z i : ℝ)-1/2)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmallComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

def SmallComponent (h : ℝ) (C : Finset Vertex) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, ∀ j, h * |(u j : ℝ) - v j| ≤ 1

def microColumn (L : Length) (h : ℝ) (z : Vertex) : Set (Torus L) :=
  Set.univ.pi fun j ↦ Metric.closedBall
    ((h * (z j : ℝ) + h/2 - 1/2 : ℝ) : AddCircle L.val)
    (if j = 0 then 1 + h/2 else h/2)

def bathWitnessCover {n : ℕ} {L : Length} (h : ℝ) (Y : Configuration n L) : Finset Vertex :=
  Finset.univ.biUnion fun i ↦ witnessBox h
    (fun j ↦ (AddCircle.equivIco L.val 0 (Y i j)).val)

def smallFills {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  {x | ∃ C, IsBadComponent (bad h r Y) C ∧ SmallComponent h C ∧ x ∈ filledRegion L h C}

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MicroPeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

def microPeriod (r : ℝ) : ℕ := ⌈1/r⌉₊
def microMesh (r : ℝ) : ℝ := 1/(microPeriod r : ℝ)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AnimalFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def LargeBadComponent (G : SimpleGraph V) (B : Finset V) (m : ℕ) : Prop :=
  ∃ C∈badComponents G B, m≤C.card

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

def parent (q : ℕ) (z : Vertex) : Vertex := fun i ↦ z i / (q : ℤ)

def coarseCenter (L : Length) (v : Vertex) : Torus L :=
  liftPoint L (fun i ↦ (v i : ℝ)+1/2)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ParentStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical ENNReal

namespace HardSphere.Lattice
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma badGraph_reachable_induce {G : SimpleGraph V} {B : Finset V} {x y : V}
    (hp : (badGraph G B).Reachable x y) (hx : x ∈ B) (hy : y ∈ B) :
    (G.induce (↑B : Set V)).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hp ⊢
  induction hp with
  | refl => exact .refl
  | @tail u v _ huv ih => exact (ih huv.1).tail huv.2.2

lemma badComponent_preconnected (G : SimpleGraph V) (B : Finset V) (x : V) :
    (G.induce (↑(badComponent G B x) : Set V)).Preconnected := by
  intro u v
  have hu := (mem_badComponent G B x u).mp u.property
  have hv := (mem_badComponent G B x v).mp v.property
  have hp := (reachable_inside_component G B hu.2).symm.trans
    (reachable_inside_component G B hv.2)
  exact badGraph_reachable_induce hp u.property v.property
end HardSphere.Lattice

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LargeParentMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

def LargeParentMarked {n K : ℕ} {L : Length} (q : ℕ) (h r : ℝ)
    (Y : Configuration n L) (B : Finset (DiscreteTorus K)) : Prop :=
  ∀ z ∈ bad h r Y,
    (¬ (liftedBadComponent (bad h r Y) z).Finite ∨
      ∃ C, IsBadComponent (bad h r Y) C ∧ z ∈ C ∧ ¬ SmallComponent h C) →
    torusProjection K (parent q z) ∈ B

def rootBox (L : Length) (v : Vertex) (R : ℝ) : Set (Torus L) :=
  Set.univ.pi fun i ↦ Metric.closedBall (((v i : ℝ)+1/2 : ℝ) : AddCircle L.val) R

def siteRep {K : ℕ} (v : DiscreteTorus K) : Vertex := fun i ↦ (v i).val

def siteCenter {K : ℕ} (L : Length) (v : DiscreteTorus K) : Torus L :=
  coarseCenter L (siteRep v)

def closeSet {n K : ℕ} [NeZero K] (L : Length) (s T : ℝ)
    (X : Configuration n L) : Finset (DiscreteTorus K) := by
  classical
  exact Finset.univ.filter fun v ↦ T ≤ ((pairCloseLabels L s (siteCenter L v) X).card:ℝ)

def largeBoxUnion {K : ℕ} [NeZero K] (L : Length) (B : Finset (DiscreteTorus K)) : Set (Torus L) :=
  ⋃ m : ℕ, ⋃ v : DiscreteTorus K, ⋃ S ∈ rootedAnimals (torusRangeGraph K 1) v (m+1),
    ⋃ (_ : S ⊆ B), rootBox L (siteRep v) ((m:ℝ)+2)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital

def packingBox (c : Fin 3 → ℝ) : Finset Vertex :=
  Finset.Icc (fun j ↦ ⌊c j - 1/2⌋ - 14) (fun j ↦ ⌊c j - 1/2⌋ + 14)

end HardSphere.FreeVisits

namespace HardSphere
open MeasureTheory Wiener Set
attribute [local irreducible] torusDistance

def pathVisitsBall {n : ℕ} (L : Length) (R : ℝ) (v : Torus L)
    (i : Fin n) (ω : ConfigurationPath n L) : Prop :=
  ∃ q : Time, torusDistance L (ω q i) v ≤ R

@[simp] lemma pathVisitsBall_reverse {n : ℕ} (L : Length) (R : ℝ) (v : Torus L)
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitsBall L R v i (reverseConfigurationPath n L ω) ↔ pathVisitsBall L R v i ω := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨reverseTime q,hq⟩
  · rintro ⟨q,hq⟩
    refine ⟨reverseTime q,?_⟩
    simpa only [reverseConfigurationPath_apply,reverseTime_reverse] using hq

def pathVisitedSites {S : Type*} {n : ℕ} (L : Length) (v : S → Torus L)
    (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L) : Finset S := by
  classical
  exact A.filter (fun a ↦ pathVisitsBall L 12 (v a) i ω)

@[simp] lemma pathVisitedSites_reverse {S : Type*} {n : ℕ} (L : Length)
    (v : S → Torus L) (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L v A i (reverseConfigurationPath n L ω)=pathVisitedSites L v A i ω := by
  classical
  simp only [pathVisitedSites,pathVisitsBall_reverse]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FreeVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

def visitCount {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t : ℝ) (X : Configuration n L) (w : CoordinatePaths n) : ℕ :=
  (pathVisitedSites L (siteCenter L) A i (freeTrajectory n L t w X)).card

attribute [local irreducible] freeTrajectory pathVisitedSites

end HardSphere.FreeVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ExpNatTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.FreeVisits

def expTailBound (C : ℕ) (η : ℝ) (a : ℝ≥0∞) : ℝ≥0∞ :=
  1+(ENNReal.ofReal (Real.exp (η*(C:ℝ)))+
       ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*(1-ENNReal.ofReal (Real.exp (-1)))⁻¹

end HardSphere.FreeVisits

end

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice
attribute [local irreducible] freeTrajectory pathVisitedSites

def visitWeight {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t η : ℝ) (X : Configuration n L) (w : CoordinatePaths n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (η*(visitCount L A i t X w:ℝ)))

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FreeVisitTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice

attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

def visitStartDistance {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (X : Configuration n L) : ℝ := by
  classical
  exact spatialSiteDistance L (A.image (siteCenter L)) (X i)

end HardSphere.FreeVisits

namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

def visitDefect {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t η : ℝ) (X : Configuration n L) (D : Set (CoordinatePaths n)) (w : CoordinatePaths n) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (Real.exp (η*(if w∈D then (visitCount L A i t X w:ℝ) else 0))-1)

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CubicMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def diameterRatio {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) := intervalDiameter 0 1 ω/r

def cubicCost {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) := (1+diameterRatio r ω)^3

lemma diameterRatio_continuous (L : Length) (r : ℝ) : Continuous (diameterRatio (L:=L) r) :=
  (intervalDiameter_continuous L 0 1).div_const r
lemma cubicCost_continuous (L : Length) (r : ℝ) : Continuous (cubicCost (L:=L) r) :=
  (continuous_const.add (diameterRatio_continuous L r)).pow 3

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_DiameterTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def MeshRegular {L : Length} (m : ℕ) (r R C : ℝ) (ω : ConfigurationPath 1 L) : Prop :=
  (∀ j : Fin m, diameterRatio r (meshSegment j ω) ≤ R) ∧
  (∑j : Fin m,cubicCost r (meshSegment j ω)) ≤ C*(m:ℝ)

lemma meshRegular_measurable {L : Length} (m : ℕ) (r R C : ℝ) :
    MeasurableSet {ω : ConfigurationPath 1 L | MeshRegular m r R C ω} := by
  change MeasurableSet ({ω : ConfigurationPath 1 L | ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R} ∩
    {ω | (∑j : Fin m,cubicCost r (meshSegment j ω)) ≤ C*(m:ℝ)})
  apply MeasurableSet.inter
  · have he (j : Fin m) : MeasurableSet {ω : ConfigurationPath 1 L | diameterRatio r (meshSegment j ω) ≤ R} :=
      measurableSet_le ((diameterRatio_continuous L r).comp (meshSegment_continuous L j)).measurable measurable_const
    simpa only [← Set.ofPred_forall] using MeasurableSet.iInter he
  · exact measurableSet_le (Finset.measurable_fun_sum _ (fun j _ ↦
      ((cubicCost_continuous L r).comp (meshSegment_continuous L j)).measurable)) measurable_const

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

abbrev EuclideanPath := Fin 3 → C(Time,ℝ)

def liftedDiameterMap (a b : Time) (ζ : EuclideanPath) : C(Time×Time,ℝ) :=
  ⟨fun p ↦ Real.sqrt (∑j, (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2), by
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro j _
    exact (((ζ j).continuous.comp ((intervalTime_continuous a b).comp continuous_fst)).sub
      ((ζ j).continuous.comp ((intervalTime_continuous a b).comp continuous_snd))).pow 2⟩

def liftedDiameter (a b : Time) (ζ : EuclideanPath) : ℝ := ‖liftedDiameterMap a b ζ‖

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def EndpointRegular {L : Length} (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) : Prop :=
  intervalDiameter 0 u ω ≤ S ∧ intervalDiameter (reverseTime u) 1 ω ≤ S

def Regular {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) : Prop :=
  MeshRegular m r R C ω ∧ EndpointRegular u S ω

lemma regular_measurable {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) :
    MeasurableSet {ω : ConfigurationPath 1 L | Regular m r R C u S ω} := by
  change MeasurableSet ({ω | MeshRegular m r R C ω} ∩
    ({ω | intervalDiameter 0 u ω ≤ S} ∩ {ω | intervalDiameter (reverseTime u) 1 ω ≤ S}))
  exact (meshRegular_measurable m r R C).inter
    ((measurableSet_le (intervalDiameter_continuous L 0 u).measurable measurable_const).inter
      (measurableSet_le (intervalDiameter_continuous L (reverseTime u) 1).measurable measurable_const))

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CenteredCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

def centeredCell (L : Length) (c : Torus L) : Set (Torus L) :=
  {x | ∀ j, ((AddCircle.equivIco L.val (-L.val/2)) (x j-c j)).val ∈ Ico (-1/2:ℝ) (1/2)}

lemma centeredCell_measurable (L : Length) (c : Torus L) : MeasurableSet (centeredCell L c) := by
  simp only [centeredCell,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_Ico.preimage (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco L.val (-L.val/2)).measurable.comp
      ((measurable_pi_apply j).sub measurable_const)))

noncomputable def centeredCount {n : ℕ} (L : Length) (c : Torus L) (X : Configuration n L) : ℕ :=
  by classical exact (Finset.univ.filter (fun i ↦ X i∈centeredCell L c)).card

end
end HardSphere.CellOrbital

namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

def gridCenter {K : ℕ} (L : Length) (v : Fin 3 → Fin K) : Torus L :=
  fun j ↦ ((v j:ℝ) : AddCircle L.val)

end
end HardSphere.CellOrbital

end
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
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CellPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace HardSphere.CellOrbital

def gridHome {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : Torus L) : Fin 3→Fin K :=
  fun j ↦ unitIndex hL (x j+(1/2:ℝ))

lemma gridHome_measurable {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) : Measurable (gridHome hL) := by
  exact Measurable.of_eval (fun j ↦ (measurable_unitIndex hL).comp ((measurable_pi_apply j).add_const _))

end HardSphere.CellOrbital

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Allocation (m : ℕ) (I : Type*) := Option (Fin m ↪ I)
instance allocationMeasurable (m : ℕ) : MeasurableSpace (Allocation m I) := ⊤
instance allocationSingletons (m : ℕ) : MeasurableSingletonClass (Allocation m I) := ⟨fun _ ↦ trivial⟩

end HardSphere.Sampling

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local irreducible] torusDistance

def Confined {L : Length} (v : Torus L) (ω : ConfigurationPath 1 L) : Prop :=
  ∀s : Time,torusDistance L (ω s 0) v≤10

lemma confined_closed {L : Length} (v : Torus L) : IsClosed {ω | Confined v ω} := by
  simp only [Confined,ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_le _ continuous_const
  exact (torusDistance_continuous_pair L).comp (f:=fun ω : ConfigurationPath 1 L ↦ (ω s 0,v)) (by fun_prop)

def EndpointEligible {N K : ℕ} {L : Length} (v : Fin 3→Fin K) (s₀ : ℝ)
    (Y Z : Configuration N L) (i : Fin N) : Prop :=
  Y i∈centeredCell L (gridCenter L v) ∧
  torusDistance L (Z i) (gridCenter L v)≤3 ∧
  ∀j,j≠i→s₀<torusDistance L (Y i) (Y j) ∧ s₀<torusDistance L (Z i) (Z j)

def Eligible {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) (i : Fin N) (ω : ConfigurationPath N L) : Prop :=
  EndpointEligible v s₀ (ω 0) (ω 1) i ∧
  PathCutoff.Regular m r R C u S (onePathAt i ω) ∧ Confined (gridCenter L v) (onePathAt i ω)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def centerMap : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousLinearMap.id ℝ _ - (ContinuousMap.evalCLM ℝ (1:Time)).smulRight linearPath

@[simp] lemma centerMap_apply (f : C(Time,ℝ)) (s : Time) :
    centerMap f s=f s-(s:ℝ)*f 1 := by
  change f s-f 1*(s:ℝ)=_
  ring

def bridgeRemainder (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (suffixTime u) - (ContinuousMap.evalCLM ℝ u).smulRight (1-linearPath)

@[simp] lemma bridgeRemainder_apply (u : Time) (f : C(Time,ℝ)) (s : Time) :
    bridgeRemainder u f s=f (suffixTime u s)-(1-(s:ℝ))*f u := by
  change f (suffixTime u s)-f u*(1-(s:ℝ))=_
  ring

end HardSphere.Wiener

namespace HardSphere
open Wiener

def reconstructCoordinates (N : ℕ) (p : (Direction N → ℝ)×CoordinatePaths N) : CoordinatePaths N :=
  fun j ↦ p.1 j • linearPath+p.2 j

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking
abbrev Point := Fin 3 → ℝ
def square (x : Point) : ℝ := ∑j,x j^2
def kernel (b : ℝ) (x : Point) : ℝ := Real.exp (-b*square x)
def cube (q : Point) (δ : ℝ) : Set Point := Icc (fun j ↦ q j-δ) (fun j ↦ q j+δ)

end HardSphere.GaussianPacking

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking
abbrev Noise := Fin 3 → C(Time,ℝ)
def law : Measure Noise := Measure.pi (fun _ ↦ bridgeLaw)
instance instIsProbabilityMeasureNoiseLaw : IsProbabilityMeasure law := by unfold law; infer_instance

def eval (s : Time) (β : Noise) : Point := fun j ↦ β j s
def remainder (s : Time) (β : Noise) : Noise := fun j ↦ bridgeRemainder s (β j)

def variance (s : Time) : ℝ≥0 := Real.toNNReal ((s:ℝ)-(s:ℝ)^2)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def normCubeMean : ℝ := ∫w : C(Time,ℝ),‖w‖^3 ∂wiener

end HardSphere.Wiener

end

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def prefixSize (u : Time) (β : Noise) : ℝ := ∑j,‖prefixMap u (β j)‖

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

def density (b : ℝ) (x : Point) : ℝ := (Real.sqrt (b/Real.pi))^3*kernel b x

def packingConstant : ℝ := 8*Real.exp 3*(Real.sqrt 2)^3

def gaussianDensity (q : Point) (v : ℝ≥0) (x : Point) : ℝ := ∏j,gaussianPDFReal (q j) v (x j)

end HardSphere.GaussianPacking

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def mean (y u : Point) (s : Time) : Point := fun j ↦ (1-(s:ℝ))*y j+(s:ℝ)*u j
def leg (t : ℝ) (y u : Point) (β : Noise) : C(Time,Point) :=
  ⟨fun s j ↦ mean y u s j+Real.sqrt (2*t)*β j s,by unfold mean; fun_prop⟩

def legVariance (t : ℝ) (s : Time) : ℝ≥0 := (NNReal.mk ((Real.sqrt (2*t))^2) (sq_nonneg _))*variance s

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking
instance instMeasurableSpaceContinuousMapElemRealTimePoint : MeasurableSpace C(Time,Point) := borel _
instance instBorelSpaceContinuousMapElemRealTimePoint : BorelSpace C(Time,Point) := ⟨rfl⟩

def center (β : C(Time,ℝ)) : C(Time,ℝ) := β-β 0 • (1-linearPath)-β 1 • linearPath
@[fun_prop] lemma center_continuous : Continuous center := by unfold center; fun_prop
def pinned (β : Noise) : Noise := fun j ↦ center (β j)

def leftTime (s : Time) : Time := ⟨min (2*(s:ℝ)) 1,by
  constructor
  · exact le_min (mul_nonneg (by norm_num) s.property.1) zero_le_one
  · exact min_le_right _ _⟩
def rightTime (s : Time) : Time := ⟨max (2*(s:ℝ)-1) 0,by
  constructor
  · exact le_max_right _ _
  · apply max_le ?_ zero_le_one
    linarith [s.property.2]⟩
@[fun_prop] lemma leftTime_continuous : Continuous leftTime := by unfold leftTime; fun_prop
@[fun_prop] lemma rightTime_continuous : Continuous rightTime := by unfold rightTime; fun_prop

def midpointTime : Time := ⟨1/2,by norm_num⟩

def trialPath (t : ℝ) (y z : Point) (u : Point) (β : Noise×Noise) : C(Time,Point) :=
  ⟨fun s ↦ leg t y u (pinned β.1) (leftTime s)+
    leg t z u (pinned β.2) (reverseTime (rightTime s))-u,by
    apply Continuous.sub _ continuous_const
    apply Continuous.add
    · exact (leg t y u (pinned β.1)).continuous.comp leftTime_continuous
    · exact (leg t z u (pinned β.2)).continuous.comp (reverseTime.continuous.comp rightTime_continuous)⟩

@[fun_prop] lemma trialPath_continuous (t : ℝ) (y z : Point) :
    Continuous (fun p : Point×(Noise×Noise) ↦ trialPath t y z p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (Point×(Noise×Noise))×Time ↦ fun j ↦
    (mean y p.1.1 (leftTime p.2) j+Real.sqrt (2*t)*center (p.1.2.1 j) (leftTime p.2))+
    (mean z p.1.1 (reverseTime (rightTime p.2)) j+Real.sqrt (2*t)*center (p.1.2.2 j) (reverseTime (rightTime p.2)))-p.1.1 j)
  unfold mean
  have hl := leftTime_continuous
  have hr := reverseTime.continuous.comp rightTime_continuous
  have hc := center_continuous
  fun_prop

def trialKernel (t : ℝ) (y z : Point) : Kernel Point C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod (Kernel.const Point (law.prod law))).map
    (fun p ↦ trialPath t y z p.1 p.2)
instance trialKernel_markov (t : ℝ) (y z : Point) : IsMarkovKernel (trialKernel t y z) := by
  unfold trialKernel
  exact Kernel.IsMarkovKernel.map _ (trialPath_continuous t y z).measurable

lemma trialKernel_apply (t : ℝ) (y z u : Point) : trialKernel t y z u=
    (law.prod law).map (trialPath t y z u) := by
  rw [trialKernel,Kernel.map_apply _ (trialPath_continuous t y z).measurable,Kernel.prod_apply,
    Kernel.deterministic_apply,Kernel.const_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_map (trialPath_continuous t y z).measurable (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id u)))]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def fluctuation (t r : ℝ) (u : Time) (β : Noise) : ℝ := Real.sqrt (2*t)/r*prefixSize u β

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def segmentHit (t : ℝ) (y v : Point) (s w : Time) (c : Time → Point) (r C : ℝ) : Set Noise :=
  {β | ‖leg t y v β s-v‖≤C ∧ ∃q : Time,(q:ℝ)≤(w:ℝ) ∧ ‖leg t y v β (suffixTime s q)-c q‖ ≤ r}

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_IncrementMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def incrementMap (s u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) := (prefixMap u).comp (suffixMap s)
@[simp] lemma incrementMap_apply (s u : Time) (f : C(Time,ℝ)) (q : Time) :
    incrementMap s u f q=f (suffixTime s (prefixTime u q))-f s := rfl

end HardSphere.Wiener

namespace HardSphere.Bridge
open Wiener GaussianPacking

def incrementSize (s u : Time) (β : Noise) : ℝ := ∑j,‖incrementMap s u (β j)‖

def incrementFluctuation (t r : ℝ) (s w : Time) (β : Noise) : ℝ := Real.sqrt (2*t)/r*incrementSize s w β

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_AffineVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

def affine (s : ℝ) (c : Point) (x : Point) : Point := fun j ↦ s*x j+c j

end HardSphere.GaussianPacking

namespace HardSphere.Bridge
open Wiener GaussianPacking

def uniformSegmentHit (t : ℝ) (y : Point) (s w : Time) (c : Time → Point) (r : ℝ) (B : Set Point) : Set (Noise×Point) :=
  {p | p.2∈B ∧ ∃q : Time,(q:ℝ) ≤ (w:ℝ) ∧ ‖leg t y p.2 p.1 (suffixTime s q)-c q‖ ≤ r}

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SegmentMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def jointSegmentHit (t : ℝ) (y : Point) (s w : Time) (c : C(Time,Point)) (r C : ℝ) : Set (Point×Noise) :=
  {p | p.2∈segmentHit t y p.1 s w c r C}

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SegmentSimplify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def hitConstant : ℝ := 256*(packingConstant+1)*(8+3072*normCubeMean)

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_MeshLegHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def combinedSegmentHit (t : ℝ) (y : Point) (B : Set Point) (s w : Time)
    (c : C(Time,Point)) (r C : ℝ) : Set (Point×Noise) :=
  if (s:ℝ)≤1/2 then jointSegmentHit t y s w c r C
  else Prod.swap ⁻¹' uniformSegmentHit t y s w c r B

end HardSphere.Bridge

namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

def meshRemainder {n : ℕ} (j : Fin n) : Time :=
  ⟨1/((n:ℝ)-(j:ℝ)),by
    have hj : (1:ℝ)≤(n:ℝ)-(j:ℝ) := by
      have h : (j:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show j.val+1≤n by omega)
      linarith
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hj⟩⟩

end HardSphere.Bridge

namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def meshHitUnion {n : ℕ} (I : Finset (Fin n)) (t : ℝ) (y : Point) (B : Set Point)
    (c : Fin n→C(Time,Point)) (r C : ℝ) : Set (Point×Noise) :=
  ⋃j∈I,combinedSegmentHit t y B (meshTime j 0) (meshRemainder j) (c j) r C

end HardSphere.Bridge

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeHighMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def normPowerMean (p : ℕ) : ℝ := ∫w : C(Time,ℝ),‖w‖^p ∂wiener

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def pathCoordinates (ω : C(Time,Point)) : Noise := fun j ↦ ⟨fun s ↦ ω s j,by fun_prop⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeWiener
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def rawNoise (w : CoordinatePaths 1) : Noise := fun j ↦ w (0,j)
def centeredNoise (w : CoordinatePaths 1) : Noise := fun j ↦ centerMap (rawNoise w j)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def rawPath (t : ℝ) (y : Point) (w : CoordinatePaths 1) : EuclideanPath := fun j ↦
  ⟨fun s ↦ y j+Real.sqrt (2*t)*w (0,j) s,by fun_prop⟩

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def legCost {n : ℕ} (t r : ℝ) (y u : Point) (j : Fin n) (β : Noise) : ℝ :=
  (1+liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r)^3

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def legMeshRatio {n : ℕ} (t r : ℝ) (y u : Point) (j : Fin n) (β : Noise) : ℝ :=
  liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeStrongRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def LegMeshRegular (n : ℕ) (t r R C : ℝ) (y u : Point) (β : Noise) : Prop :=
  (∀j : Fin n,legMeshRatio t r y u j β≤R) ∧
   (∑j : Fin n,legCost t r y u j β)≤C*(n:ℝ)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def projectCurve (L : Length) (f : C(Time,Point)) : ConfigurationPath 1 L :=
  ⟨fun s _ j ↦ (f s j:AddCircle L.val),by fun_prop⟩
lemma projectCurve_continuous (L : Length) : Continuous (projectCurve L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(Time,Point)×Time ↦ fun _ : Fin 1 ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
  fun_prop

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_BridgeScaleTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def scaleMoment (p : ℕ) (t r : ℝ) (s w : Time) : ℝ :=
  (3^p*3*2^(p+1))*(Real.sqrt (2*t*(1-(s:ℝ))*(w:ℝ))/r)^p*normPowerMean p

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

abbrev projectPoint (L : Length) (y : Point) : Torus L := fun j ↦ (y j : AddCircle L.val)

def nearestLift (L : Length) (v : Point) (x : Torus L) : Point := fun j ↦
  (((AddCircle.equivIco L.val (-L.val/2)) (x j-(v j : AddCircle L.val))).val)+v j

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def TrialConfined (L : Length) (v : Point) (f : C(Time,Point)) : Prop :=
  ∀s : Time,‖f s-v‖≤10 ∧ torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10

def TrialCutoff (L : Length) (n : ℕ) (r R C : ℝ) (w : Time) (S : ℝ) (v : Point) (f : C(Time,Point)) : Prop :=
  Regular (n+n) r R C (prefixTime midpointTime w) S (projectCurve L f) ∧ TrialConfined L v f

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

def meshLocalLift {L : Length} {n : ℕ} (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (v : Point) (j : Fin n) : C(Time,Point) :=
  ⟨fun q k ↦ ζ k (suffixTime (meshTime j 0) q)-ζ k (meshTime j 0)+nearestLift L v (ω (meshTime j 0) 0) k,
    continuous_pi fun k ↦ (((ζ k).continuous.comp (suffixTime (meshTime j 0)).continuous).sub continuous_const).add continuous_const⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_CollisionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

def torusLegHit {L : Length} (t : ℝ) (y v : Point) (B : Set Point) (ω : ConfigurationPath 1 L)
    (r C h : ℝ) : Set (Point×Noise) :=
  {p | p.1∈B ∧ (∀s : Time,‖leg t y p.1 p.2 s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y p.1 p.2 s)) (projectPoint L v)≤10) ∧
    (∀s : Time,‖leg t y p.1 p.2 s-p.1‖≤ C) ∧
    ∃s : Time,h≤(s:ℝ) ∧ torusDistance L (projectPoint L (leg t y p.1 p.2 s)) (ω s 0)≤ r}

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def endpointIndex (n : ℕ) (t h : ℝ) : ℕ := ⌊(n:ℝ)*h/(4*t)⌋₊

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_EarlyTorusHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking
attribute [local irreducible] torusDistance

def earlyTorusHit {L : Length} (t : ℝ) (y z v : Point) (ω : ConfigurationPath 1 L)
    (r C h : ℝ) : Set Noise :=
  {β | (∀s : Time,‖leg t y z β s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10) ∧
    (∀s : Time,‖leg t y z β s-z‖≤C) ∧
    ∃s : Time,h≤(s:ℝ) ∧ (s:ℝ)≤1/2 ∧ torusDistance L (projectPoint L (leg t y z β s)) (ω s 0) ≤ r}

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeSplit
attribute [-instance] _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.trialKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def bridgePrefix (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) := centerMap.comp (prefixMap u)
@[simp] lemma bridgePrefix_apply (u : Time) (f : C(Time,ℝ)) (s : Time) :
    bridgePrefix u f s=f (prefixTime u s)-(s:ℝ)*f u := by
  simp only [bridgePrefix,ContinuousLinearMap.comp_apply,centerMap_apply,prefixMap_apply]
  congr 2
  congr 1
  apply Subtype.ext
  simp [prefixTime]

end HardSphere.Wiener

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeAssemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener
open Bridge (leftTime rightTime midpointTime leftTime_continuous rightTime_continuous)

def assembleBridge (p : (ℝ×C(Time,ℝ))×C(Time,ℝ)) : C(Time,ℝ) :=
  ⟨fun s ↦ ((leftTime s:ℝ)-(rightTime s:ℝ))*p.1.1+
    p.1.2 (leftTime s)+p.2 (rightTime s),by
    have hl := leftTime_continuous
    have hr := rightTime_continuous
    fun_prop⟩

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def bridgeReverse : C(Time,ℝ) →L[ℝ] C(Time,ℝ) := ContinuousMap.compCLM ℝ ℝ reverseTime

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def midpointNoise : Measure Point := Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (Real.toNNReal (1/4:ℝ)))
instance instIsProbabilityMeasurePointMidpointNoise : IsProbabilityMeasure midpointNoise := by unfold midpointNoise; infer_instance

def assembleNoise (p : (Point×Noise)×Noise) : Noise := fun j ↦ assembleBridge
  ((p.1.1 j,Real.sqrt (1/2:ℝ) • p.1.2 j),Real.sqrt (1/2:ℝ) • p.2 j)

def reverseNoise (β : Noise) : Noise := fun j ↦ bridgeReverse (β j)

def midpointPoint (t : ℝ) (y z v : Point) : Point := fun j ↦ (y j+z j)/2+Real.sqrt (4*t)*v j

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def midpointLaw (t : ℝ) (y z : Point) : Measure Point := midpointNoise.map (midpointPoint t y z)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

def densityLower (b C : ℝ) : ℝ := (Real.sqrt (b/Real.pi))^3*Real.exp (-b*(3*C^2))

end HardSphere.GaussianPacking

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_TrialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]

def successKernel (κ : Kernel U X) (S : Set X) (hS : MeasurableSet S) : Kernel U X where
  toFun u := (κ u S)⁻¹ • (κ u).restrict S
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    simp only [Measure.smul_apply,Measure.restrict_apply hB,smul_eq_mul]
    exact (κ.measurable_coe hS).inv.mul (κ.measurable_coe (hB.inter hS))

def pairedFactor (μ : Measure U) (κ : Kernel U X) (η : Kernel U Y)
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    [IsFiniteKernel κ] [IsFiniteKernel η] : Measure (U×(X×Y)) :=
  μ.compProd ((successKernel κ S hS).prod (successKernel η T hT))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_ParameterSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]

def parameterSuccessKernel (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) : Kernel E X where
  toFun e := (κ e (Prod.mk e ⁻¹' S))⁻¹ • (κ e).restrict (Prod.mk e ⁻¹' S)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    simp only [Measure.smul_apply,Measure.restrict_apply hB,smul_eq_mul]
    have hm := Kernel.measurable_kernel_prodMk_left (κ:=κ) hS
    have hi := Kernel.measurable_kernel_prodMk_left (κ:=κ)
      ((MeasurableSet.univ.prod hB).inter hS)
    apply hm.inv.mul
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    ext e
    congr 1
    ext x
    simp

lemma parameterSuccessKernel_apply (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) (e : E) :
    parameterSuccessKernel κ S hS e=
      (κ e (Prod.mk e ⁻¹' S))⁻¹ • (κ e).restrict (Prod.mk e ⁻¹' S) := rfl

lemma parameterSuccessKernel_mass_le (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) (e : E) :
    parameterSuccessKernel κ S hS e univ ≤ 1 := by
  simp only [parameterSuccessKernel_apply,Measure.smul_apply,
    Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

instance parameterSuccessKernel_finite (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) : IsFiniteKernel (parameterSuccessKernel κ S hS) :=
  ⟨1,by simp,parameterSuccessKernel_mass_le κ S hS⟩

end HardSphere.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_LocalReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def targetUniform (A : Set Point) : Measure Point := (volume A)⁻¹ • volume.restrict A

def midpointLower (t C : ℝ) : ℝ≥0∞ := ENNReal.ofReal (densityLower ((2*t)⁻¹) C)

def individualReference (t : ℝ) (y z : Point) (S : Set C(Time,Point)) : Measure C(Time,Point) :=
  ((law.map (leg (2*t) y z)) S)⁻¹ • (law.map (leg (2*t) y z)).restrict S

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def pairedTrialLaw (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Measure (C(Time,Point)×(Point×C(Time,Point))) :=
  (pairedFactor (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT).map
    (fun p ↦ (p.2.1,(p.1,p.2.2)))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialHitMeasure
attribute [-instance] _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def trialCutoffHit {L : Length} (n : ℕ) (t r R C S : ℝ) (y z v : Point)
    (B : Set Point) (w : Time) (ω : ConfigurationPath 1 L) : Set (Point×(Noise×Noise)) :=
  {p | p.1∈B ∧ TrialCutoff L n r R C w S v (trialPath t y z p.1 p.2) ∧
    ∃s : Time,torusDistance L (projectPoint L (trialPath t y z p.1 p.2 s)) (ω s 0) ≤ r}

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def GoodLeg (n : ℕ) (t r R C S : ℝ) (y u : Point) (w : Time) (β : Noise) : Prop :=
  LegMeshRegular n t r R C y u β ∧
    liftedDiameter 0 w (pathCoordinates (leg t y u β))≤S ∧
    incrementFluctuation t 1 0 1 β≤1/3

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSuccess
attribute [-instance] _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

def TrialCollision {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) (f : C(Time,Point)) : Prop :=
  ∃s : Time,torusDistance L (projectPoint L (f s)) (ω s 0) ≤ r

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

structure LocalCheck (X : ι → Type*) [∀ i, MeasurableSpace (X i)] where
  support : Finset ι
  nonempty : support.Nonempty
  arity : support.card ≤ 2
  pass : (∀ i, X i) → Prop
  measurable_pass : MeasurableSet {x | pass x}
  depends : ∀ x y, (∀ i ∈ support, x i = y i) → (pass x ↔ pass y)

variable {C : Type*} [Fintype C] (checks : C → LocalCheck X)

def retainedEvent (s : Finset ι) : Set (∀ i, X i) :=
  {x | ∀ c, (checks c).support ⊆ s → (checks c).pass x}

def insertionEvent (s : Finset ι) (i : ι) : Set (∀ i, X i) :=
  {x | ∀ c, (checks c).support ⊆ insert i s →
    ¬ (checks c).support ⊆ s → (checks c).pass x}

def checkWeight (s : Finset ι) : (∀ i, X i) → ℝ≥0∞ :=
  (retainedEvent checks s).indicator (fun _ ↦ 1)

def checkNormalizer (μ : ∀ i, Measure (X i)) (s : Finset ι)
    (x : ∀ i, X i) : ℝ≥0∞ := lmarginal μ s (checkWeight checks s) x

def SeparatedChecks (s t : Finset ι) : Prop :=
  ∀ c, (checks c).support ⊆ s ∪ t →
    (checks c).support ⊆ s ∨ (checks c).support ⊆ t

end HardSphere.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_JointCollision
attribute [-instance] _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma jointCollision_closed {L : Length} (r : ℝ) :
    IsClosed {p : C(Time,Point)×C(Time,Point) | TrialCollision r (projectCurve L p.2) p.1} := by
  let E : Set ((C(Time,Point)×C(Time,Point))×Time) :=
    {p | torusDistance L (projectPoint L (p.1.1 p.2)) (projectPoint L (p.1.2 p.2)) ≤ r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f:=fun p : (C(Time,Point)×C(Time,Point))×Time ↦
      (projectPoint L (p.1.1 p.2),projectPoint L (p.1.2 p.2)))
    unfold projectPoint
    fun_prop
  convert isClosedMap_fst_of_compactSpace E hE using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(p,s),hs,rfl⟩,fun ⟨⟨q,s⟩,hs,hq⟩ ↦ by
    change q=p at hq
    subst q
    exact ⟨s,hs⟩⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_FiberNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]

def fiberRestrict (κ : Kernel W V) [IsSFiniteKernel κ] (C : Set (W×V)) : Kernel W V :=
  κ.withDensity (fun w v ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))

def fiberNormalize (κ : Kernel W V) [IsSFiniteKernel κ] (C : Set (W×V)) : Kernel W V where
  toFun w := (fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ((fiberRestrict κ C).measurable_coe MeasurableSet.univ).inv.mul
      ((fiberRestrict κ C).measurable_coe hB)

instance fiberNormalize_finite (κ : Kernel W V) [IsSFiniteKernel κ] (C : Set (W×V)) :
    IsFiniteKernel (fiberNormalize κ C) := ⟨1,by simp,fun w ↦ by
      change ((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) univ≤1
      rw [Measure.smul_apply,smul_eq_mul]
      exact ENNReal.inv_mul_le_one _⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ProductExpose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]

def blockGlue (p : I→Prop) [DecidablePred p]
    (z : (E×(∀i : {i // ¬p i},X i))×(∀i : {i // p i},X i)) : E×(∀i,X i) :=
  (z.1.1,(MeasurableEquiv.piEquivPiSubtypeProd X p).symm (z.2,z.1.2))

def blockEvent (p : I→Prop) [DecidablePred p] (B : Set (E×(∀i,X i))) := blockGlue p ⁻¹' B

def exposedLaw (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] (B : Set (E×(∀i,X i))) : Measure (E×(∀i : {i // ¬p i},X i)) :=
  (μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i)).withDensity
    (fun w ↦ fiberRestrict (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (blockEvent p B) w univ)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ProductNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

def conditionedMeasure {A : Type*} [MeasurableSpace A] (μ : Measure A) (S : Set A) : Measure A :=
  (μ S)⁻¹ • μ.restrict S

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E I J : Type*} [MeasurableSpace E] [Fintype I] [Fintype J]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]

def flagEvent (f : ∀i,E×X i→Bool) (b : I→Bool) : Set (E×(∀i,X i)) :=
  {z | ∀i,f i (z.1,z.2 i)=b i}

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GroundBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener

abbrev BridgeEndpoints (N : ℕ) (L : Length) := (Direction N→ℝ)×Configuration N L

def endpointBridgePath (N : ℕ) (L : Length) (t : ℝ)
    (p : BridgeEndpoints N L×CoordinatePaths N) : ConfigurationPath N L :=
  freeTrajectory N L t (reconstructCoordinates N (p.1.1,p.2)) p.1.2

def bridgeEnd (N : ℕ) (L : Length) (t : ℝ) (e : BridgeEndpoints N L) : Configuration N L :=
  fun i j ↦ e.2 i j+((Real.sqrt (2*t)*e.1 (i,j):ℝ):AddCircle L.val)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Comparison Bridge

def labelBridgePath (N : ℕ) (L : Length) (t : ℝ) (p : BridgeEndpoints N L×(Fin N→Bridge.Noise)) : ConfigurationPath N L :=
  endpointBridgePath N L t (p.1,fun j ↦ p.2 j.1 j.2)

def labelInteraction (N : ℕ) (L : Length) (a t : ℝ) : Set (BridgeEndpoints N L×(Fin N→Bridge.Noise)) :=
  labelBridgePath N L t ⁻¹' staysAllowed N L a

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Bridge GaussianPacking

def labelStartLift {N : ℕ} {L : Length} (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  representative N L e.2 i

def labelEndLift {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  fun j ↦ labelStartLift e i j+Real.sqrt (2*t)*e.1 (i,j)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I E : Type*} [Fintype I] [MeasurableSpace E]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

def pairEvent (C : ∀i j,X i→X j→Prop) : Set (∀i,X i) :=
  {v | ∀i j,i≠j→C i j (v i) (v j)}

def frozenCompatible (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (w : ∀i : {i // ¬p i},X i) : Prop :=
  ∀i j : {i // ¬p i},i≠j→C i j (w i) (w j)

def individualFiber (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (flag : ∀i,X i→Bool) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i) (i : {i // p i}) : Set (X i) :=
  {v | flag i v=b i ∧ ∀j : {j // ¬p j},C i j v (w j) ∧ C j i (w j) v}

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_WeightedExpose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E J A : Type*} [MeasurableSpace E] [MeasurableSpace J] [MeasurableSpace A]
  [Fintype J] [Fintype A] [MeasurableSingletonClass A]

def allocationBase (μ : Measure E) (κ : Kernel (E×J) A) (b : J) (a : A) : Measure E :=
  μ.withDensity (fun e ↦ κ (e,b) {a})

instance allocationBase_sfinite (μ : Measure E) [SFinite μ]
    (κ : Kernel (E×J) A) (b : J) (a : A) : SFinite (allocationBase μ κ b a) := by
  unfold allocationBase
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

attribute [local instance] Classical.propDecidable

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge CellOrbital Sampling Comparison
attribute [local instance] Classical.propDecidable

def ownPath {N : ℕ} {L : Length} (i : Fin N) (t : ℝ)
    (p : BridgeEndpoints N L×Bridge.Noise) : ConfigurationPath 1 L :=
  onePathAt i (labelBridgePath N L t (p.1,fun _ ↦ p.2))

def ownEligible {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (p : BridgeEndpoints N L×Bridge.Noise) : Prop :=
  ∃v : Fin 3→Fin K, EndpointEligible v s₀ p.1.2 (bridgeEnd N L t p.1) i ∧
    PathCutoff.Regular m r R C u S (ownPath i t p) ∧ Confined (gridCenter L v) (ownPath i t p)

def eligibilityFlag {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (p : BridgeEndpoints N L×Bridge.Noise) : Bool :=
  decide (ownEligible (K:=K) m r R C S s₀ t u i p)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_FiniteKernelPi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HardSphere.Comparison

theorem exists_kernel_pi_fin {α : Type*} [MeasurableSpace α] (n : ℕ)
    (β : Fin n → Type*) [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] :
    ∃ η : Kernel α (∀ i, β i), IsFiniteKernel η ∧
      ∀ a, η a = Measure.pi (fun i ↦ κ i a) := by
  induction n with
  | zero =>
    let η : Kernel α (∀ i, β i) := Kernel.deterministic (fun _ i ↦ Fin.elim0 i) measurable_const
    refine ⟨η, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), fun a ↦ ?_⟩
    rw [Kernel.deterministic_apply, Measure.pi_of_empty (fun i ↦ κ i a) (fun i ↦ Fin.elim0 i)]
  | succ n ih =>
    obtain ⟨η, hη, heq⟩ := ih (fun i ↦ β ((0 : Fin (n+1)).succAbove i))
      (fun i ↦ κ ((0 : Fin (n+1)).succAbove i))
    let := hη
    let e := (MeasurableEquiv.piFinSuccAbove β 0).symm
    refine ⟨((κ 0).prod η).map e, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), fun a ↦ ?_⟩
    rw [Kernel.map_apply _ e.measurable, Kernel.prod_apply, heq]
    exact ((measurePreserving_piFinSuccAbove (fun i ↦ κ i a) 0).symm
      (MeasurableEquiv.piFinSuccAbove β 0)).map_eq

theorem exists_kernel_pi {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (β : ι → Type*) [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] :
    ∃ η : Kernel α (∀ i, β i), IsFiniteKernel η ∧
      ∀ a, η a = Measure.pi (fun i ↦ κ i a) := by
  classical
  let e := (Fintype.equivFin ι).symm
  obtain ⟨η, hη, heq⟩ := exists_kernel_pi_fin (Fintype.card ι)
    (fun i ↦ β (e i)) (fun i ↦ κ (e i))
  let := hη
  let E := MeasurableEquiv.piCongrLeft β e
  refine ⟨η.map E, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), fun a ↦ ?_⟩
  rw [Kernel.map_apply _ E.measurable, heq]
  exact (measurePreserving_piCongrLeft (fun i ↦ κ i a) e).map_eq

noncomputable def finiteKernelPi {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] : Kernel α (∀ i, β i) :=
  (exists_kernel_pi β κ).choose

instance instIsFiniteKernelForallFiniteKernelPi {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] :
    IsFiniteKernel (finiteKernelPi κ) := (exists_kernel_pi β κ).choose_spec.1

section CoordinateKernels
variable {ι : Type*} [Fintype ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

def coordinateKernel : Kernel (∀ i, X i) (∀ i, Z i) :=
  finiteKernelPi (fun i ↦ (κ i).comap (fun x ↦ x i) (measurable_pi_apply (i : ι)))

instance instIsFiniteKernelForallCoordinateKernel : IsFiniteKernel (coordinateKernel κ) := by
  unfold coordinateKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CoordinateKernels
end HardSphere.Comparison

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

abbrev GridAllocation (N K q : ℕ) := (Fin 3→Fin K)→Allocation q (Fin N)

def groupPosition (M G : ℕ) (g : Fin G) : Fin M↪Fin (G*M) where
  toFun k := ⟨g.val*M+k.val, by
    have hg : g.val+1≤G := g.isLt
    have hk := k.isLt
    calc
      g.val*M+k.val < g.val*M+M := Nat.add_lt_add_left hk _
      _ = (g.val+1)*M := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ G*M := Nat.mul_le_mul_right M hg⟩
  inj' := by intros a b h; apply Fin.ext; have he := congrArg Fin.val h; dsimp at he; omega

def groupAt {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) (v : Fin 3→Fin K) : Finset (Fin N) :=
  match a v with
  | none => ∅
  | some f => Finset.univ.image (fun k ↦ f (groupPosition M G g k))

def groupUnion {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) : Finset (Fin N) :=
  Finset.univ.biUnion (groupAt g a)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AuxiliaryChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory

section AuxiliaryMarginals
variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

def auxiliaryChecks (x : ∀ i, X i) (c : C) : LocalCheck Z where
  support := (checks c).support
  nonempty := (checks c).nonempty
  arity := (checks c).arity
  pass := fun z ↦ (checks c).pass (fun i ↦ (x i, z i))
  measurable_pass := (by fun_prop : Measurable (fun z : ∀ i, Z i ↦ fun i ↦ (x i,z i)))
    (checks c).measurable_pass
  depends := by
    intro z w h
    apply (checks c).depends
    intro i hi
    exact Prod.ext rfl (h i hi)

def auxiliaryDensity (s : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) : ℝ≥0∞ :=
  checkNormalizer (auxiliaryChecks checks x) (fun i ↦ κ i (x i)) s z

end AuxiliaryMarginals

section OverlapProducts
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

def densityProduct (s : Finset ι) (g : ∀ i, X i → ℝ≥0∞) (x : ∀ i, X i) : ℝ≥0∞ :=
  ∏ i ∈ s, g i (x i)

end OverlapProducts

section ConditionalNormalizers
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)

def UniformInsertionOn (μ : ∀ i, Measure (X i)) (a : ℝ≥0∞) (r : Finset ι) : Prop :=
  ∀ i ∈ r, ∀ (s : Finset ι), i ∉ s → ∀ x : ∀ j, X j,
    a ≤ ∫⁻ y, (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
      (Function.update x i y) ∂μ i

def partialNormalizer (μ : ∀ i, Measure (X i)) (s o : Finset ι)
    (x : ∀ i, X i) : ℝ≥0∞ := lmarginal μ s (checkWeight checks (s ∪ o)) x

end ConditionalNormalizers

variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

def conditionalDensity (s o : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) : ℝ≥0∞ :=
  lmarginal (fun i ↦ κ i (x i)) s
    (fun v ↦ checkWeight checks (s ∪ o) (fun i ↦ (x i,v i))) z

end HardSphere.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RestrictedMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X : Type*} [MeasurableSpace X]

def subtypeConditional (P : Measure X) (S : Set X) : Measure S :=
  (P S)⁻¹ • P.comap Subtype.val

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

def referenceOn (t : ℝ) (y z : Point) (S : Set C(Time,Point)) : Measure S :=
  subtypeConditional (law.map (leg (2*t) y z)) S

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

def fixedEndpoints (y z : Point) : Set C(Time,Point) := {f | f 0=y ∧ f 1=z}

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ConfinedLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

def permittedPath {J : Type*} {L : Length} (n : ℕ) (r R Creg S : ℝ)
    (w : Time) (y z v : Point) (F : J → ConfigurationPath 1 L) : Set C(Time,Point) :=
  {f | Regular n r R Creg w S (projectCurve L f) ∧ TrialConfined L v f ∧
    f∈fixedEndpoints y z ∧ ∀j,¬TrialCollision r (F j) f}

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff Comparison CellOrbital
attribute [local instance] Classical.propDecidable

def frozenPaths {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L)
    (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise) : {i // ¬p i} → ConfigurationPath 1 L :=
  fun j ↦ projectCurve L (leg t (labelStartLift e j) (labelEndLift t e j) (w j))

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking Comparison CellOrbital
attribute [local instance] Classical.propDecidable

def physicalMutual {I : Type*} {L : Length} (r : ℝ) : Set (I → C(Time,Point)) :=
  pairEvent (fun _ _ f g ↦ ¬TrialCollision (L:=L) r (projectCurve L g) f)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice

def torusNear (K R : ℕ) (x y : DiscreteTorus K) : Prop :=
  ∃ d : Vertex, (∀ i, |d i|≤R) ∧ ∀ i, y i=x i+(d i : ZMod K)

lemma torusNear_mono {K R S : ℕ} {x y : DiscreteTorus K} (hRS : R≤S) (h : torusNear K R x y) :
    torusNear K S x y := by
  obtain ⟨d,hd,he⟩ := h
  exact ⟨d,fun i ↦ (hd i).trans (by exact_mod_cast hRS),he⟩

open MeasureTheory

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BoxWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

def boxWeight (m : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2*((m:ℝ)+1))^3)

attribute [local irreducible] torusDistance

lemma volume_torus (L : Length) : (volume : Measure (Torus L)) Set.univ = ENNReal.ofReal (L.val^3) := by
  rw [volume_pi,Measure.pi_univ]
  simp only [AddCircle.measure_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.ofReal_pow L.property.le]

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SiteCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open MeasureTheory Set Filter HardSphere.Lattice

def siteCube {K : ℕ} [NeZero K] (v : DiscreteTorus K) : CubeCell K :=
  (⟨(v 0).val, ZMod.val_lt _⟩, ⟨(v 1).val, ZMod.val_lt _⟩, ⟨(v 2).val, ZMod.val_lt _⟩)

lemma siteCube_injective {K : ℕ} [NeZero K] : Function.Injective (siteCube (K := K)) := by
  intro v w h
  have h0 := congrArg (fun z : CubeCell K ↦ z.1.val) h
  have h1 := congrArg (fun z : CubeCell K ↦ z.2.1.val) h
  have h2 := congrArg (fun z : CubeCell K ↦ z.2.2.val) h
  funext j
  fin_cases j <;> apply ZMod.val_injective <;> assumption

def siteCubeEmbedding {K : ℕ} [NeZero K] : DiscreteTorus K ↪ CubeCell K :=
  ⟨siteCube, siteCube_injective⟩

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathPermutation
attribute [-instance] _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.trialKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma permuteConfiguration_continuous {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n)) :
    Continuous (permuteConfiguration (L:=L) σ) := by
  unfold permuteConfiguration
  fun_prop

def permuteConfigurationPath {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n))
    (ω : ConfigurationPath n L) : ConfigurationPath n L :=
  ⟨fun s ↦ permuteConfiguration σ (ω s), (permuteConfiguration_continuous σ).comp ω.continuous⟩

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_SelectedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace HardSphere

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Wiener

@[simp] lemma onePathAt_permute {n : ℕ} {L : Length} (σ : Equiv.Perm (Fin n))
    (i : Fin n) (ω : ConfigurationPath n L) :
    onePathAt i (permuteConfigurationPath σ ω)=onePathAt (σ i) ω := rfl

@[simp] lemma onePathAt_split_left {m n : ℕ} {L : Length} (i : Fin m)
    (ω : ConfigurationPath (m+n) L) :
    onePathAt i (splitConfigurationPath m n L ω).1=onePathAt (Fin.castAdd n i) ω := rfl

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_SingleVisitDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

def singleVisitDefect {K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (η : ℝ) (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath 1 L) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (Real.exp (η*(if ω∈D then ((pathVisitedSites L (siteCenter L) A 0 ω).card:ℝ) else 0))-1)

end HardSphere.FreeVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_InteractingVisits
attribute [-instance] _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.trialKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener BathSlice _root_.OAI.HardSphere.Lattice CellOrbital

def shiftPath {n : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath n L) : ConfigurationPath n L :=
  ⟨fun s i ↦ ω s i+c,by fun_prop⟩

@[simp] lemma shiftPath_neg {n : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath n L) :
    shiftPath c (shiftPath (-c) ω)=ω := by
  ext s i j
  simp [shiftPath]

@[simp] lemma shiftPath_reverse {n : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath n L) :
    shiftPath c (reverseConfigurationPath n L ω)=reverseConfigurationPath n L (shiftPath c ω) := rfl

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitCounts
attribute [-instance] _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.trialKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital PathCutoff FreeVisits
attribute [local instance] Classical.propDecidable

@[simp] lemma intervalTime_zero_one (s : Time) : intervalTime 0 1 s=s := by
  apply Subtype.ext
  simp [intervalTime]

def longVisitors {N : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ pathVisitsBall L 12 c i ω ∧ 1 < intervalDiameter 0 1 (onePathAt i ω))

def visitors {N : ℕ} {L : Length} (c : Torus L) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ pathVisitsBall L 12 c i ω)

structure Certificate {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) : Prop where
  low : ell*D≤(centeredCount L (gridCenter L v) (ω 0):ℝ)
  closeY : ((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ)<θ*D
  closeZ : ((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ)<θ*D
  visit : ((visitors (gridCenter L v) ω).card:ℝ)≤H*D
  regular : ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)
  long : ((longVisitors (gridCenter L v) ω).card:ℝ)<θ*D

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SupplyIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance
attribute [local instance] Classical.propDecidable

def SuccessExcept {L : Length} {N : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin N → ConfigurationPath 1 L) (i : Fin N) : Set C(Time,Point) :=
  {f | TrialCutoff L n r R C w S v f ∧ ∀j,j≠i → ¬TrialCollision r (ω j) f}

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_TrialScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def scalarTrialRemainder (Cn M c a b D : ℝ) : ℝ :=
  Cn*D^2*(3*M)*Real.exp (-(c/46656)*D^(1/6:ℝ))+
    Real.exp (-(a/8)*D)+3*M*Real.exp (-c*D^(1/6:ℝ))+
    3981312*b⁻¹^2*D^(-(1/3):ℝ)*normPowerMean 2

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialScalarBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison
attribute [local instance] Classical.propDecidable

def StrongExcept {L : Length} {N : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (y z v : Point) (ω : Fin N → ConfigurationPath 1 L) (label : Fin N)
    (B : Fin 7 → Set Point) : Prop :=
  ∀j, ENNReal.ofReal (99/100:ℝ)≤(volume.restrict (B j))
    {u | ENNReal.ofReal (9/10:ℝ)≤trialKernel t y z u (SuccessExcept n r R C S w v ω label)}

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital GaussianPacking
attribute [local instance] Classical.propDecidable

def exposedAnchorLift {N K : ℕ} {L : Length} (hL : L.val = (K : ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  nearestLift L (labelStartLift e i) (gridCenter L (gridHome hL (e.2 i)))

def ExposedPhysicalIdentity {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool)
    (w : BridgeEndpoints N L × ({i // ¬p i} → Bridge.Noise)) : Prop :=
(conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
  {β | blockGlue p (w,β) ∈ labelInteraction N L r (2*t) ∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b}).map
  (fun β (i : {i // p i}) ↦
    leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i)) =
conditionedMeasure (Measure.pi fun i : {i // p i} ↦
  individualReference t (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
    (permittedPath m r R C S u (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
      (exposedAnchorLift hL w.1 i) (frozenPaths (2*t) w.1 p w.2)))
  (physicalMutual (L:=L) r)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_ExposedTrials
attribute [-instance] _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma trialPath_all_continuous (t : ℝ) :
    Continuous (fun p : (Point×(Point×Point))×(Noise×Noise) ↦
      trialPath t p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((Point×(Point×Point))×(Noise×Noise))×Time ↦ fun j ↦
    (mean p.1.1.1 p.1.1.2.2 (leftTime p.2) j+Real.sqrt (2*t)*center (p.1.2.1 j) (leftTime p.2))+
    (mean p.1.1.2.1 p.1.1.2.2 (reverseTime (rightTime p.2)) j+
      Real.sqrt (2*t)*center (p.1.2.2 j) (reverseTime (rightTime p.2)))-p.1.1.2.2 j)
  unfold mean
  have hl := leftTime_continuous
  have hr := reverseTime.continuous.comp rightTime_continuous
  have hc := center_continuous
  fun_prop

def exposedTrialKernel (t : ℝ) : Kernel (Point×(Point×Point)) C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod
      (Kernel.const (Point×(Point×Point)) (law.prod law))).map
    (fun p ↦ trialPath t p.1.1 p.1.2.1 p.1.2.2 p.2)

instance exposedTrialKernel_markov (t : ℝ) : IsMarkovKernel (exposedTrialKernel t) := by
  unfold exposedTrialKernel
  exact Kernel.IsMarkovKernel.map _ (trialPath_all_continuous t).measurable

lemma exposedTrialKernel_apply (t : ℝ) (y z u : Point) :
    exposedTrialKernel t (y,z,u)=trialKernel t y z u := by
  rw [exposedTrialKernel,Kernel.map_apply _ (trialPath_all_continuous t).measurable,
    Kernel.prod_apply,Kernel.deterministic_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (trialPath_all_continuous t).measurable
      (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id (y,z,u)))),
    trialKernel_apply]
  rfl

lemma trialCollision_joint_closed {L : Length} (r : ℝ) :
    IsClosed {p : ConfigurationPath 1 L×C(Time,Point) | TrialCollision r p.1 p.2} := by
  let E : Set ((ConfigurationPath 1 L×C(Time,Point))×Time) :=
    {p | torusDistance L (projectPoint L (p.1.2 p.2)) (p.1.1 p.2 0) ≤ r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f := fun p : (ConfigurationPath 1 L×C(Time,Point))×Time ↦
      (projectPoint L (p.1.2 p.2),p.1.1 p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : (ConfigurationPath 1 L×C(Time,Point))×Time ↦
        fun j : Fin 3 ↦ (p.1.2 p.2 j:AddCircle L.val))
      fun_prop
    · fun_prop
  convert isClosedMap_fst_of_compactSpace E hE using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(p,s),hs,rfl⟩,fun ⟨⟨q,s⟩,hs,hq⟩ ↦ by
    change q=p at hq
    subst q
    exact ⟨s,hs⟩⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_ParameterPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E U X Y : Type*} [MeasurableSpace E] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]

def parameterPairedKernel (Q : Kernel E U) [IsFiniteKernel Q]
    (κ : Kernel (E×U) X) (η : Kernel (E×U) Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y))
    (hS : MeasurableSet S) (hT : MeasurableSet T) : Kernel E (U×(X×Y)) :=
  Q.compProd ((parameterSuccessKernel κ S hS).prod (parameterSuccessKernel η T hT))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_ExposedPhysicalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

def parameterTrialKernel (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    Kernel (E×Point) C(Time,Point) :=
  (exposedTrialKernel t).comap (fun p ↦ (y p.1,z p.1,p.2))
    ((hy.comp measurable_fst).prodMk ((hz.comp measurable_fst).prodMk measurable_snd))
instance parameterTrialKernel_markov (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    IsMarkovKernel (parameterTrialKernel t y z hy hz) := inferInstanceAs
      (IsMarkovKernel ((exposedTrialKernel t).comap _ _))
lemma parameterTrialKernel_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (e : E) (u : Point) : parameterTrialKernel t y z hy hz (e,u)=trialKernel t (y e) (z e) u :=
  exposedTrialKernel_apply _ _ _ _

def exposedSuccess (S : Set (E×C(Time,Point))) : Set ((E×Point)×C(Time,Point)) :=
  (fun p ↦ (p.1.1,p.2)) ⁻¹' S
lemma exposedSuccess_measurable {S : Set (E×C(Time,Point))} (hS : MeasurableSet S) :
    MeasurableSet (exposedSuccess S) := hS.preimage (by fun_prop)

def exposedPairedTrialKernel (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z')
    (S T : Set (E×C(Time,Point))) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Kernel E (C(Time,Point)×(Point×C(Time,Point))) :=
  (parameterPairedKernel Q (parameterTrialKernel t y z hy hz) (parameterTrialKernel t y' z' hy' hz')
    (exposedSuccess S) (exposedSuccess T) (exposedSuccess_measurable hS) (exposedSuccess_measurable hT)).map
    (fun p ↦ (p.2.1,(p.1,p.2.2)))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ExposedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

lemma leg_all_continuous (t : ℝ) :
    Continuous (fun p : (Point×Point)×Noise ↦ leg t p.1.1 p.1.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((Point×Point)×Noise)×Time ↦ fun j ↦
    mean p.1.1.1 p.1.1.2 p.2 j+Real.sqrt (2*t)*p.1.2 j p.2)
  unfold mean
  fun_prop

def exposedBridgeKernel (t : ℝ) : Kernel (Point×Point) C(Time,Point) :=
  ((Kernel.deterministic id measurable_id).prod (Kernel.const (Point×Point) law)).map
    (fun p ↦ leg t p.1.1 p.1.2 p.2)
instance exposedBridgeKernel_markov (t : ℝ) : IsMarkovKernel (exposedBridgeKernel t) := by
  unfold exposedBridgeKernel
  exact Kernel.IsMarkovKernel.map _ (leg_all_continuous t).measurable

def parameterBridgeKernel (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    Kernel E C(Time,Point) := (exposedBridgeKernel t).comap (fun e ↦ (y e,z e)) (hy.prodMk hz)
instance parameterBridgeKernel_markov (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) :
    IsMarkovKernel (parameterBridgeKernel t y z hy hz) := inferInstanceAs
      (IsMarkovKernel ((exposedBridgeKernel t).comap _ _))

def parameterIndividualReference (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) : Kernel E C(Time,Point) :=
  parameterSuccessKernel (parameterBridgeKernel (2*t) y z hy hz) S hS
instance parameterIndividualReference_finite (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) :
    IsFiniteKernel (parameterIndividualReference t y z hy hz S hS) := inferInstanceAs
      (IsFiniteKernel (parameterSuccessKernel _ _ _))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SupportedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def supportedPair (ρ : Measure (X×Y)) (S : Set X) (T : Set Y) : Measure (S×T) :=
  ρ.comap (Prod.map Subtype.val Subtype.val)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PeriodShift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

def shiftPath (c : Point) (f : C(Time,Point)) : C(Time,Point) :=
  f+ContinuousMap.const _ c
@[fun_prop] lemma shiftPath_continuous (c : Point) : Continuous (shiftPath c) := by
  unfold shiftPath
  fun_prop

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma trialConfined_joint_closed (L : Length) :
    IsClosed {p : Point × C(Time,Point) | TrialConfined L p.1 p.2} := by
  have he : {p : Point × C(Time,Point) | TrialConfined L p.1 p.2} =
      ⋂ s : Time, {p : Point × C(Time,Point) |
        ‖p.2 s-p.1‖≤10 ∧ torusDistance L (projectPoint L (p.2 s)) (projectPoint L p.1)≤10} := by
    ext p
    simp only [TrialConfined, mem_ofPred_eq, mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro s
  change IsClosed ({p : Point × C(Time,Point) | ‖p.2 s-p.1‖≤(10:ℝ)} ∩
    {p | torusDistance L (projectPoint L (p.2 s)) (projectPoint L p.1)≤(10:ℝ)})
  apply IsClosed.inter
  · apply isClosed_le _ continuous_const
    fun_prop
  · apply isClosed_le _ continuous_const
    unfold torusDistance projectPoint
    fun_prop

variable {E : Type*} [MeasurableSpace E]

def exposedPeriodPair (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z y' z' : E → Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point)
    (S U : Set (E × C(Time,Point))) (hS : MeasurableSet S) (hU : MeasurableSet U) :
    Kernel E (C(Time,Point) × C(Time,Point)) :=
  (exposedPairedTrialKernel Q t y z (fun e ↦ y' e+c) (fun e ↦ z' e+c)
    hy hz (hy'.add measurable_const) (hz'.add measurable_const) S U hS hU).map
    (fun p ↦ (p.1, shiftPath (-c) p.2.2))

end HardSphere.Bridge
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

abbrev PhysicalDatum (N K M G : ℕ) (L : Length) :=
  Configuration N L × Configuration N L × (Fin N → Bool) ×
    GridAllocation N K (G*M) × (Fin N → ConfigurationPath 1 L)

def datumSelected {N K M G : ℕ} {L : Length} (g : Fin G)
    (d : PhysicalDatum N K M G L) : Finset (Fin N) := groupUnion g d.2.2.2.1

def datumHome {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (d : PhysicalDatum N K M G L) (i : Fin N) : Fin 3 → Fin K := gridHome hL (d.1 i)

def anchorPoint {K : ℕ} (v : Fin 3 → Fin K) : Point := fun j ↦ ((v j).val:ℝ)

def datumStart {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (d : PhysicalDatum N K M G L) (i : Fin N) : Point :=
  nearestLift L (anchorPoint (datumHome hL d i)) (d.1 i)

def datumEnd {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (d : PhysicalDatum N K M G L) (i : Fin N) : Point :=
  nearestLift L (anchorPoint (datumHome hL d i)) (d.2.1 i)

lemma datumHome_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ datumHome hL d i) :=
  (gridHome_measurable hL).comp ((measurable_pi_apply i).comp measurable_fst)

lemma datumAnchor_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ anchorPoint (datumHome hL d i)) :=
  (measurable_of_countable (anchorPoint (K:=K))).comp (datumHome_measurable hL i)

lemma nearestLift_measurable (L : Length) :
    Measurable (fun p : Point × Torus L ↦ nearestLift L p.1 p.2) := by
  apply Measurable.of_eval
  intro j
  exact (measurable_subtype_coe.comp ((AddCircle.measurableEquivIco L.val (-L.val/2)).measurable.comp
    (((measurable_pi_apply j).comp measurable_snd).sub
      (AddCircle.measurable_mk'.comp ((measurable_pi_apply j).comp measurable_fst))))).add
    ((measurable_pi_apply j).comp measurable_fst)

lemma datumStart_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ datumStart hL d i) := by
  unfold datumStart
  exact (nearestLift_measurable L).comp
    ((datumAnchor_measurable hL i).prodMk ((measurable_pi_apply i).comp measurable_fst))

lemma datumEnd_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (i : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ datumEnd hL d i) := by
  unfold datumEnd
  exact (nearestLift_measurable L).comp
    ((datumAnchor_measurable hL i).prodMk ((measurable_pi_apply i).comp measurable_snd.fst))

lemma datumFrozen_measurable {N K M G : ℕ} {L : Length} (j : Fin N) :
    Measurable (fun d : PhysicalDatum N K M G L ↦ d.2.2.2.2 j) :=
  (measurable_pi_apply j).comp (measurable_snd.snd.snd.snd)

attribute [local irreducible] TrialCollision

lemma datumFrozen_collision_measurable {N K M G : ℕ} {L : Length}
    (j : Fin N) (r : ℝ) :
    MeasurableSet {p : PhysicalDatum N K M G L × C(Time,Point) |
      TrialCollision (L:=L) r (p.1.2.2.2.2 j) p.2} :=
  by
  have hm : Measurable (fun p : PhysicalDatum N K M G L × C(Time,Point) ↦
      (p.1.2.2.2.2 j,p.2)) :=
    (((datumFrozen_measurable (K:=K) (M:=M) (G:=G) (L:=L) j).comp measurable_fst).prodMk measurable_snd)
  have H : MeasurableSet {q : ConfigurationPath 1 L × C(Time,Point) | TrialCollision (L:=L) r q.1 q.2} :=
    (trialCollision_joint_closed (L:=L) r).measurableSet
  exact hm H

def datumPermitted {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) :
    Set (PhysicalDatum N K M G L × C(Time,Point)) :=
  {p | Regular m r R C u S (projectCurve L p.2) ∧
    TrialConfined L (anchorPoint (datumHome hL p.1 i)) p.2 ∧
    p.2∈fixedEndpoints (datumStart hL p.1 i) (datumEnd hL p.1 i) ∧
    ∀j, j∉datumSelected g p.1 → ¬TrialCollision (L:=L) r (p.1.2.2.2.2 j) p.2}

lemma datumPermitted_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) :
    MeasurableSet (datumPermitted (M:=M) hL g m r R C S u i) := by
  apply ((regular_measurable m r R C u S).preimage
    ((projectCurve_continuous L).measurable.comp measurable_snd)).inter
  apply ((trialConfined_joint_closed L).measurableSet.preimage
    (((datumAnchor_measurable hL i).comp measurable_fst).prodMk measurable_snd)).inter
  apply MeasurableSet.inter
  · exact (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      ((datumStart_measurable hL i).comp measurable_fst)).inter
      (measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_snd)
        ((datumEnd_measurable hL i).comp measurable_fst))
  simp only [imp_iff_not_or,not_not]
  change MeasurableSet {p : PhysicalDatum N K M G L × C(Time,Point) | ∀j,
    j∈datumSelected g p.1 ∨ ¬TrialCollision (L:=L) r (p.1.2.2.2.2 j) p.2}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.union
  · exact (measurable_fst.snd.snd.snd.fst)
      ((Set.to_countable {a : GridAllocation N K (G*M) | j∈groupUnion g a}).measurableSet)
  · exact (datumFrozen_collision_measurable (K:=K) (M:=M) (G:=G) (L:=L) j r).compl

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_PartialPhysicalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I E : Type*} [DecidableEq I] [Fintype E]
  {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (checks : E → LocalCheck V)
  (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]

def insertionFiberEvent (s o : Finset I) : Set ((∀i,V i)×(∀i : s,V i)) :=
  {p | Function.updateFinset p.1 s p.2∈retainedEvent checks (s∪o)}

def insertedLaw (s o : Finset I) (ξ : Measure (∀i,V i)) [SFinite ξ] :
    Measure ((∀i,V i)×(∀i : s,V i)) :=
  ξ.compProd (fiberNormalize (Kernel.const _ (Measure.pi (fun i : s ↦ μ i)))
    (insertionFiberEvent checks s o))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ConditionalLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory

section CancellationEstimate
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {R C D : Type*} [Fintype R] [Fintype C] [Fintype D]
  (reference : R → LocalCheck X)
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

def conditionalLikelihood (s o : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) : ℝ≥0∞ :=
  (partialNormalizer reference μ s o x /
    partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i))) *
      conditionalDensity checks κ s o x z

end CancellationEstimate

end HardSphere.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ExactFiberLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I : Type*} [DecidableEq I] {X Z : I → Type*}
  [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]
  {E R : Type*} [Fintype E] [Fintype R]
  (checks : E → LocalCheck (fun i ↦ X i×Z i))
  (reference : R → LocalCheck X)
  (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
  (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]

def proposalFiber (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i) : Measure (∀i : s,X i×Z i) :=
  conditionedMeasure (Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))
    {p | Function.updateFinset (fun i ↦ (x i,z i)) s p∈retainedEvent checks (s∪o)}

def referenceFiber (s o : Finset I) (x : ∀i,X i) : Measure (∀i : s,X i) :=
  conditionedMeasure (Measure.pi (fun i : s ↦ μ i))
    {p | Function.updateFinset x s p∈retainedEvent reference (s∪o)}

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FrozenChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

def freezeOutside (U : Finset I) (x y : ∀i,X i) : ∀i,X i :=
  fun i ↦ if i∈U then y i else x i
omit [Fintype I] in
lemma freezeOutside_measurable (U : Finset I) (x : ∀i,X i) : Measurable (freezeOutside U x) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈U
  · simpa only [freezeOutside,ite_eq_left hi] using (measurable_pi_apply i)
  · simp only [freezeOutside,ite_eq_right hi]
    exact measurable_const

def FrozenCheckIndex (checks : C → LocalCheck X) (U : Finset I) :=
  {c : C // ((checks c).support∩U).Nonempty}

instance instFintypeFrozenCheckIndex (checks : C → LocalCheck X) (U : Finset I) : Fintype (FrozenCheckIndex checks U) :=
  by
    classical
    unfold FrozenCheckIndex
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def frozenChecks (checks : C → LocalCheck X) (U : Finset I) (x : ∀i,X i) :
    FrozenCheckIndex checks U → LocalCheck X := fun c ↦ {
  support := (checks c.val).support∩U
  nonempty := c.property
  arity := (Finset.card_le_card Finset.inter_subset_left).trans (checks c.val).arity
  pass := fun y ↦ (checks c.val).pass (freezeOutside U x y)
  measurable_pass := (checks c.val).measurable_pass.preimage (freezeOutside_measurable U x)
  depends := by
    intro y z hyz
    apply (checks c.val).depends
    intro i hi
    by_cases hu : i∈U
    · simp only [freezeOutside,ite_eq_left hu]
      exact hyz i (Finset.mem_inter.mpr ⟨hi,hu⟩)
    · simp only [freezeOutside,ite_eq_right hu]
}

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ReferenceResample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
instance conditioned_finite {A : Type*} [MeasurableSpace A] (μ : Measure A) (S : Set A) :
    IsFiniteMeasure (conditionedMeasure μ S) := by
  constructor
  simp only [conditionedMeasure,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) (by norm_num)

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C R : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype R]
  {X Z : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]

def proposalEvent (checks : C→LocalCheck (fun i ↦ X i×Z i)) (s o : Finset I)
    (z : ∀i,Z i) : Set ((∀i,X i)×(∀i:s,X i×Z i)) :=
  {p | Function.updateFinset (fun i ↦ (p.1 i,z i)) s p.2∈retainedEvent checks (s∪o)}

def proposalKernel (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) : Kernel (∀i,X i) (∀i:s,X i×Z i) :=
  fiberNormalize (Kernel.const _ (Measure.pi fun i:s ↦ (μ i).compProd (κ i)))
    (proposalEvent checks s o z)

instance proposalKernel_finite (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) : IsFiniteKernel (proposalKernel checks μ κ s o z) :=
  inferInstanceAs (IsFiniteKernel (fiberNormalize _ _))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_NearLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def canonicalShift {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  anchorPoint (gridHome hL (e.2 i))-exposedAnchorLift hL e i

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_GlobalExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

def blockExpose (p : I → Prop) (z : E × (∀i,X i)) :
    E × (∀i : {i // ¬p i},X i) := (z.1,fun i ↦ z.2 i)

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
attribute [local instance] Classical.propDecidable

def fillOutside (p : I → Prop) (x₀ : ∀i,X i) (x : ∀i : {i // ¬p i},X i) : ∀i,X i :=
  fun i ↦ if h : p i then x₀ i else x ⟨i,h⟩

end HardSphere.Comparison

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CoarsePhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def datumIndividualReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N) :
    Kernel (PhysicalDatum N K M G L) C(Time,Point) :=
  parameterIndividualReference t (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (datumStart_measurable hL i) (datumEnd_measurable hL i)
    (datumPermitted hL g m r R C S u i) (datumPermitted_measurable hL g m r R C S u i)

instance datumIndividualReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N) :
    IsFiniteKernel (datumIndividualReference (M:=M) hL g m r R C S t u i) :=
  inferInstanceAs (IsFiniteKernel (parameterIndividualReference ..))

def datumGroupReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    Kernel (PhysicalDatum N K M G L) ({i // i∈groupUnion g a}→C(Time,Point)) :=
  fiberNormalize (finiteKernelPi (fun i : {i // i∈groupUnion g a} ↦
    datumIndividualReference hL g m r R C S t u i))
    (Prod.snd ⁻¹' physicalMutual (L:=L) r)

instance datumGroupReference_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) :
    IsFiniteKernel (datumGroupReference hL g a m r R C S t u) :=
  inferInstanceAs (IsFiniteKernel (fiberNormalize ..))

end HardSphere.Groups

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTargets
attribute [-instance] _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def unitTarget (c : Point) : Set Point :=
  Set.pi Set.univ (fun j ↦ Set.Ico (c j-1/2) (c j+1/2))

lemma unitTarget_measurable (c : Point) : MeasurableSet (unitTarget c) :=
  MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ ↦ measurableSet_Ico)

lemma unitTarget_volume (c : Point) : volume (unitTarget c)=1 := by
  rw [unitTarget, volume_pi_pi]
  simp only [Real.volume_Ico]
  have he (j : Fin 3) : c j+1/2-(c j-1/2)=(1:ℝ) := by ring
  simp only [he]
  norm_num

def targetStep (j : Fin 7) : Point :=
  if j.val=0 then 0 else fun k ↦
    if k.val=(j.val-1)/2 then (if (j.val-1)%2=0 then 1 else -1) else 0

def datumSuccess {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) :
    PhysicalDatum N K M G L × Point → ℝ≥0∞ := fun p ↦
  trialKernel t (datumStart hL p.1 i) (datumEnd hL p.1 i) p.2
    (Prod.mk p.1 ⁻¹' datumPermitted hL g m r R C S u i)

lemma datumSuccess_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) :
    Measurable (datumSuccess (M:=M) hL g m t r R C S u i) := by
  let κ := parameterTrialKernel t (fun d : PhysicalDatum N K M G L ↦ datumStart hL d i)
    (fun d ↦ datumEnd hL d i) (datumStart_measurable hL i) (datumEnd_measurable hL i)
  have h := Kernel.measurable_kernel_prodMk_left (κ:=κ)
    (exposedSuccess_measurable (datumPermitted_measurable (M:=M) hL g m r R C S u i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  obtain ⟨d,U⟩ := p
  simp only [κ,datumSuccess,parameterTrialKernel_apply]
  rfl

def datumTarget {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (j : Fin 7) :
    Set (PhysicalDatum N K M G L × Point) :=
  {p | p.2∈unitTarget (anchorPoint (datumHome hL p.1 i)+targetStep j) ∧
    ENNReal.ofReal (9/10:ℝ)≤datumSuccess hL g m t r R C S u i p}

lemma datumTarget_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (j : Fin 7) :
    MeasurableSet (datumTarget (M:=M) hL g m t r R C S u i j) := by
  simp only [datumTarget,Set.ofPred_and]
  apply MeasurableSet.inter
  · have he : {p : PhysicalDatum N K M G L × Point |
        p.2∈unitTarget (anchorPoint (datumHome hL p.1 i)+targetStep j)} =
        ⋂k : Fin 3, {p | anchorPoint (datumHome hL p.1 i) k+targetStep j k-1/2≤p.2 k ∧
        p.2 k<anchorPoint (datumHome hL p.1 i) k+targetStep j k+1/2} := by
      ext p
      simp [unitTarget]
    rw [he]
    apply MeasurableSet.iInter
    intro k
    have hc : Measurable (fun p : PhysicalDatum N K M G L × Point ↦ anchorPoint (datumHome hL p.1 i) k) :=
      ((measurable_pi_apply k).comp ((datumAnchor_measurable (M:=M) hL i).comp measurable_fst))
    exact (measurableSet_le ((hc.add_const _).sub_const _)
      ((measurable_pi_apply k).comp measurable_snd)).inter
        (measurableSet_lt ((measurable_pi_apply k).comp measurable_snd)
          ((hc.add_const _).add_const _))
  · exact measurableSet_le measurable_const (datumSuccess_measurable hL g m t r R C S u i)

def datumAccessible {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (d : PhysicalDatum N K M G L) : Prop :=
  ∀j : Fin 7, ENNReal.ofReal (99/100:ℝ)≤
    volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j)

lemma datumAccessible_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) :
    MeasurableSet {d : PhysicalDatum N K M G L | datumAccessible hL g m t r R C S u i d} := by
  unfold datumAccessible
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply measurableSet_le measurable_const
  exact Kernel.measurable_kernel_prodMk_left (κ:=Kernel.const (PhysicalDatum N K M G L) volume)
    (datumTarget_measurable hL g m t r R C S u i j)

def datumAccessibleLabels {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (v : Fin 3 → Fin K)
    (d : PhysicalDatum N K M G L) : Finset (Fin N) :=
  (datumSelected g d).filter fun i ↦ datumHome hL d i=v ∧ datumAccessible hL g m t r R C S u i d

lemma datumAccessibleLabels_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (v : Fin 3 → Fin K) :
    Measurable (datumAccessibleLabels (N:=N) (M:=M) hL g m t r R C S u v) := by
  apply measurable_to_countable'
  intro f
  change MeasurableSet {d | _ = f}
  have he : {d : PhysicalDatum N K M G L | datumAccessibleLabels hL g m t r R C S u v d=f} =
      ⋂i : Fin N, {d | (i∈datumSelected g d ∧ datumHome hL d i=v ∧
        datumAccessible hL g m t r R C S u i d) ↔ i∈f} := by
    ext d
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    rw [Finset.ext_iff]
    simp only [datumAccessibleLabels,Finset.mem_filter]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  have hs : MeasurableSet {d : PhysicalDatum N K M G L | i∈datumSelected g d} := by
    exact (measurable_snd.snd.snd.fst)
      ((Set.to_countable {a : GridAllocation N K (G*M) | i∈groupUnion g a}).measurableSet)
  have hh := hs.inter ((measurableSet_eq_fun (datumHome_measurable hL i) (measurable_const (a:=v))).inter
    (datumAccessible_measurable hL g m t r R C S u i))
  by_cases hi : i∈f
  · simpa only [hi,iff_true,Set.ofPred_and] using hh
  · simpa only [hi,iff_false,Set.ofPred_and,←Set.compl_ofPred] using hh.compl

def datumBad {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time)
    (d : PhysicalDatum N K M G L) : Finset (Fin 3 → Fin K) :=
  Finset.univ.filter fun v ↦ 2*(datumAccessibleLabels hL g m t r R C S u v d).card<M

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ParameterTarget
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge HardSphere.Wiener HardSphere.GaussianPacking
variable {E : Type*} [MeasurableSpace E]

def parameterTargetKernel {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A) : Kernel E Point := by
  letI : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  exact parameterSuccessKernel (Kernel.const E (volume.restrict B)) A hA

instance parameterTargetKernel_finite {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A) :
    IsFiniteKernel (parameterTargetKernel hB A hA) := by
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  exact inferInstanceAs (IsFiniteKernel (parameterSuccessKernel (Kernel.const E (volume.restrict B)) A hA))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def routeCellPeriod {K : ℕ} (v w : Fin 3→Fin K) (j : Fin 7) : Point :=
  anchorPoint v-(anchorPoint w+targetStep j)

def vertexTarget {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) : Set (PhysicalDatum N K M G L×Point) :=
  (univ×ˢunitTarget (anchorPoint v))∩
    (datumTarget hL g m t r R C S u i 0 ∩
      (fun p ↦ (p.1,p.2-routeCellPeriod v w j)) ⁻¹'
        datumTarget hL g m t r R C S u i' j)

lemma vertexTarget_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    MeasurableSet (vertexTarget (M:=M) hL g m t r R C S u i i' v w j) :=
  (MeasurableSet.univ.prod (unitTarget_measurable _)).inter
    ((datumTarget_measurable hL g m t r R C S u i 0).inter
      ((datumTarget_measurable hL g m t r R C S u i' j).preimage
        (measurable_fst.prodMk (measurable_snd.sub measurable_const))))

def shiftedDatumPermitted {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) (c : Point) :
    Set (PhysicalDatum N K M G L×C(Time,Point)) :=
  (fun p ↦ (p.1,Bridge.shiftPath (-c) p.2)) ⁻¹' datumPermitted hL g m r R C S u i

lemma shiftedDatumPermitted_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) (c : Point) :
    MeasurableSet (shiftedDatumPermitted (M:=M) hL g m r R C S u i c) :=
  (datumPermitted_measurable hL g m r R C S u i).preimage
    (measurable_fst.prodMk ((Bridge.shiftPath_continuous (-c)).measurable.comp measurable_snd))

def vertexPair {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    Kernel (PhysicalDatum N K M G L) (C(Time,Point)×C(Time,Point)) :=
  exposedPeriodPair
    (parameterTargetKernel (B:=unitTarget (anchorPoint v)) (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
      (vertexTarget hL g m t r R C S u i i' v w j)
      (vertexTarget_measurable hL g m t r R C S u i i' v w j)) t
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (fun d ↦ datumStart hL d i') (fun d ↦ datumEnd hL d i')
    (datumStart_measurable hL i) (datumEnd_measurable hL i)
    (datumStart_measurable hL i') (datumEnd_measurable hL i') (routeCellPeriod v w j)
    (datumPermitted hL g m r R C S u i)
    (shiftedDatumPermitted hL g m r R C S u i' (routeCellPeriod v w j))
    (datumPermitted_measurable hL g m r R C S u i)
    (shiftedDatumPermitted_measurable hL g m r R C S u i' (routeCellPeriod v w j))

def vertexDensityBound (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (9/10:ℝ))⁻¹*((ENNReal.ofReal (49/50:ℝ))⁻¹*(midpointLower t 13)⁻¹)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AddedSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace HardSphere.Lattice
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

def encounterSet (e : V → V → Prop) (P Q : Finset V) : Finset (V×V) :=
  (P×ˢQ).filter fun z ↦ e z.1 z.2

end HardSphere.Lattice

namespace HardSphere.Lattice

def shellAttachment {K : ℕ} [NeZero K] (R : ℕ) (B Γ : Finset (DiscreteTorus K))
    (x : DiscreteTorus K) : Prop :=
  ∃ c∈B, torusNear K 1 c x ∧
    ∃ z∈Γ, z∈badComponent (torusRangeGraph K (R+2)) B c

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointsExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma periodicLift_internalReach {K a : ℕ} (S : Finset (DiscreteTorus K))
    {r x : Vertex} (hx : x∈periodicLift K a S r) :
    withinReach (rangeStep a) (periodicLift K a S r) r x := by
  obtain ⟨_,hp⟩ := hx
  induction hp with
  | refl => exact .refl
  | @tail u v hru huv ih =>
    exact (ih huv.1).tail ⟨⟨huv.1,hru⟩,⟨huv.2.1,hru.tail huv⟩,huv.2.2⟩

lemma exists_bad_lift {K : ℕ} [NeZero K] (hK : 2<K)
    (B : Finset (DiscreteTorus K)) (r : Vertex) (hr : torusProjection K r∈B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K r)).card<K) :
    ∃ C : Finset Vertex,
      (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r)) r ∧
      r∈C ∧ starConnected (↑C) ∧
      (∀ x∈C, torusProjection K x∈B) ∧
      (∀ c∈C, ∀ x, torusProjection K x∈B → starStep c x → x∈C) := by
  let S := badComponent (torusRangeGraph K 1) B (torusProjection K r)
  have hrS : torusProjection K r∈S := mem_own_badComponent _ _ hr
  obtain ⟨C,hC,_,_⟩ := small_periodic_lifts (a:=1) (by simpa using hK) S
    (by simpa using hsmall) (badComponent_preconnected _ _ _) r hrS
  have hrC : r∈C := by change r∈(↑C:Set Vertex); rw [hC]; exact ⟨hrS,.refl⟩
  refine ⟨C,hC,hrC,?_,?_,?_⟩
  · rw [hC]
    intro x hx y hy
    change withinReach (rangeStep 1) (periodicLift K 1 S r) x y
    exact (withinReach_symm (fun _ _ h ↦ rangeStep_symm h) (periodicLift_internalReach S hx)).trans
      (periodicLift_internalReach S hy)
  · intro x hx
    have hx' : x∈periodicLift K 1 S r := by rw [← hC]; exact hx
    exact badComponent_subset _ _ _ hx'.1
  · intro c hc x hx hcx
    have hc' : c∈periodicLift K 1 S r := by rw [← hC]; exact hc
    have hproj := rangeStep_projection (a:=1) (by simpa using hK) (show rangeStep 1 c x from hcx)
    have hstep : (badGraph (torusRangeGraph K 1) B).Adj (torusProjection K c) (torusProjection K x) :=
      ⟨badComponent_subset _ _ _ hc'.1,hx,hproj⟩
    have hxS : torusProjection K x∈S := (mem_badComponent _ _ _ _).mpr
      ⟨hx,((mem_badComponent _ _ _ _).mp hc'.1).2.trans hstep.reachable⟩
    change x∈(↑C:Set Vertex)
    rw [hC]
    exact ⟨hxS,hc'.2.tail ⟨hc'.1,hxS,hcx⟩⟩

def endpointsExterior {K : ℕ} [NeZero K] (B : Finset (DiscreteTorus K))
    (v w : Vertex) : Prop :=
  ∀ r : Vertex, torusProjection K r∈B → ∀ C : Finset Vertex,
    (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r)) r →
    v∈exterior C ∧ w∈exterior C

lemma torusRangeGraph_mono {K a b : ℕ} (hab : a≤b) :
    torusRangeGraph K a≤torusRangeGraph K b := by
  intro x y h
  exact ⟨h.1,torusNear_mono hab h.2⟩

lemma badGraph_graphMono {V : Type*} [Fintype V] [DecidableEq V] {G G' : SimpleGraph V}
    (h : G≤G') (B : Finset V) : badGraph G B≤badGraph G' B := by
  intro x y he
  exact ⟨he.1,he.2.1,h he.2.2⟩

def torusNearestGraph (K : ℕ) : SimpleGraph (DiscreteTorus K) where
  Adj x y := x≠y ∧ ∃ u v : Vertex, torusProjection K u=x ∧ torusProjection K v=y ∧ nearestStep u v
  symm := ⟨by
    intro x y h
    obtain ⟨hne,u,v,hu,hv,he⟩ := h
    exact ⟨hne.symm,v,u,hv,hu,nearestStep_symm he⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def nearestProjection {K : ℕ} (hK : 2<K) : nearestGraph →g torusNearestGraph K where
  toFun := torusProjection K
  map_rel' := by
    intro x y h
    exact ⟨short_projection_ne (a:=1) (by simpa using hK) (nearestStep_star h),x,y,rfl,rfl,h⟩

theorem periodic_good_detour {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K))
    (hsmall : ∀ z∈B, (badComponent (torusRangeGraph K 1) B z).card<K)
    (Γ : Finset Vertex) {v w : Vertex} (hvΓ : v∈Γ) (hwΓ : w∈Γ)
    (hE : endpointsExterior B v w) (hwalk : withinReach nearestStep (↑Γ) v w) :
    ∃ p : (torusNearestGraph K).Walk (torusProjection K v) (torusProjection K w),
      p.IsPath ∧ ∀ x∈p.support, x∉B ∧
        (x∈Γ.image (torusProjection K) ∨ shellAttachment R B (Γ.image (torusProjection K)) x) := by
  let roots := Γ.filter (fun r ↦ torusProjection K r∈B)
  have hex : ∀ r : roots, ∃ C : Finset Vertex,
      (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r.val)) r.val ∧
      r.val∈C ∧ starConnected (↑C) ∧
      (∀ x∈C, torusProjection K x∈B) ∧
      (∀ c∈C, ∀ x, torusProjection K x∈B → starStep c x → x∈C) := by
    intro r
    have hr := (Finset.mem_filter.mp r.property).2
    exact exists_bad_lift hK B r.val hr (hsmall _ hr)
  choose C hC using hex
  let Cs : Finset (Finset Vertex) := Finset.univ.image C
  have hCs : ∀ D∈Cs, starConnected (↑D) := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact (hC r).2.2.1
  have hbad : ∀ D∈Cs, (↑D:Set Vertex)⊆(torusProjection K) ⁻¹' (↑B) := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact (hC r).2.2.2.1
  have hmax : ∀ D∈Cs, ∀ c∈D, ∀ x∈(torusProjection K) ⁻¹' (↑B), starStep c x → x∈D := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact (hC r).2.2.2.2
  have hcover : ∀ x∈(↑Γ:Set Vertex), x∈(torusProjection K) ⁻¹' (↑B) → ∃ D∈Cs, x∈D := by
    intro x hx hxB
    let r : roots := ⟨x,Finset.mem_filter.mpr ⟨hx,hxB⟩⟩
    exact ⟨C r,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩,(hC r).2.1⟩
  have hmeet : ∀ D∈Cs, ∃ x∈(↑Γ:Set Vertex), x∈D := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact ⟨r.val,(Finset.mem_filter.mp r.property).1,(hC r).2.1⟩
  have hends : ∀ D∈Cs, v∈exterior D ∧ w∈exterior D := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact hE r.val (Finset.mem_filter.mp r.property).2 (C r) (hC r).1
  obtain ⟨q,_,hq⟩ := simple_good_detour (↑Γ) ((torusProjection K) ⁻¹' (↑B)) Cs
    hCs hbad hmax hcover hmeet hvΓ hwΓ (fun D hD ↦ (hends D hD).1)
    (fun D hD ↦ (hends D hD).2) hwalk
  let qT := q.map (nearestProjection hK)
  refine ⟨qT.toPath.val,qT.toPath.isPath,?_⟩
  intro x hx
  have hxq : x∈qT.support := qT.support_toPath_subset_support hx
  rw [SimpleGraph.Walk.support_map] at hxq
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hxq
  change torusProjection K y∉B ∧ _
  refine ⟨(hq y hy).1,?_⟩
  rcases (hq y hy).2 with hyΓ|⟨D,hD,_,hyD⟩
  · exact Or.inl (Finset.mem_image.mpr ⟨y,hyΓ,rfl⟩)
  · right
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨_,c,hc,hcy⟩ := hyD
    have hc' : c∈periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r.val)) r.val := by
      rw [← (hC r).1]; exact hc
    have hcr := ((mem_badComponent _ _ _ _).mp hc'.1).2.symm
    have hbig := hcr.mono (badGraph_graphMono (torusRangeGraph_mono (show 1≤R+2 by omega)) B)
    refine ⟨torusProjection K c,(hC r).2.2.2.1 c hc,
      (rangeStep_projection (a:=1) (by simpa using hK) hcy).2,
      torusProjection K r.val,Finset.mem_image.mpr ⟨r.val,(Finset.mem_filter.mp r.property).1,rfl⟩,?_⟩
    exact (mem_badComponent _ _ _ _).mpr ⟨(Finset.mem_filter.mp r.property).2,hbig⟩

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice

def siteIndex {K : ℕ} [NeZero K] (v : DiscreteTorus K) : Fin 3→Fin K :=
  fun j ↦ ⟨(v j).val,ZMod.val_lt _⟩

def indexSite {K : ℕ} (v : Fin 3→Fin K) : DiscreteTorus K :=
  fun j ↦ ((v j).val:ZMod K)

@[simp] lemma indexSite_siteIndex {K : ℕ} [NeZero K] (v : DiscreteTorus K) :
    indexSite (siteIndex v)=v := by
  funext j
  exact ZMod.natCast_zmod_val _

@[simp] lemma siteIndex_indexSite {K : ℕ} [NeZero K] (v : Fin 3→Fin K) :
    siteIndex (indexSite v)=v := by
  funext j
  apply Fin.ext
  change (((v j).val:ZMod K).val)=(v j).val
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (v j).isLt]

lemma intPeriod_project {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (z : ℤ) (hz : (z:ZMod K)=0) : ((z:ℝ):AddCircle L.val)=0 := by
  obtain ⟨q,hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z K).mp hz
  apply (AddCircle.coe_eq_zero_iff L.val).mpr
  refine ⟨q,?_⟩
  rw [zsmul_eq_mul,hL]
  norm_cast
  rw [hq,mul_comm]

lemma siteIndex_project_lift {K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (z : Vertex) :
    projectPoint L (anchorPoint (siteIndex (torusProjection K z)))=
      projectPoint L (fun k ↦ (z k:ℝ)) := by
  ext k
  change ((((z k:ZMod K).val:ℕ):ℝ):AddCircle L.val)=((z k:ℝ):AddCircle L.val)
  apply sub_eq_zero.mp
  rw [←AddCircle.coe_sub]
  have H := intPeriod_project hL (((z k:ZMod K).val:ℤ)-z k) (by
    simp only [Int.cast_sub,Int.cast_natCast,ZMod.natCast_zmod_val,sub_self])
  simpa only [Int.cast_sub,Int.cast_natCast] using H

lemma targetStep_positive (i : Fin 3) :
    targetStep ⟨2*i.val+1,by omega⟩=fun k ↦ if k=i then (1:ℝ) else 0 := by
  funext k
  fin_cases i <;> fin_cases k <;> norm_num [targetStep]

lemma targetStep_negative (i : Fin 3) :
    targetStep ⟨2*i.val+2,by omega⟩=fun k ↦ if k=i then (-1:ℝ) else 0 := by
  funext k
  fin_cases i <;> fin_cases k <;> norm_num [targetStep]

lemma nearest_targetStep {x y : Vertex} (h : nearestStep x y) :
    ∃ j : Fin 7,targetStep j=fun k ↦ ((y k-x k:ℤ):ℝ) := by
  obtain ⟨i,hi,hr⟩ := h
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hi with hp|hn
  · refine ⟨⟨2*i.val+2,by omega⟩,?_⟩
    rw [targetStep_negative]
    funext k
    by_cases hk : k=i
    · subst k
      simp only
      have H : y i-x i=-1 := by omega
      rw [H]; norm_num
    · simp only [ite_eq_right hk,hr k hk,sub_self,Int.cast_zero]
  · refine ⟨⟨2*i.val+1,by omega⟩,?_⟩
    rw [targetStep_positive]
    funext k
    by_cases hk : k=i
    · subst k
      simp only
      have H : y i-x i=1 := by omega
      rw [H]; norm_num
    · simp only [ite_eq_right hk,hr k hk,sub_self,Int.cast_zero]

theorem adjacent_routeCellPeriod {K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) {w v : DiscreteTorus K} (h : (torusNearestGraph K).Adj w v) :
    ∃ j : Fin 7,projectPoint L (routeCellPeriod (siteIndex v) (siteIndex w) j)=0 := by
  obtain ⟨_,x,y,hx,hy,hn⟩ := h
  obtain ⟨j,hj⟩ := nearest_targetStep hn
  refine ⟨j,?_⟩
  subst w v
  have hx' := siteIndex_project_lift hL x
  have hy' := siteIndex_project_lift hL y
  ext k
  change (((anchorPoint (siteIndex (torusProjection K y)) k-
    (anchorPoint (siteIndex (torusProjection K x)) k+targetStep j k)):ℝ):AddCircle L.val)=0
  rw [AddCircle.coe_sub,AddCircle.coe_add,show targetStep j k=((y k-x k:ℤ):ℝ) from congrFun hj k]
  have HX := congrFun hx' k
  have HY := congrFun hy' k
  change ((anchorPoint (siteIndex (torusProjection K x)) k:ℝ):AddCircle L.val)=((x k:ℝ):AddCircle L.val) at HX
  change ((anchorPoint (siteIndex (torusProjection K y)) k:ℝ):AddCircle L.val)=((y k:ℝ):AddCircle L.val) at HY
  rw [HX,HY,Int.cast_sub,AddCircle.coe_sub]
  abel

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_TaggedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {Ω A G Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G]

def allocatedTagLaw (μ : Measure Ω) (I : G→Ω→Finset A) (κ : A→Kernel Ω Y)
    (g : G) : Measure Y := ∑i,κ i ∘ₘ (μ.restrict {ω | i∈I g ω})

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
instance labelOptionSpace (J : Type*) : MeasurableSpace (Option J) := ⊤

variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def branchAccessible {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) (d : PhysicalDatum N K M G L) : Finset J :=
  Finset.univ.filter fun j ↦ particle j∈datumAccessibleLabels hL g m t r R C S u (siteIndex v) d

omit [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma branchAccessible_measurable {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) : Measurable (branchAccessible (M:=M) hL g m t r R C S u particle v) := by
  exact (measurable_of_countable (f:=fun s : Finset (Fin N) ↦
    Finset.univ.filter fun j ↦ particle j∈s)).comp (datumAccessibleLabels_measurable hL g m t r R C S u _)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalEndpoint
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener Comparison GaussianPacking
variable {E : Type*} [MeasurableSpace E]

def exposedPeriodSingle (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) :
    Kernel E (C(Time,Point)×Point) :=
  (Q ⊗ₖ parameterSuccessKernel
    (parameterTrialKernel t (fun e ↦ y e+c) (fun e ↦ z e+c)
      (hy.add measurable_const) (hz.add measurable_const))
    (exposedSuccess S) (exposedSuccess_measurable hS)).map
      (fun p ↦ (shiftPath (-c) p.2,p.1))

instance exposedPeriodSingle_finite (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) :
    IsFiniteKernel (exposedPeriodSingle Q t y z hy hz c S hS) := by
  unfold exposedPeriodSingle
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def endpointTarget {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) : Set (PhysicalDatum N K M G L×Point) :=
  (univ×ˢunitTarget (anchorPoint v)) ∩
    (fun p ↦ (p.1,p.2-routeCellPeriod v w j)) ⁻¹' datumTarget hL g m t r R C S u i j

lemma endpointTarget_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    MeasurableSet (endpointTarget (M:=M) hL g m t r R C S u i v w j) :=
  (MeasurableSet.univ.prod (unitTarget_measurable _)).inter
    ((datumTarget_measurable hL g m t r R C S u i j).preimage (by fun_prop))

def endpointPair {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) : Kernel (PhysicalDatum N K M G L) (C(Time,Point)×Point) :=
  exposedPeriodSingle
    (parameterTargetKernel (B:=unitTarget (anchorPoint v)) (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
      (endpointTarget hL g m t r R C S u i v w j)
      (endpointTarget_measurable hL g m t r R C S u i v w j)) t
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (datumStart_measurable hL i) (datumEnd_measurable hL i) (routeCellPeriod v w j)
    (shiftedDatumPermitted hL g m r R C S u i (routeCellPeriod v w j))
    (shiftedDatumPermitted_measurable hL g m r R C S u i (routeCellPeriod v w j))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteFactors
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

def pointAsPath (u : Point) : C(Time,Point) := ContinuousMap.const Time u

lemma pointAsPath_measurable : Measurable pointAsPath := by
  apply Continuous.measurable
  exact ContinuousMap.continuous_const'

@[simp] lemma pointAsPath_apply (u : Point) (s : Time) : pointAsPath u s=u := rfl

def cellPathReference {K : ℕ} (v : Fin 3→Fin K) : Measure C(Time,Point) :=
  (targetUniform (unitTarget (anchorPoint v))).map pointAsPath

instance cellPathReference_probability {K : ℕ} (v : Fin 3→Fin K) :
    IsProbabilityMeasure (cellPathReference v) := by
  have : IsProbabilityMeasure (targetUniform (unitTarget (anchorPoint v))) := by
    rw [targetUniform,unitTarget_volume,inv_one,one_smul]
    constructor
    simp only [Measure.restrict_apply_univ,unitTarget_volume]
  unfold cellPathReference
  exact Measure.isProbabilityMeasure_map pointAsPath_measurable.aemeasurable

def routeDensityBound (t : ℝ) : ℝ≥0∞ := max 2 (vertexDensityBound t)

def encodeFirstEndpoint (p : C(Time,Point)×Point) : C(Time,Point)×C(Time,Point) :=
  (p.1,pointAsPath p.2)
def encodeLastEndpoint (p : C(Time,Point)×Point) : C(Time,Point)×C(Time,Point) :=
  (pointAsPath p.2,p.1)

def physicalRouteFactor {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (labels : Fin (n+1)↪Fin N) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (k : Fin (n+2)) :
    Kernel (PhysicalDatum N K M G L) (C(Time,Point)×C(Time,Point)) :=
  if h0 : k.val=0 then
    (endpointPair hL g m t r R C S u (labels 0) (v 0) (v 0) 0).map encodeFirstEndpoint
  else if hk : k.val<n+1 then
    vertexPair hL g m t r R C S u (labels ⟨k.val,hk⟩)
      (labels ⟨k.val-1,by omega⟩) (v k) (v ⟨k.val-1,by omega⟩) (steps ⟨k.val-1,by omega⟩)
  else
    (endpointPair hL g m t r R C S u (labels (Fin.last n)) (v (Fin.last (n+1)))
      (v (Fin.last n).castSucc) (steps (Fin.last n))).map encodeLastEndpoint

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RoutePartition
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {I V : Type*} [DecidableEq I]
def nearSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) : Finset I :=
  s.filter (fun i ↦ ∃j∈t,e (c i) (c j))
def farSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) : Finset I :=
  s\nearSlots e c s t

end HardSphere.Comparison

end
end

section
noncomputable section
namespace HardSphere.Comparison
variable {J : Type*}

def routeEmbedding {d : ℕ} (labels : Fin d↪J) : Fin (d+1)↪Option J where
  toFun i := if h : i.val<d then some (labels ⟨i.val,h⟩) else none
  inj' := by
    intro i j hij
    by_cases hi : i.val<d <;> by_cases hj : j.val<d
    · simp only [dite_eq_left hi,dite_eq_left hj,Option.some.injEq] at hij
      have he := labels.injective hij
      exact Fin.ext (congrArg (fun k : Fin d ↦ k.val) he)
    · simp only [dite_eq_left hi,dite_eq_right hj] at hij
      contradiction
    · simp only [dite_eq_right hi,dite_eq_left hj] at hij
      contradiction
    · exact Fin.ext (by omega)
@[simp] lemma routeEmbedding_castSucc {d : ℕ} (labels : Fin d↪J) (i : Fin d) :
    routeEmbedding labels i.castSucc=some (labels i) := by
  change (if h : i.val<d then some (labels ⟨i.val,h⟩) else none)=_
  simp [i.isLt]
@[simp] lemma routeEmbedding_last {d : ℕ} (labels : Fin d↪J) :
    routeEmbedding labels (Fin.last d)=none := by
  change (if h : d<d then some (labels ⟨d,h⟩) else none)=_
  simp

def routePermutation {d : ℕ} (labels : Fin d↪J) : Equiv.Perm (Option J) :=
  (finRotate (d+1)).viaEmbedding (routeEmbedding labels)

def routeSlots {d : ℕ} (labels : Fin d↪J) : Finset (Option J) :=
  (Finset.univ.map (routeEmbedding labels))
lemma routePermutation_fixed {d : ℕ} (labels : Fin d↪J) (i : Option J)
    (hi : i∉routeSlots labels) : routePermutation labels i=i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j,rfl⟩
  apply hi
  exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalRoute
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {J : Type*}

def routePosition {d : ℕ} (labels : Fin d↪J) (i : routeSlots labels) : Fin (d+1) :=
  (Finset.mem_map.mp i.property).choose

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*}

def physicalSelectedFactor {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (i : routeSlots labels) :
    Kernel (PhysicalDatum N K M G L) (C(Time,Point)×C(Time,Point)) :=
  physicalRouteFactor hL g m t r R C S u (labels.trans particle) v steps (routePosition labels i)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_DependentChecks
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I E P : Type*} [Fintype I] [DecidableEq I] [Fintype E] [MeasurableSpace P]
  {V : I→Type*} [∀i,MeasurableSpace (V i)]
  (avoid : P→P→Prop) (hm : MeasurableSet {p : P×P | avoid p.1 p.2})
  (left right : E→I) (hdiff : ∀e,left e≠right e)
  (getL : (e:E)→V (left e)→P) (getR : (e:E)→V (right e)→P)
  (hL : ∀e,Measurable (getL e)) (hR : ∀e,Measurable (getR e))

def dependentCheck (e : E) : LocalCheck V where
  support := {left e,right e}
  nonempty := ⟨left e,by simp⟩
  arity := by simpa using Finset.card_insert_le (left e) ({right e}:Finset I)
  pass x := avoid (getL e (x (left e))) (getR e (x (right e)))
  measurable_pass := hm.preimage (f:=fun x : ∀i,V i ↦ (getL e (x (left e)),getR e (x (right e)))) (by fun_prop)
  depends x y h := by rw [h (left e) (by simp),h (right e) (by simp)]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalFactorChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison CellOrbital Groups
attribute [local instance] Classical.propDecidable

variable {I J E : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype E]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (allowed : J → Set C(Time,Point))
  (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
  (color : E → Bool) (labelL labelR : E → J) (hdiff : ∀e,labelL e ≠ labelR e)
  (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))

def factorPathCheck (r : ℝ) : E → LocalCheck V :=
  dependentCheck (fun f g : C(Time,Point) ↦ ¬TrialCollision (L:=L) r (projectCurve L g) f)
    (jointCollision_closed (L:=L) r).measurableSet.compl
    (fun e ↦ owner (color e) (labelL e)) (fun e ↦ owner (color e) (labelR e))
    (fun e x ↦ (path (color e) (labelL e) x).val)
    (fun e x ↦ (path (color e) (labelR e) x).val)
    (fun e ↦ measurable_subtype_coe.comp (hpath (color e) (labelL e)))
    (fun e ↦ measurable_subtype_coe.comp (hpath (color e) (labelR e)))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSparse
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]

def physicalEdges (anchor : J → Torus L) :=
  Bool×{p : J×J // p.1≠p.2 ∧ torusDistance L (anchor p.1) (anchor p.2)≤21}

instance physicalEdges_fintype (anchor : J → Torus L) : Fintype (physicalEdges anchor) :=
  inferInstanceAs (Fintype (Bool×{p : J×J // p.1≠p.2 ∧ torusDistance L (anchor p.1) (anchor p.2)≤21}))

def physicalSparseChecks (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (owner : Bool → J → I) (path : ∀b j,V (owner b j) → allowed j)
    (hpath : ∀b j,Measurable (path b j)) : physicalEdges anchor → LocalCheck V :=
  factorPathCheck (L:=L) allowed owner Prod.fst (fun e ↦ e.2.val.1) (fun e ↦ e.2.val.2) path hpath r

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

def fiberEquiv {i j : I} (h : i=j) : X i ≃ᵐ X j := by
  subst j
  exact MeasurableEquiv.refl _
omit [Fintype I] [DecidableEq I] in
@[simp] lemma fiberEquiv_self {i : I} (h : i=i) (x : X i) : fiberEquiv h x=x := rfl

variable (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
omit [Fintype I] in
include hfix in
lemma move_mem_iff (i : I) : σ i∈S ↔ i∈S := by
  constructor
  · intro hi
    by_contra hn
    exact hn (by simpa only [hfix i hn] using hi)
  · intro hi
    by_contra hn
    have hf := hfix (σ i) hn
    have he := σ.injective hf
    exact hn (he.symm ▸ hi)

def routeOwner (label : J → I) (b : Bool) (j : J) : I := if b then σ (label j) else label j

def routePath (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (b : Bool) (j : J) :
    (X (routeOwner σ label b j)×X (σ.symm (routeOwner σ label b j))) → allowed j := by
  cases b
  · exact fun p ↦ get j p.1
  · exact fun p ↦ if h : label j∈S then
      get j (fiberEquiv (σ.symm_apply_apply (label j)) p.2)
    else get j (fiberEquiv (hfix (label j) h) p.1)

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_measurable (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j)) (b : Bool) (j : J) :
    Measurable (routePath σ S hfix allowed label get b j) := by
  cases b
  · exact (hg j).comp measurable_fst
  · by_cases h : label j∈S
    · simp only [routePath,dite_eq_left h]
      exact (hg j).comp ((fiberEquiv (σ.symm_apply_apply (label j))).measurable.comp measurable_snd)
    · simp only [routePath,dite_eq_right h]
      exact (hg j).comp ((fiberEquiv (hfix (label j) h)).measurable.comp measurable_fst)

def routeChecks (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j)) :=
  physicalSparseChecks (V:=fun i ↦ X i×X (σ.symm i)) r anchor allowed (routeOwner σ label)
    (routePath σ S hfix allowed label get) (routePath_measurable σ S hfix allowed label get hg)

def primaryChecks (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j)) :=
  physicalSparseChecks r anchor allowed (fun _ ↦ label) (fun _ ↦ get) (fun _ ↦ hg)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ReversePair
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

def reverseFactor (σ : Equiv.Perm I) (j : I) :
    (X (σ j)×X (σ.symm (σ j))) ≃ᵐ (X j×X (σ j)) :=
  ((MeasurableEquiv.refl _).prodCongr (fiberEquiv (σ.symm_apply_apply j))).trans
    (MeasurableEquiv.prodComm)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma reverse_fix (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i) :
    ∀i,i∉s→σ.symm i=i := by
  intro i hi
  apply σ.injective
  rw [σ.apply_symm_apply,hf i hi]

def partialReverseFactor (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (j : I) :
    (X (σ j)×X (σ.symm (σ j))) ≃ᵐ (X j×X (σ j)) :=
  if hj : j∈s then reverseFactor σ j else
    (fiberEquiv (hf j hj)).prodCongr
      (fiberEquiv ((σ.symm_apply_apply j).trans (hf j hj).symm))

def partialReversePairs (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) :
    (∀i,X i×X (σ.symm i)) ≃ᵐ (∀j,X j×X (σ j)) :=
  (MeasurableEquiv.piCongrLeft (fun i ↦ X i×X (σ.symm i)) σ).symm.trans
    (MeasurableEquiv.piCongrRight (partialReverseFactor σ s hf))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SelectedReverse
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

abbrev selectedPerm (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i) : Equiv.Perm s where
  toFun i := ⟨σ i,(move_mem_iff σ s hf i).mpr i.property⟩
  invFun j := ⟨σ.symm j,by
    have h : σ (σ.symm j)∈s := by simp
    exact (move_mem_iff σ s hf _).mp h⟩
  left_inv i := Subtype.ext (σ.symm_apply_apply i)
  right_inv j := Subtype.ext (σ.apply_symm_apply j)

def reverseSelected (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i) :
    (∀i:s,X i×X (σ.symm i)) ≃ᵐ (∀j:s,X j×X (σ j)) :=
  (MeasurableEquiv.piCongrLeft (fun i:s ↦ X i×X (σ.symm i)) (selectedPerm σ s hf)).symm.trans
    (MeasurableEquiv.piCongrRight (fun j:s ↦ reverseFactor (X:=X) σ j))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ActualReverse
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

def rebuildPrimary (s : Finset I)
    (p : ((∀i:{i // i∉s},X i)×(∀i:s,X i×Y i))) : ∀i,X i :=
  fun i ↦ if hi : i∈s then (p.2 ⟨i,hi⟩).1 else p.1 ⟨i,hi⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PermutationObserved
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace HardSphere.Comparison
variable {I E W : Type*} [DecidableEq I] [MeasurableSpace E] [MeasurableSpace W]

def bathPermutation (σ : Equiv.Perm I) (star a b : I)
    (hs : σ star=a) (hb : σ b=star) :
    {i : I // i≠star ∧ i≠b} ≃ {i : I // i≠a ∧ i≠star} :=
  σ.subtypeEquiv (by
    intro i
    constructor
    · rintro ⟨hi,hj⟩
      exact ⟨fun h ↦ hi (σ.injective (h.trans hs.symm)),
        fun h ↦ hj (σ.injective (h.trans hb.symm))⟩
    · rintro ⟨hi,hj⟩
      exact ⟨fun h ↦ hi (h ▸ hs),fun h ↦ hj (h ▸ hb)⟩)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SharedRoute
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge
attribute [local instance] Classical.propDecidable

variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

def ambientFirst (s : Finset I) (σ : Equiv.Perm I)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) : ∀i,X i :=
  Function.updateFinset p.1 s (fun i ↦ (p.2 i).1)

def ambientSecond (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) : ∀i,X i :=
  Function.updateFinset p.1 s (fun i ↦ (reverseSelected σ s hf p.2 i).1)

def ambientRefreshEvent (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (A : Set (E×(∀i,X i))) : Set ((E×(∀i,X i))×(∀i:s,X i×X (σ.symm i))) :=
  {p | (p.1.1,ambientFirst s σ (p.1.2,p.2))∈A ∧
       (p.1.1,ambientSecond s σ hf (p.1.2,p.2))∈A}

def ambientRefreshKernel (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : Kernel (E×(∀i,X i)) (∀i:s,X i×X (σ.symm i)) :=
  fiberNormalize ((finiteKernelPi ρ).comap Prod.fst measurable_fst) (ambientRefreshEvent s σ hf A)

instance ambientRefreshKernel_finite (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : IsFiniteKernel (ambientRefreshKernel s σ hf ρ A) := by
  unfold ambientRefreshKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def ambientSharedKernel (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : Kernel E ((∀i,X i)×(∀i:s,X i×X (σ.symm i))) :=
  ξ ⊗ₖ ambientRefreshKernel s σ hf ρ A

instance ambientSharedKernel_finite (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : IsFiniteKernel (ambientSharedKernel s σ hf ξ ρ A) := by
  unfold ambientSharedKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SharedTransport
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge
attribute [local instance] Classical.propDecidable
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

def routeConfigMap (f : ∀i,X i→Y i) (x : ∀i,X i) : ∀i,Y i := fun i ↦ f i (x i)
def routeFactorMap (f : ∀i,X i→Y i) (s : Finset I) (σ : Equiv.Perm I)
    (p : ∀i:s,X i×X (σ.symm i)) : ∀i:s,Y i×Y (σ.symm i) :=
  fun i ↦ (f i (p i).1,f (σ.symm i) (p i).2)
def routePairedMap (f : ∀i,X i→Y i) (s : Finset I) (σ : Equiv.Perm I)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) :=
  (routeConfigMap f p.1,routeFactorMap f s σ p.2)

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPrimary
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalSlotAllowed {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) : Option J→Set C(Time,Point)
  | none => univ
  | some i => Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i)

def physicalSlotOn {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    (i : Option J)→Measure (physicalSlotAllowed hL g m r R C S u particle d i)
  | none => subtypeConditional (cellPathReference v) univ
  | some i => referenceOn t (datumStart hL d (particle i)) (datumEnd hL d (particle i))
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupported
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalSelectedOn {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) (i : routeSlots labels) :
    Measure (physicalSlotAllowed hL g m r R C S u particle d i ×
      physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)) :=
  supportedPair (physicalSelectedFactor hL g m t r R C S u particle labels v steps i d)
    (physicalSlotAllowed hL g m r R C S u particle d i)
    (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteAuxiliary
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

def extendSelectedPair (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) (ρ : ∀i:s,Measure (X i×X (σ.symm i)))
    (i : I) : Measure (X i×X (σ.symm i)) :=
  if hi : i∈s then ρ ⟨i,hi⟩ else (μ i).prod (ν (σ.symm i))

omit [Fintype I] in
instance extendSelectedPair_probability (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (ρ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ρ i)] (i : I) :
    IsProbabilityMeasure (extendSelectedPair σ s μ ν ρ i) := by
  unfold extendSelectedPair
  split <;> infer_instance

end HardSphere.Bridge
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_PhysicalCollisionReference
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [DecidableEq J]

def physicalCollisionReference {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J) :
    Measure (physicalSlotAllowed hL g m r R C S u particle d (some j)) :=
  if datumAccessible hL g m t r R C S u (particle j) d then
    physicalSlotOn hL g m t r R C S u particle (datumHome hL d (particle j)) d (some j) else 0

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CandidateConstant
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

def candidateConstant (a : ℕ) : ℕ := (2*(a+3)+1)^3*2^((2*a+1)^3)+(12*a+24)

end HardSphere.Lattice

open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointDanger
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

def acceptedEnvironment {K : ℕ} [NeZero K] (a : ℕ) (B : Finset (DiscreteTorus K)) (v w : Vertex) : Prop :=
  ¬LargeBadComponent (torusRangeGraph K a) B (K/(10*a)) ∧ endpointsExterior B v w

lemma small_star_of_no_large {K a : ℕ} [NeZero K] (ha : 1≤a)
    (B : Finset (DiscreteTorus K)) (hB : ¬LargeBadComponent (torusRangeGraph K a) B (K/(10*a))) :
    ∀ z∈B, (badComponent (torusRangeGraph K 1) B z).card<K := by
  intro z hz
  have hC : badComponent (torusRangeGraph K a) B z∈badComponents (torusRangeGraph K a) B :=
    Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hcard : (badComponent (torusRangeGraph K a) B z).card<K/(10*a) := by
    by_contra hn
    exact hB ⟨_,hC,by omega⟩
  have hsub : badComponent (torusRangeGraph K 1) B z ⊆ badComponent (torusRangeGraph K a) B z := by
    intro y hy
    rcases (mem_badComponent _ _ _ _).mp hy with ⟨hyB,hzy⟩
    exact (mem_badComponent _ _ _ _).mpr ⟨hyB,hzy.mono (badGraph_graphMono (torusRangeGraph_mono ha) B)⟩
  exact (Finset.card_le_card hsub).trans_lt (hcard.trans_le (Nat.div_le_self _ _))

open scoped NNReal

def SimpleGoodPath {K : ℕ} (B : Finset (DiscreteTorus K)) (x y : DiscreteTorus K) :=
  {p : (torusNearestGraph K).Walk x y // p.IsPath ∧ ∀ z∈p.support, z∉B}

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SimplePath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice
open MeasureTheory ProbabilityTheory

abbrev SimplePath {K : ℕ} (x y : DiscreteTorus K) :=
  {p : (torusNearestGraph K).Walk x y // p.IsPath}

instance simplePathMeasurableSpace {K : ℕ} (x y : DiscreteTorus K) :
    MeasurableSpace (SimplePath x y) := ⊤

def forgetGood {K : ℕ} {B : Finset (DiscreteTorus K)} {x y : DiscreteTorus K}
    (p : SimpleGoodPath B x y) : SimplePath x y := ⟨p.val,p.property.1⟩

def simpleEncounter {K : ℕ} (R : ℕ) {x y : DiscreteTorus K} (p q : SimplePath x y) : ℕ :=
  (encounterSet (torusNear K R) p.val.support.toFinset q.val.support.toFinset).card

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathSlots
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}

def pathVertexEmbedding (p : SimplePath x y) : Fin (p.val.length+1)↪DiscreteTorus K where
  toFun i := p.val.getVert i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij
@[simp] lemma pathVertex_zero (p : SimplePath x y) : pathVertexEmbedding p 0=x := by
  exact p.val.getVert_zero
@[simp] lemma pathVertex_last (p : SimplePath x y) :
    pathVertexEmbedding p (Fin.last p.val.length)=y := p.val.getVert_length

def departureEmbedding (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) : Fin p.val.length↪J where
  toFun := pick
  inj' := by
    intro i j h
    have he := congrArg anchor h
    rw [hpick i,hpick j] at he
    have hv := (pathVertexEmbedding p).injective he
    exact Fin.ext (congrArg (fun k : Fin (p.val.length+1) ↦ k.val) hv)
def extendedAnchor (anchor : J→DiscreteTorus K) (y : DiscreteTorus K) : Option J→DiscreteTorus K :=
  fun o ↦ o.elim y anchor

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RouteMatches
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open _root_.OAI.HardSphere.Lattice MeasureTheory ProbabilityTheory
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*} [DecidableEq J]

def departureSites (p : SimplePath x y) : Finset (DiscreteTorus K) :=
  Finset.univ.image (fun i : Fin p.val.length ↦ pathVertexEmbedding p i.castSucc)

def matchingSites (p q : SimplePath x y) (f g : DiscreteTorus K→J) : Finset (DiscreteTorus K) :=
  (departureSites p∩departureSites q).filter (fun v ↦ f v=g v)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

def branchParticles {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) :
    {i // i∈groupUnion g a}↪Fin N := ⟨Subtype.val,Subtype.val_injective⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLifted
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalOnChecks {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) :=
  primaryChecks (X:=fun i : Option J ↦ physicalSlotAllowed hL g m r R C S u particle d i)
    r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
    (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j))
    some (fun _ f ↦ f) (fun _ ↦ measurable_id)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteAuxiliary
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)

structure PhysicalRouteAux where
  forward : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
    (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i))
  backward : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
    (physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i))
  forward_finite : ∀i,IsFiniteKernel (forward i)
  backward_finite : ∀i,IsFiniteKernel (backward i)
  selected : ∀i:routeSlots labels,
    (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i).compProd (forward i)=
      physicalSelectedOn hL g m t r R C S u particle labels v steps d i
  reverse : ∀i,((physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d (routePermutation labels i)).compProd
    (forward (routePermutation labels i))).map (reverseFactor (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels) i)=(physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (backward i)
  forward_bound : ∀i x,forward i x univ ≤ routeDensityBound t
  backward_bound : ∀i x,backward i x univ ≤ routeDensityBound t
  forward_mass : ∀i,∫⁻x,forward i x univ ∂physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i=1
  backward_mass : ∀i,∫⁻x,backward i x univ ∂physicalSlotOn hL g m t r R C S u particle (v 0) d i=1
  firstSeed : ∀i,physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)
  secondSeed : ∀i,physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)

attribute [instance] PhysicalRouteAux.forward_finite PhysicalRouteAux.backward_finite

variable {hL g m t r R C S u particle labels v steps d}

def PhysicalRouteAux.firstDensity (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d) :
    (∀i,physicalSlotAllowed hL g m r R C S u particle d i)→ℝ≥0∞ :=
  fun x ↦ conditionalLikelihood (physicalOnChecks hL g m r R C S u particle d)
    (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels) (routeSlots labels) (routePermutation_fixed labels) r
      (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
    (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d) A.forward
    (routeSlots labels) (Finset.univ\routeSlots labels) x A.firstSeed

def PhysicalRouteAux.secondDensity (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d) :
    (∀i,physicalSlotAllowed hL g m r R C S u particle d i)→ℝ≥0∞ :=
  fun x ↦ conditionalLikelihood (physicalOnChecks hL g m r R C S u particle d)
    (routeChecks (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
      (routePermutation labels).symm (routeSlots labels) (reverse_fix _ _ (routePermutation_fixed labels)) r
      (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id))
    (physicalSlotOn hL g m t r R C S u particle (v 0) d) A.backward
    (routeSlots labels) (Finset.univ\routeSlots labels) x A.secondSeed

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_RouteFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def RouteFieldValid (p : SimplePath x y) (z : DiscreteTorus K→Option J) : Prop :=
  ∃ f : Fin p.val.length↪J, ∀i,z (pathVertexEmbedding p i.castSucc)=some (f i)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev PhysicalRouteCode (x y : DiscreteTorus K) (J : Type*) :=
  SimplePath x y × (DiscreteTorus K→Option J)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalObservation
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {I J E : Type*} [DecidableEq I] [DecidableEq J]

def optionParticle (particle : J↪I) : Option J↪Option I where
  toFun := Option.map particle
  inj' := by
    intro i j h
    cases i <;> cases j <;> simp_all only [Option.map_none,Option.map_some,Option.some.injEq,
      reduceCtorEq]
    exact particle.injective h

def fillGroup (particle : J↪I) (H : Option I→E) (F : Option J→E) : Option I→E :=
  Function.extend (optionParticle particle) F H

omit [DecidableEq I] [DecidableEq J] in
lemma fillGroup_selected (particle : J↪I) (H : Option I→E) (F : Option J→E) (i : Option J) :
    fillGroup particle H F (optionParticle particle i)=F i :=
  (optionParticle particle).injective.extend_apply F H i

omit [DecidableEq I] [DecidableEq J] in
lemma fillGroup_measurable [MeasurableSpace E] (particle : J↪I) :
    Measurable (fun z : (Option I→E)×(Option J→E) ↦ fillGroup particle z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈Set.range (optionParticle particle)
  · obtain ⟨j,rfl⟩ := hi
    simpa only [fillGroup_selected,Function.comp_def] using (measurable_pi_apply j).comp measurable_snd
  · have he : (fun z : (Option I→E)×(Option J→E) ↦ fillGroup particle z.1 z.2 i)=fun z ↦ z.1 i := by
      funext z; exact Function.extend_apply' z.2 z.1 i hi
    rw [he]
    exact (measurable_pi_apply i).comp measurable_fst

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma projectPoint_continuous (L : Length) : Continuous (projectPoint L) :=
  continuous_pi (fun j ↦ (AddCircle.continuous_mk' L.val).comp (continuous_apply j))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_UniformBath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
local instance permBathSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
local instance permBathSingleton (n : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ ↦ trivial⟩

def bathFinEquiv (a : Fin (n+1)) : Fin n ≃ {j : Option (Fin (n+1)) // j≠none ∧ j≠some a} :=
  Equiv.ofBijective (fun k ↦ ⟨some (a.succAbove k),
    ⟨Option.some_ne_none _,fun equality ↦ Fin.succAbove_ne a k (Option.some.inj equality)⟩⟩) (by
    constructor
    · intro j k h
      exact Fin.succAbove_right_injective (Option.some_injective _ (congrArg Subtype.val h))
    · rintro ⟨j,hj⟩
      cases j with
      | none => exact False.elim (hj.1 rfl)
      | some j =>
        have hja : j≠a := fun h ↦ hj.2 (congrArg some h)
        obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hja
        exact ⟨k,Subtype.ext (congrArg some hk)⟩)

def bathIndexPermutation (σ : Equiv.Perm (Option (Fin (n+1))))
    (a b : Fin (n+1)) (hs : σ none=some a) (hb : σ (some b)=none) : Equiv.Perm (Fin n) :=
  (bathFinEquiv b).trans ((bathPermutation σ none (some a) (some b) hs hb).trans
    ((Equiv.subtypeEquivRight fun _ ↦ and_comm).trans (bathFinEquiv a).symm))

def uniformBathOrder (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
instance uniformBathOrder_probability (n : ℕ) : IsProbabilityMeasure (uniformBathOrder n) := by
  unfold uniformBathOrder; infer_instance

def orderedPrimaryObservation (b : Bool) (i : Fin (n+1))
    (z : (Option (Fin (n+1))→E)×Equiv.Perm (Fin n)) : E×E×(Fin n→E) :=
  if b then (z.1 (some i),z.1 none,fun j ↦ z.1 (some (i.succAbove (z.2 j))))
  else (z.1 none,z.1 (some i),fun j ↦ z.1 (some (i.succAbove (z.2 j))))

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalObservedLaw
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

def primaryBathKernel (b : Bool) (i : Fin (n+1)) :
    Kernel (Option (Fin (n+1))→E) (E×E×(Fin n→E)) :=
  (Kernel.id ×ₖ Kernel.const _ (uniformBathOrder n)).map (orderedPrimaryObservation b i)
end HardSphere.Comparison

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SymmetricTag
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
local instance permSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
local instance permSingleton (n : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ ↦ trivial⟩

def tagOrderPerm (i : Fin (n+1)) (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' 0).trans ((Equiv.optionCongr τ).trans (finSuccEquiv' i).symm)
@[simp] lemma tagOrderPerm_zero (i : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    tagOrderPerm i τ 0=i := by simp [tagOrderPerm]
@[simp] lemma tagOrderPerm_succ (i : Fin (n+1)) (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    tagOrderPerm i τ j.succ=i.succAbove (τ j) := by
  change (finSuccEquiv' i).symm ((Equiv.optionCongr τ) ((finSuccEquiv' 0) j.succ))=_
  have hh : (finSuccEquiv' (0:Fin (n+1))) j.succ=some j := by
    simpa only [Fin.succAbove_zero] using finSuccEquiv'_succAbove (0:Fin (n+1)) j
  simp [hh]

def splitFirst (x : Fin (n+1)→E) : E×(Fin n→E) := (x 0,fun j ↦ x j.succ)

def orderedObservation (i : Fin (n+1)) (p : (Fin (n+1)→E)×Equiv.Perm (Fin n)) : E×(Fin n→E) :=
  (p.1 i,fun j ↦ p.1 (i.succAbove (p.2 j)))

def orderedKernel (β : Measure (Equiv.Perm (Fin n))) (i : Fin (n+1)) :
    Kernel (Fin (n+1)→E) (E×(Fin n→E)) :=
  (Kernel.id ×ₖ Kernel.const _ β).map (orderedObservation i)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalCellReference
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def cellExtraKernel (ν : Measure X) (A B : Set X) (hA : MeasurableSet A) :
    Kernel (X×Y) ((X×Y)×X) :=
  (Kernel.id ×ₖ Kernel.const _ (ν.restrict B)).restrict
    (hA.preimage (measurable_fst.comp measurable_fst))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PrimaryProduct
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

def adjoinPoint (z : (Fin (n+1)→E)×E) : Option (Fin (n+1))→E :=
  fun i ↦ i.elim z.2 z.1

def cellObservation (b : Bool) (z : (E×(Fin n→E))×E) : E×E×(Fin n→E) :=
  if b then (z.1.1,z.2,z.1.2) else (z.2,z.1.1,z.1.2)

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_MixtureMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

instance targetUniform_finite (A : Set Point) : IsFiniteMeasure (targetUniform A) := by
  constructor
  change ((volume A)⁻¹ • volume.restrict A) univ<⊤
  rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact (ENNReal.inv_mul_le_one _).trans_lt (by simp)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_TaggedMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X]

def taggedReference (P : Measure X) (E : I→Set X) : Measure (I×X) :=
  (Measure.count.prod P).restrict {p | p.2∈E p.1}

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {Q X I : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def tagLikelihood (σ : Measure Q) (tag : Q→I) (L : Q×X→ℝ≥0∞) (i : I) (x : X) : ℝ≥0∞ :=
  ∫⁻q,if tag q=i then L (q,x) else 0 ∂σ

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalReferenceRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

def cellPointReference {K : ℕ} (L : Length) (v : Fin 3→Fin K) : Measure (Torus L) :=
  (cellPathReference v).map (fun e ↦ projectPoint L (e midpointTime))
instance cellPointReference_probability {K : ℕ} (L : Length) (v : Fin 3→Fin K) :
    IsProbabilityMeasure (cellPointReference L v) := by
  unfold cellPointReference
  exact (Measure.isProbabilityMeasure_map_iff (((projectPoint_continuous L).measurable.comp
    (continuous_eval_const midpointTime).measurable).aemeasurable)).mpr inferInstance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_Affinity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere.Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def affinity (μ : Measure α) (p q : α → ℝ) : ℝ :=
  ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ

def measureAffinity (P Q : Measure α) : ℝ :=
  affinity (P + Q) (fun x ↦ (P.rnDeriv (P + Q) x).toReal)
    (fun x ↦ (Q.rnDeriv (P + Q) x).toReal)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ConditionalTagDensity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {D Q X I : Type*} [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def conditionalTagLikelihood (σ : Kernel D Q) (tag : Q→I)
    (L : (D×Q)×X→ℝ≥0∞) (E : Set D) (i : I) (z : D×X) : ℝ≥0∞ :=
  if z.1∈E then ∫⁻q,if tag q=i then L ((z.1,q),z.2) else 0 ∂σ z.1 else 0

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_SumMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X]

def retainedFiniteSum (P : I→Measure X) : Measure (I×X) :=
  ∑i,(P i).map (Prod.mk i)
instance retainedFiniteSum_finite (P : I→Measure X) [∀i,IsFiniteMeasure (P i)] :
    IsFiniteMeasure (retainedFiniteSum P) := by
  unfold retainedFiniteSum; infer_instance

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RetainedObservation
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {D X Y : Type*} [MeasurableSpace D] [MeasurableSpace X] [MeasurableSpace Y]

def retainedObserver (κ : Kernel (D×X) Y) : Kernel (D×X) (D×Y) :=
  (Kernel.deterministic Prod.fst measurable_fst) ×ₖ κ
instance retainedObserver_markov (κ : Kernel (D×X) Y) [IsMarkovKernel κ] :
    IsMarkovKernel (retainedObserver κ) := by unfold retainedObserver; infer_instance

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Density_DensityOperators
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
namespace HardSphere.Density

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H}

def Operator.root (T : Operator H) : H →L[ℂ] H := CFC.sqrt T.toCLM

end HardSphere.Density

namespace HardSphere.Density
open ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def Operator.entry {ι : Type*} (T : Operator H) (A : H →L[ℂ] K)
    (b : HilbertBasis ι ℂ K) (i : basisSet H) (j : ι) : ℝ :=
  ‖inner ℂ (b j) (A (T.root (basis H i)))‖^2

end HardSphere.Density
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_PhysicalOrbitalReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def orbitalObservationEquiv : ((Y×X)×X)≃ᵐ(X×X×Y) where
  toFun p := (p.1.2,p.2,p.1.1)
  invFun p := ((p.2.2,p.1),p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (Y×X)×X ↦ (p.1.2,p.2,p.1.1)); fun_prop
  measurable_invFun := by change Measurable (fun p : X×X×Y ↦ ((p.2.2,p.1),p.2.1)); fun_prop

def tagBathSwapEquiv : ((X×Y)×X)≃ᵐ((Y×X)×X) where
  toFun p := ((p.1.2,p.1.1),p.2)
  invFun p := ((p.1.2,p.1.1),p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (X×Y)×X ↦ ((p.1.2,p.1.1),p.2)); fun_prop
  measurable_invFun := by change Measurable (fun p : (Y×X)×X ↦ ((p.1.2,p.1.1),p.2)); fun_prop

def orbitalSwapEquiv : ((Y×X)×X)≃ᵐ((Y×X)×X) where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (Y×X)×X ↦ ((p.1.1,p.2),p.1.2)); fun_prop
  measurable_invFun := by change Measurable (fun p : (Y×X)×X ↦ ((p.1.1,p.2),p.1.2)); fun_prop

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_Index
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace HardSphere.DyadicSkeleton

abbrev Index := Fin 2 × ℕ × ℕ
abbrev Noise := Index → unitInterval

def law : Measure Noise := Measure.infinitePi (fun _ : Index ↦ volume)
instance instIsProbabilityMeasureNoiseLaw : IsProbabilityMeasure law := by unfold law; infer_instance

def uniform (ω : Noise) (j : Fin 2) (ℓ k : ℕ) : ℝ :=
  2 * (ω (j,ℓ,k) : ℝ) - 1

@[fun_prop] lemma measurable_uniform (j : Fin 2) (ℓ k : ℕ) :
    Measurable (fun ω ↦ uniform ω j ℓ k) := by
  unfold uniform
  fun_prop

def decay : ℝ := (2:ℝ)^(-(1:ℝ)/4)
def cvel : ℝ := (1-decay)/2

def velocity (ω : Noise) (j : Fin 2) (i : ℕ) : ℝ :=
  cvel * ∑' ℓ : ℕ, decay^ℓ * uniform ω j ℓ (i/2^ℓ)

def position (ω : Noise) (j : Fin 2) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range t, velocity ω j i

@[fun_prop] lemma measurable_velocity (j : Fin 2) (i : ℕ) :
    Measurable (fun ω ↦ velocity ω j i) := by
  unfold velocity
  apply Measurable.const_mul
  exact Measurable.tsum (fun ℓ ↦ measurable_const.mul (measurable_uniform j ℓ _))

@[fun_prop] lemma measurable_position (j : Fin 2) (t : ℕ) :
    Measurable (fun ω ↦ position ω j t) := by
  unfold position
  fun_prop

def coordinateTest (j : Fin 2) (n : ℕ) (y R : ℝ) (ω : Noise) : ℝ≥0∞ :=
  {ω | |position ω j n-y| ≤ R}.indicator (fun _ ↦ 1) ω

@[fun_prop] lemma measurable_coordinateTest (j : Fin 2) (n : ℕ) (y R : ℝ) :
    Measurable (coordinateTest j n y R) := by
  apply measurable_const.indicator
  exact measurableSet_le ((measurable_position j n).sub_const y).abs measurable_const

def freshScale (ℓ : ℕ) : ℝ := (2^ℓ:ℕ) * cvel * decay^ℓ

def nearTest (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) : ℝ≥0∞ :=
  coordinateTest 0 n (y 0) R ω * coordinateTest 1 n (y 1) R ω

@[fun_prop] lemma measurable_nearTest (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) :
    Measurable (nearTest n y R) :=
  (measurable_coordinateTest 0 n (y 0) R).mul (measurable_coordinateTest 1 n (y 1) R)

def PastInvariant (t : ℕ) (H : Noise → ℝ≥0∞) : Prop :=
  ∀ (j : Fin 2) (ℓ b : ℕ), t ≤ b*2^ℓ → ∀ ω x,
    H (Function.update ω (j,ℓ,b) x) = H ω

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_TimeGaps
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

def timeGaps : {n : ℕ} → (Fin n → ℕ) → Fin n → ℕ
  | 0, _ => Fin.elim0
  | _+1, t => Fin.cases (t 0) (fun i ↦ t i.succ - t i.castSucc)

@[simp] lemma timeGaps_zero {n : ℕ} (t : Fin (n+1) → ℕ) : timeGaps t 0 = t 0 := rfl
@[simp] lemma timeGaps_succ {n : ℕ} (t : Fin (n+1) → ℕ) (i : Fin n) :
    timeGaps t i.succ = t i.succ - t i.castSucc := rfl

def splitVectorEquiv (n : ℕ) (A : Type*) : (Fin (n+1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i ↦ f i.succ)
  invFun v := Fin.cases v.1 v.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv v := rfl

abbrev BoundedTimes (T n : ℕ) := {t : Fin n → ℕ // StrictMono t ∧ ∀ i, t i ≤ T}
abbrev TimeSubset (T : ℕ) := {s : Finset ℕ // s ∈ (Finset.range (T+1)).powerset}

def encodeTimeSubset (T : ℕ) (s : TimeSubset T) : Σ n, BoundedTimes T n :=
  ⟨s.val.card, ⟨s.val.orderEmbOfFin rfl, (s.val.orderEmbOfFin rfl).strictMono,
    fun i ↦ by
      have h := (Finset.mem_powerset.mp s.property) (s.val.orderEmbOfFin_mem rfl i)
      exact Nat.le_of_lt_succ (Finset.mem_range.mp h)⟩⟩

def decodeTimes {T : ℕ} (v : Σ n, BoundedTimes T n) : Finset ℕ :=
  Finset.univ.image v.2.val

def gapKernel (k : ℕ) : ℝ≥0∞ :=
  if k=0 then 1 else ENNReal.ofReal ((16/cvel^2) * (k:ℝ)^(-(3:ℝ)/2))
def radiusFactor (R : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((1+R)^2)

def encounterMass {n : ℕ} (t : Fin n → ℕ) (r : Fin n → ℝ)
    (y : ℕ → Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∏ i, nearTest (t i) (y (t i)) (r i) ω ∂law

def orderedEncounterConstant : ℝ := (∑' k, gapKernel k).toReal

def radiusEnvelope (a : ℕ → ℝ≥0∞) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) : ℝ≥0∞ :=
  ∑' l : ℕ, a l * nearTest n y (l:ℝ) ω

@[fun_prop] lemma measurable_radiusEnvelope (a : ℕ → ℝ≥0∞) (n : ℕ) (y : Fin 2 → ℝ) :
    Measurable (radiusEnvelope a n y) := by
  unfold radiusEnvelope
  exact Measurable.tsum (fun l ↦ (measurable_nearTest n y (l:ℝ)).const_mul _)

def weightedEncounterMass {n : ℕ} (t : Fin n → ℕ) (a : ℕ → ℝ≥0∞)
    (y : ℕ → Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∏ i, radiusEnvelope a (t i) (y (t i)) ω ∂law

def radiusActivity (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal orderedEncounterConstant * ∑' l : ℕ, a l * radiusFactor (l:ℝ)

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_NearPotential
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

def transverseDistance (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) : ℝ :=
  max |position ω 0 n-y 0| |position ω 1 n-y 1|
@[fun_prop] lemma measurable_transverseDistance (n : ℕ) (y : Fin 2 → ℝ) :
    Measurable (transverseDistance n y) := by unfold transverseDistance; fun_prop

def softPotential (B : ℝ) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) : ℝ :=
  Real.exp (-transverseDistance n y ω/B)
@[fun_prop] lemma measurable_softPotential (B : ℝ) (n : ℕ) (y : Fin 2 → ℝ) :
    Measurable (softPotential B n y) := by unfold softPotential; fun_prop

def softWeights (B : ℝ) (l : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((1-(l:ℝ))/B))

def twoCopyDistance (n : ℕ) (z : Noise × Noise) : ℝ :=
  transverseDistance n (fun j ↦ position z.2 j n) z.1

@[fun_prop] lemma measurable_twoCopyDistance (n : ℕ) :
    Measurable (twoCopyDistance n) := by
  unfold twoCopyDistance transverseDistance
  exact (((measurable_position 0 n).comp measurable_fst).sub
    ((measurable_position 0 n).comp measurable_snd)).abs.max
    (((measurable_position 1 n).comp measurable_fst).sub
    ((measurable_position 1 n).comp measurable_snd)).abs

abbrev Vertex := Fin 3 → ℤ

def baseTrans (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) (j : Fin 2) : ℝ :=
  (t:ℝ)*(d j:ℝ)/(n:ℝ)+position ω j (min t (n-t))

def baseVertex (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) : Vertex :=
  ![(t:ℤ),⌊baseTrans n d ω t 0⌋,⌊baseTrans n d ω t 1⌋]

@[fun_prop] lemma measurable_baseTrans (n : ℕ) (d : Fin 2 → ℤ) (t : ℕ) (j : Fin 2) :
    Measurable (fun ω ↦ baseTrans n d ω t j) := by unfold baseTrans; fun_prop

@[fun_prop] lemma measurable_baseVertex (n : ℕ) (d : Fin 2 → ℤ) (t : ℕ) :
    Measurable (fun ω ↦ baseVertex n d ω t) := by
  apply Measurable.of_eval
  intro j
  fin_cases j
  · exact measurable_const
  · exact Int.measurable_floor.comp (measurable_baseTrans n d t 0)
  · exact Int.measurable_floor.comp (measurable_baseTrans n d t 1)

lemma baseVertex_initial (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    baseVertex n d ω 0 = 0 := by
  ext j
  fin_cases j <;> simp [baseVertex,baseTrans,position]

lemma baseVertex_final (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ) (ω : Noise) :
    baseVertex n d ω n = ![(n:ℤ),d 0,d 1] := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  ext j
  fin_cases j <;> simp [baseVertex,baseTrans,position,mul_div_cancel_left₀ _ hn0]

def axisSteps (a b : ℤ) : List ℤ :=
  if a ≤ b then (List.range (b-a).toNat).map (fun k : ℕ ↦ a+(k:ℤ)+1)
  else (List.range (a-b).toNat).map (fun k : ℕ ↦ a-(k:ℤ)-1)

def refineStep (a b : Vertex) : List Vertex :=
  [![b 0,a 1,a 2]] ++
  (axisSteps (a 1) (b 1)).map (fun c ↦ ![b 0,c,a 2]) ++
  (axisSteps (a 2) (b 2)).map (fun c ↦ ![b 0,b 1,c])

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_LevelList
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

def levelList (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) : ℕ → List Vertex
  | 0 => [baseVertex n d ω 0]
  | t+1 => refineStep (baseVertex n d ω t) (baseVertex n d ω (t+1))

def occurrenceList (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) : List Vertex :=
  (List.range (n+1)).flatMap (levelList n d ω)

lemma occurrenceList_initial (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    (0:Vertex) ∈ occurrenceList n d ω := by
  apply List.mem_flatMap.mpr
  refine ⟨0,by simp,?_⟩
  simp [levelList,baseVertex_initial]

def periodicProjection (K : ℕ) (x : Vertex) : Fin 3 → AddCircle (K:ℝ) :=
  fun j ↦ ((x j:ℝ) : AddCircle (K:ℝ))

def periodicDistance (K : ℕ) (x y : Vertex) : ℝ :=
  dist (periodicProjection K x) (periodicProjection K y)

def foldIndex (n : ℕ) (j : Fin (n+1)) : Fin (n/2+1) × Bool :=
  if hj : j.val ≤ n/2 then (⟨j.val, by omega⟩, false)
  else (⟨n-j.val, by omega⟩, true)

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_SkeletonHitConstant
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

instance listVertexMeasurableSpace : MeasurableSpace (List Vertex) := ⊤
instance listVertexDiscreteMeasurableSpace : DiscreteMeasurableSpace (List Vertex) := ⟨fun _ ↦ trivial⟩

@[fun_prop] lemma measurable_levelList (n : ℕ) (d : Fin 2 → ℤ) (t : ℕ) :
    Measurable (fun ω ↦ levelList n d ω t) := by
  cases t with
  | zero =>
    exact (measurable_of_countable (fun a : Vertex ↦ [a])).comp
      (measurable_baseVertex n d 0)
  | succ t =>
    exact (measurable_of_countable (fun a : Vertex × Vertex ↦ refineStep a.1 a.2)).comp
      ((measurable_baseVertex n d t).prodMk (measurable_baseVertex n d (t+1)))

@[fun_prop] lemma measurable_occurrenceList (n : ℕ) (d : Fin 2 → ℤ) :
    Measurable (occurrenceList n d) := by
  have hl (ts : List ℕ) : Measurable (fun ω ↦ ts.flatMap (levelList n d ω)) := by
    induction ts with
    | nil => exact measurable_const
    | cons t ts ih =>
      simpa only [List.flatMap_cons,Function.comp_def] using
        (measurable_of_countable (fun p : List Vertex × List Vertex ↦ p.1 ++ p.2)).comp
          ((measurable_levelList n d t).prodMk ih)
  exact hl (List.range (n+1))

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_LiftedSkeleton
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma mem_axisSteps_of_between (a b k : ℤ) (hl : min a b ≤ k) (hu : k ≤ max a b) :
    k = a ∨ k ∈ axisSteps a b := by
  by_cases ha : k = a
  · exact Or.inl ha
  right
  unfold axisSteps
  split_ifs with h
  · simp only [min_eq_left h] at hl
    simp only [max_eq_right h] at hu
    apply List.mem_map.mpr
    refine ⟨(k-a-1).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega
  · simp only [min_eq_right (by omega : b ≤ a)] at hl
    simp only [max_eq_left (by omega : b ≤ a)] at hu
    apply List.mem_map.mpr
    refine ⟨(a-k-1).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

lemma refineStep_final (a b : Vertex) : b ∈ refineStep a b := by
  have h2 := mem_axisSteps_of_between (a 2) (b 2) (b 2) (min_le_right _ _) (le_max_right _ _)
  have h1 := mem_axisSteps_of_between (a 1) (b 1) (b 1) (min_le_right _ _) (le_max_right _ _)
  have hb : ![b 0,b 1,b 2] = b := by ext j; fin_cases j <;> rfl
  rcases h2 with h2|h2
  · rcases h1 with h1|h1
    · have he : ![b 0,a 1,a 2] = b := by rw [← h1,← h2,hb]
      simp [refineStep,he]
    · apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨b 1,h1,by rw [← h2,hb]⟩
  · apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨b 2,h2,hb⟩

lemma refineStep_reach (a b : Vertex) (hfirst : b 0 = a 0+1) :
    withinReach nearestStep {x | x=a ∨ x∈refineStep a b} a b := by
  let D : Set Vertex := {x | x=a ∨ x∈refineStep a b}
  let u : Vertex := ![b 0,a 1,a 2]
  let v : Vertex := ![b 0,b 1,a 2]
  have hu : u∈D := Or.inr (by simp [refineStep,u])
  have h1 : withinReach nearestStep D a u := by
    apply Relation.ReflTransGen.single
    refine ⟨Or.inl rfl,hu,0,?_,?_⟩
    · simp only [u,Matrix.cons_val_zero,hfirst]; norm_num
    · intro j hj
      fin_cases j <;> simp_all [u]
  have h2 : withinReach nearestStep D u v := by
    have h := withinReach_axis u 1 (a 1) (b 1) (D:=D) ?_
    · convert h using 1 <;> ext j <;> fin_cases j <;> simp [u,v]
    intro k hk hk'
    rcases mem_axisSteps_of_between (a 1) (b 1) k hk hk' with rfl|hmem
    · change Function.update u 1 (u 1)∈D
      simpa only [Function.update_eq_self] using hu
    · right
      apply List.mem_append_left
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨k,hmem,?_⟩
      ext j; fin_cases j <;> simp [u]
  have hv : v∈D := by
    rcases mem_axisSteps_of_between (a 1) (b 1) (b 1) (min_le_right _ _) (le_max_right _ _) with h|h
    · simpa [v,h] using hu
    · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨b 1,h,rfl⟩)))
  have h3 : withinReach nearestStep D v b := by
    have h := withinReach_axis v 2 (a 2) (b 2) (D:=D) ?_
    · convert h using 1 <;> ext j <;> fin_cases j <;> simp [v]
    intro k hk hk'
    rcases mem_axisSteps_of_between (a 2) (b 2) k hk hk' with rfl|hmem
    · change Function.update v 2 (v 2)∈D
      simpa only [Function.update_eq_self] using hv
    · right
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨k,hmem,?_⟩
      ext j; fin_cases j <;> simp [v]
  exact h1.trans (h2.trans h3)

lemma baseVertex_mem_level (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) :
    baseVertex n d ω t ∈ levelList n d ω t := by
  cases t with
  | zero => simp [levelList]
  | succ t => exact refineStep_final _ _

lemma level_mem_occurrence (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) (ht : t ≤ n)
    {x : Vertex} (hx : x∈levelList n d ω t) : x∈occurrenceList n d ω :=
  List.mem_flatMap.mpr ⟨t,List.mem_range.mpr (by omega),hx⟩

lemma occurrence_reach (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    withinReach nearestStep {x | x∈occurrenceList n d ω}
      (baseVertex n d ω 0) (baseVertex n d ω n) := by
  have H : ∀t, t≤n → withinReach nearestStep {x | x∈occurrenceList n d ω}
      (baseVertex n d ω 0) (baseVertex n d ω t) := by
    intro t
    induction t with
    | zero => intro _; exact .refl
    | succ t ih =>
      intro ht
      apply (ih (by omega)).trans
      apply withinReach_mono (D:={x | x=baseVertex n d ω t ∨ x∈refineStep
        (baseVertex n d ω t) (baseVertex n d ω (t+1))})
      · intro x hx
        rcases hx with rfl|hx
        · exact level_mem_occurrence n d ω t (by omega) (baseVertex_mem_level n d ω t)
        · exact level_mem_occurrence n d ω (t+1) ht hx
      · apply refineStep_reach
        simp [baseVertex]
  exact H n le_rfl

lemma nearestStep_add (v : Vertex) {x y : Vertex} (h : nearestStep x y) :
    nearestStep (v+x) (v+y) := by
  obtain ⟨j,hj,hr⟩ := h
  refine ⟨j,?_,fun i hi ↦ by simpa using congrArg (v i+·) (hr i hi)⟩
  simpa only [Pi.add_apply,add_sub_add_left_eq_sub] using hj

lemma withinReach_add (v : Vertex) {D : Set Vertex} {x y : Vertex}
    (h : withinReach nearestStep D x y) :
    withinReach nearestStep ((v+·) '' D) (v+x) (v+y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact .single ⟨mem_image_of_mem _ h.1,mem_image_of_mem _ h.2.1,nearestStep_add v h.2.2⟩
  | trans _ _ ih ih' => exact ih.trans ih'

def liftedSkeleton (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) : Finset Vertex :=
  ((occurrenceList n d ω).map (v+·)).toFinset

lemma liftedSkeleton_mem (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) {x : Vertex} :
    x∈liftedSkeleton n d v ω ↔ ∃y∈occurrenceList n d ω,v+y=x := by
  simp [liftedSkeleton]

lemma liftedSkeleton_reach (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    withinReach nearestStep (↑(liftedSkeleton n d v ω))
      (v+baseVertex n d ω 0) (v+baseVertex n d ω n) := by
  apply withinReach_mono _ (withinReach_add v (occurrence_reach n d ω))
  rintro x ⟨y,hy,rfl⟩
  exact (liftedSkeleton_mem _ _ _ _).mpr ⟨y,hy,rfl⟩

lemma liftedSkeleton_initial (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    v ∈ liftedSkeleton n d v ω := by
  exact (liftedSkeleton_mem _ _ _ _).mpr ⟨0,occurrenceList_initial n d ω,add_zero v⟩

lemma liftedSkeleton_final (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    v+![(n:ℤ),d 0,d 1] ∈ liftedSkeleton n d v ω := by
  apply (liftedSkeleton_mem _ _ _ _).mpr
  refine ⟨baseVertex n d ω n,level_mem_occurrence n d ω n le_rfl
    (baseVertex_mem_level n d ω n),?_⟩
  rw [baseVertex_final n hn]

instance finsetVertexMeasurableSpace : MeasurableSpace (Finset Vertex) := ⊤
instance finsetVertexDiscreteMeasurableSpace : DiscreteMeasurableSpace (Finset Vertex) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

@[fun_prop] lemma measurable_liftedSkeleton (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) :
    Measurable (liftedSkeleton n d v) :=
  (measurable_of_countable (fun xs : List Vertex ↦ (xs.map (v+·)).toFinset)).comp
    (measurable_occurrenceList n d)

def ConnectedSkeleton (v w : Vertex) :=
  {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w}

instance instMeasurableSpaceConnectedSkeleton (v w : Vertex) : MeasurableSpace (ConnectedSkeleton v w) := inferInstanceAs
  (MeasurableSpace {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w})
instance instCountableConnectedSkeleton (v w : Vertex) : Countable (ConnectedSkeleton v w) := inferInstanceAs
  (Countable {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w})
instance instDiscreteMeasurableSpaceConnectedSkeleton (v w : Vertex) : DiscreteMeasurableSpace (ConnectedSkeleton v w) := inferInstanceAs
  (DiscreteMeasurableSpace {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w})

lemma exists_connected_detour {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hB : acceptedEnvironment (R+2) B v w) (Γ : ConnectedSkeleton v w) :
    ∃ p : SimpleGoodPath B (torusProjection K v) (torusProjection K w),
      ∀ x∈p.val.support, x∈Γ.val.image (torusProjection K) ∨
        shellAttachment R B (Γ.val.image (torusProjection K)) x := by
  obtain ⟨p,hp,ha⟩ := periodic_good_detour hK R B
    (small_star_of_no_large (by omega) B hB.1) Γ.val Γ.property.1 Γ.property.2.1
    hB.2 Γ.property.2.2
  exact ⟨⟨p,hp,fun x hx ↦ (ha x hx).1⟩,fun x hx ↦ (ha x hx).2⟩

def connectedDetour {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hB : acceptedEnvironment (R+2) B v w) (Γ : ConnectedSkeleton v w) :
    SimplePath (torusProjection K v) (torusProjection K w) :=
  forgetGood (Classical.choose (exists_connected_detour hK R B v w hB Γ))

def connectedSample (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    ConnectedSkeleton v (v+![(n:ℤ),d 0,d 1]) :=
  ⟨liftedSkeleton n d v ω,liftedSkeleton_initial n d v ω,liftedSkeleton_final n hn d v ω,
    by simpa only [baseVertex_initial,baseVertex_final n hn,add_zero] using
      liftedSkeleton_reach n d v ω⟩

@[fun_prop] lemma measurable_connectedSample (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) :
    Measurable (connectedSample n hn d v) := by
  exact Measurable.subtype_mk (measurable_liftedSkeleton n d v)

def dyadicDetour {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) (ω : Noise) :
    SimplePath (torusProjection K v) (torusProjection K (v+![(n:ℤ),d 0,d 1])) :=
  connectedDetour hK R B v _ hB (connectedSample n hn d v ω)

@[fun_prop] lemma measurable_dyadicDetour {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    Measurable (dyadicDetour hK R hn d v B hB) :=
  (measurable_of_countable (connectedDetour hK R B v _ hB)).comp
    (measurable_connectedSample n hn d v)

def nominalBase (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) : Fin (n+1) → Vertex :=
  fun i ↦ v+baseVertex n d ω i.val

def projectedSkeleton (K n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    Finset (DiscreteTorus K) := (liftedSkeleton n d v ω).image (torusProjection K)

def dyadicRadius (R : ℕ) : ℕ := candidateConstant (R+2)+4*(R+6)+1

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_AcceptedIntegrand
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

def acceptedIntegrand {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (κ : ℝ) (B : Finset (DiscreteTorus K)) (z : Noise×Noise) : ℝ≥0∞ :=
  if hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1]) then
    ENNReal.ofReal (Real.exp (κ*(simpleEncounter R (dyadicDetour hK R hn d v B hB z.1)
      (dyadicDetour hK R hn d v B hB z.2):ℝ))) else 0

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_Admissible
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

def currentAdmissiblePair {K : ℕ} [NeZero K] (x y : DiscreteTorus K) : Prop :=
  ∃ n : ℕ, K≤10*n ∧ 8*n≤K ∧ ∃ d : Fin 2 → ℤ, (∀ j, |d j|≤n) ∧
    y=x+![(n:ZMod K),(d 0:ZMod K),(d 1:ZMod K)]

def currentAdmissiblePairs (K : ℕ) [NeZero K] : Finset (DiscreteTorus K × DiscreteTorus K) :=
  Finset.univ.filter (fun z ↦ currentAdmissiblePair z.1 z.2)

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalScaleData
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable

structure PhysicalScaleBounds (m : ℕ) (t r R C S s₀ h : ℝ) (u : Time) : Prop where
  mesh_pos : 0  <  m
  time_pos : 0  <  t
  radius_pos : 0  <  r
  radius_le : r ≤ 1
  R_nonneg : 0 ≤ R
  C_nonneg : 0 ≤ C
  window_pos : 0  <  h
  prefix_eq : (u:ℝ)=h/(2*t)
  small : r*R ≤ 1
  separation : r+2*S ≤ s₀
  mesh_radius : (2*t)/(m:ℝ) ≤ r^2
  mesh_scale : (m:ℝ)*r^2 ≤ 2*(2*t)
  window : 2*((2*t)/(m:ℝ)) ≤ h
  large : 8*(2*t) ≤ (m:ℝ)*h
  drift : 26/(m:ℝ) ≤ r

variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def PhysicalMomentData {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) (q : ℝ≥0∞)
    (d : PhysicalDatum N K M G L) : Prop :=
  (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ) ≤ 2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
  (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card ≤ M) ∧
  (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
  (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
    physicalCollisionReference hL g m t r R C S u particle d j
      {p | TrialCollision r (projectCurve L f.val) p.val} ≤ q)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_ThermodynamicCalibration
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.Calibration

def scaleQ (a α n L : ℝ) : ℝ := Real.sqrt (a*n/(α*L))
def scaleK (a α n L : ℝ) : ℕ := ⌊scaleQ a α n L⌋₊

def densityLimit (a α ρ : ℝ) : ℝ := ρ/(Real.sqrt ((a/α)*ρ))^3

end HardSphere.Calibration

end
end

end OAI
end


