-- Prove2me | Definitions.Def_Q146C008
-- name    : Q146C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:12:58.800767+00:00
-- url     : https://prove2.me/theorems/3dd5fe7e-7fba-46ab-ba61-51bcbc33daed
-- title:
--   Definitions bundle Q146C008 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 190 declarations of OpenAI's Lean: 103 definitions, 1 inductive type or structure, 11 instances and 75 theorems. The definitions and types are `OAI.CircleDomainRigidity.PassesHitTests`, `OAI.CircleDomainRigidity.PrincipalConductivityScalarSolver`, `OAI.CircleDomainRigidity.RecursiveCodeGeometry.of_presentation`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.candidate`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.countable_dust_hits`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.density`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.domain_agrees`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.dust_eq`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.energy`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.energy_finite`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.extendedHitFlags`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.finite_hit_tests`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.flag_deletions_eq`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.hitConstant`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.levels_eq`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.occupationMass`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.occupationMass_finite`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.of_positive_candidate`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.physical_eq`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.presentation`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.prior_deletions_eq`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.quotient_eq`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.target_dust`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.tupleMass`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.visitConstant`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.visitConstant_finite`, `OAI.CircleDomainRigidity.RecursiveCodeLaw.weights_eq`, `OAI.CircleDomainRigidity.RecursiveLawWitness.candidate`, `OAI.CircleDomainRigidity.RecursiveLawWitness.hitConstant`, `OAI.CircleDomainRigidity.SavedSeparatingFamily.Holds`, `OAI.CircleDomainRigidity.SmallAnchoredPlateaus`, `OAI.CircleDomainRigidity.SmoothCompactMetricSphereUniformization`, `OAI.CircleDomainRigidity.SmoothJordanCore.inDomain`, `OAI.CircleDomainRigidity.WeightedCollar`, `OAI.CircleDomainRigidity.WeightedCollar.region`, `OAI.CircleDomainRigidity.WeightedCollar.retarget`, `OAI.CircleDomainRigidity.activeSlotPairs`, `OAI.CircleDomainRigidity.activeSlotParameterEvent`, `OAI.CircleDomainRigidity.affineRectifiablePath`, `OAI.CircleDomainRigidity.affineRestrictedTaggedPath` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CircleDomains_Modulus_ActualOneEndedBudget`, `CircleDomains_Modulus_ActualTwoEndedBudget`, `CircleDomains_Modulus_AdmissiblePathCost`, `CircleDomains_Modulus_AffinePhysicalArclength`, `CircleDomains_Modulus_AffineRectifiableLength`, `CircleDomains_Modulus_ConstrainedCostCodes`, `CircleDomains_Modulus_CountablePhysicalCost`, `CircleDomains_Modulus_CountablePhysicalLength`, `CircleDomains_Modulus_IntervalChartCost`, `CircleDomains_Modulus_JoinedPhysicalCost`, `CircleDomains_Modulus_NormalizedUniformBounds`, `CircleDomains_Modulus_PathLengthLocality`, `CircleDomains_Modulus_PersistentSavedBarriers`, `CircleDomains_Modulus_PhysicalLengthCharacterization`, `CircleDomains_Modulus_PhysicalPieceLength`, `CircleDomains_Modulus_PhysicalTagPayment`, `CircleDomains_Modulus_RetaggedCost`, `CircleDomains_Modulus_ReversedPhysicalLength`, `CircleDomains_Modulus_WeightedCollarNeighborhoods`, `CircleDomains_Probability_AffinePhysicalTimeMeasure`, `CircleDomains_Probability_AffineTimeMeasure`, `CircleDomains_Probability_CodeHitMeasures`, `CircleDomains_Probability_CodeLawMeasures`, `CircleDomains_Probability_CodePairOccupation`, `CircleDomains_Probability_CodePathLaws`, `CircleDomains_Probability_ConstrainedCodeLaws`, `CircleDomains_Probability_DomainPhysicalOccupation`, `CircleDomains_Probability_FusionSmallSets`, `CircleDomains_Probability_MeanVisitDensity`, `CircleDomains_Probability_ParametricNullTuples`, `CircleDomains_Probability_PathCostMeasure`, `CircleDomains_Probability_PathOccupation`, `CircleDomains_Probability_PhysicalPieceTimeMeasure`, `CircleDomains_Probability_RectifiableOccupationCode`, `CircleDomains_Probability_RecursiveCodeLaw`, `CircleDomains_Probability_RecursiveLawConstruction`, `CircleDomains_Probability_ReversedPhysicalOccupation`, `CircleDomains_Probability_SlotLawMeasures`, `CircleDomains_Probability_SlotPairNull`, `CircleDomains_Probability_TerminalPathMeasurability`, `CircleDomains_Rigidity_ConductivityContraction`, `CircleDomains_Rigidity_ConjugateBeltramiL2`, `CircleDomains_Rigidity_PrincipalScalarSolver`, `CircleDomains_Selection_AffineTagRestriction`, `CircleDomains_Selection_CodeConstraints`, `CircleDomains_Selection_ConcatenatedTags`, `CircleDomains_Selection_FiniteMarkedTrapping`, `CircleDomains_Selection_FirstExitFragmentArray`, `CircleDomains_Selection_FullDomainPhysicalLift`, `CircleDomains_Selection_IndependentTagLevel`, `CircleDomains_Selection_InitialBlockPiece`, `CircleDomains_Selection_LastEntryFragmentArray`, `CircleDomains_Selection_LocalHeightDifference`, `CircleDomains_Selection_PhysicalTimeSupport`, `CircleDomains_Selection_PrependNewBlockJump`, `CircleDomains_Selection_PrependOldBlockJump`, `CircleDomains_Selection_RealCoordinateFamily`, `CircleDomains_Selection_SelectedRealSmallness`, `CircleDomains_Selection_SignedScalarTests`, `CircleDomains_Selection_SparseBaseCodes`, `CircleDomains_Selection_TagCodeSpace`, `CircleDomains_Selection_VisitCounts`, `CircleDomains_Sobolev_FiniteSphericalArea`, `CircleDomains_Sobolev_LipschitzIntervalPaths`, `CircleDomains_Sobolev_MetricChartEnergy`, `CircleDomains_Sobolev_SmoothPlaneEnergyTransport`, `CircleDomains_Sobolev_SphereRealDifferential`, `CircleDomains_Sobolev_TransportedRealEnergy`, `CircleDomains_Sobolev_WeakHeightIdentification`, `CircleDomains_Topology_AffineClippedIntervals`, `CircleDomains_Topology_AffinePathTime`, `CircleDomains_Topology_AllowedCollarConcatenation`, `CircleDomains_Topology_CircleComponentCoordinates`, `CircleDomains_Topology_ClosedJordanCore`, `CircleDomains_Topology_CountablePathConcatenation`, `CircleDomains_Topology_DomainPhysicalPaths`, `CircleDomains_Topology_DyadicOpenCover`, `CircleDomains_Topology_EmbeddedPathTags`, `CircleDomains_Topology_ExteriorSeparation`, `CircleDomains_Topology_FiniteTerminalDisks`, `CircleDomains_Topology_IntervalPath`, `CircleDomains_Topology_JoinedPaths`, `CircleDomains_Topology_JoinedPhysicalPaths`, `CircleDomains_Topology_PathTags`, `CircleDomains_Topology_PlaneQuotientRepresentative`, `CircleDomains_Topology_RetargetedCollars`, `CircleDomains_Topology_SaturatedDisks`, `CircleDomains_Topology_SourceMapNeighborhood`, `CircleDomains_Topology_SphereJordanCoordinates`, `CircleDomains_Topology_SubarcPointAvoidance`, `CircleDomains_Topology_TerminalBoundaryLimits`, `CircleDomains_Transfer_EmptyDustScalarModel`, `CircleDomains_Transfer_SourceTargetEnds`, `CircleDomains_Transfer_TransportedTerminalBranches`, `CircleDomains_Uniformization_Conformal`, `CircleDomains_Uniformization_SmoothMetricUniformization`, `SquareMeshConnected`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundles `Q146C003`, `Q146C004` and `Q146C005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q146C010`; the statements `OAI.CircleDomainRigidity.FiniteTransfer.exists_countable_mixed_stages`, `OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels`, `OAI.CircleDomainRigidity.barrier_modulus_lower_bound`, `OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential`, `OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar`, `OAI.CircleDomainRigidity.exists_small_selected_height_data`, `OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier`, `OAI.CircleDomainRigidity.principalConductivityScalarSolver` and `OAI.CircleDomainRigidity.smoothCompactMetricSphereUniformization`; the proofs of `OAI.CircleDomainRigidity.barrier_modulus_lower_bound`, `OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential`, `OAI.CircleDomainRigidity.exists_principal_conductivity_energy_scalar`, `OAI.CircleDomainRigidity.exteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem`, `OAI.CircleDomainRigidity.prescribed_countable_law_of_no_small_level_barrier` and `OAI.CircleDomainRigidity.smoothCompactMetricSphereUniformization`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C003
import Definitions.Def_Q146C004
import Definitions.Def_Q146C005

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite visit witnesses have Borel incidence. The resulting extended count
records visits at distinct parameter times, including both endpoints. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def meanVisitCount (μ : ProbabilityMeasure C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  ∫⁻ γ, visitCount γ x ∂(μ : Measure C(PathTime, X))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient tagged-path code space and its compact residual-time sections.
An active slot contains a nonempty finite label tuple, its circle levels,
and the two ends of its open time interval. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

instance instSecondCountableTopologyTagSlot : SecondCountableTopology TagSlot :=
  inferInstanceAs (SecondCountableTopology (Unit ⊕ TagData))

instance instBorelSpaceTagSlot : BorelSpace TagSlot := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffinePathTime
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing affine restriction maps and their clipped inverse on the
standard path interval. Interior inequalities remain exact after clipping. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem affinePathTime_mem_Icc {a b : PathTime} (hab : a ≤ b) (t : PathTime) :
    affinePathTime a b t ∈ Icc a b := by
  have hmono : Monotone (affinePathTime a b) := by
    rcases hab.eq_or_lt with rfl | hlt
    · intro s t _
      simp [affinePathTime, Set.Icc.convexComb_eq]
    · exact (affinePathTime_strictMono hlt).monotone
  constructor
  · simpa only [affinePathTime_zero] using hmono (bot_le : (⊥ : PathTime) ≤ t)
  · simpa only [affinePathTime_one] using hmono (le_top : t ≤ (⊤ : PathTime))

theorem rescalePathTime_coe (a b t : PathTime) :
    (rescalePathTime a b t : ℝ) = max 0 (min 1 (((t : ℝ) - a) / ((b : ℝ) - a))) := rfl

theorem rescale_affinePathTime {a b : PathTime} (hab : a < b) (t : PathTime) :
    rescalePathTime a b (affinePathTime a b t) = t := by
  apply Subtype.ext
  rw [rescalePathTime_coe, affinePathTime_coe]
  have he : (((b : ℝ) - a) * t + a - a) / ((b : ℝ) - a) = t := by
    field_simp [ne_of_gt (sub_pos.mpr (show (a : ℝ) < b from hab))]
    ring
  rw [he, min_eq_right t.property.2, max_eq_right t.property.1]

theorem affine_rescalePathTime {a b : PathTime} (hab : a < b) {t : PathTime}
    (ht : t ∈ Icc a b) : affinePathTime a b (rescalePathTime a b t) = t := by
  have hden : 0 < (b : ℝ) - a := sub_pos.mpr hab
  have hzero : 0 ≤ ((t : ℝ) - a) / ((b : ℝ) - a) :=
    div_nonneg (sub_nonneg.mpr ht.1) hden.le
  have hone : ((t : ℝ) - a) / ((b : ℝ) - a) ≤ 1 := by
    apply (div_le_one hden).mpr
    exact sub_le_sub_right (show (t : ℝ) ≤ b from ht.2) _
  apply Subtype.ext
  rw [affinePathTime_coe, rescalePathTime_coe, min_eq_right hone, max_eq_right hzero]
  field_simp
  ring

theorem range_affinePathTime {a b : PathTime} (hab : a < b) :
    range (affinePathTime a b) = Icc a b := by
  apply Subset.antisymm
  · rintro t ⟨s, rfl⟩
    exact affinePathTime_mem_Icc hab.le s
  · intro t ht
    exact ⟨rescalePathTime a b t, affine_rescalePathTime hab ht⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountablePathConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual countable path concatenation, including the new limiting endpoint.
The shrinking-tail hypothesis is the one supplied by nested dust collars. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def collarPiece (γ : ℕ → C(PathTime, X)) (n : ℕ) : C(PathTime, X) :=
  (γ n).comp (rescalePathTime (collarTime (n + 1)) (collarTime n))

theorem collarPiece_lower (γ : ℕ → C(PathTime, X)) (n : ℕ) :
    collarPiece γ n (collarTime (n + 1)) = γ n ⊥ := by
  have h := rescale_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n)) ⊥
  rw [affinePathTime_zero] at h
  change γ n _ = γ n ⊥
  rw [h]

theorem collarPiece_upper (γ : ℕ → C(PathTime, X)) (n : ℕ) :
    collarPiece γ n (collarTime n) = γ n ⊤ := by
  have h := rescale_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n)) ⊤
  rw [affinePathTime_one] at h
  change γ n _ = γ n ⊤
  rw [h]

theorem collarPieces_agree (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥) {i j : ℕ} {t : PathTime}
    (hi : t ∈ collarCell i) (hj : t ∈ collarCell j) :
    collarPiece γ i t = collarPiece γ j t := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi (Nat.le_of_not_ge hij)).symm
  rcases hij.eq_or_lt with rfl | hij
  · rfl
  have hji : j ≤ i + 1 := by
    by_contra hn
    have hb := collarTime_strictAnti (Nat.lt_of_not_ge hn)
    exact (hj.2.trans_lt hb).not_ge hi.1
  have heq : j = i + 1 := le_antisymm hji (Nat.succ_le_of_lt hij)
  subst j
  have ht : t = collarTime (i + 1) := le_antisymm hj.2 hi.1
  rw [ht, collarPiece_lower, collarPiece_upper, hjoin]

def collarConcatenationFun (p : X) (γ : ℕ → C(PathTime, X)) (t : PathTime) : X :=
  if t = ⊥ then p else collarPiece γ (collarPieceIndex t) t

theorem collarConcatenation_on_cell (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥) (n : ℕ) {t : PathTime}
    (ht : t ∈ collarCell n) :
    collarConcatenationFun p γ t = collarPiece γ n t := by
  have hpos : ⊥ < t := (collarTime_pos (n + 1)).trans_le ht.1
  rw [collarConcatenationFun, ite_eq_right (ne_of_gt hpos)]
  exact collarPieces_agree γ hjoin
    ⟨(collarPieceIndex_spec hpos).1.le, (collarPieceIndex_spec hpos).2⟩ ht

theorem collarConcatenation_continuous_positive (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥) :
    Continuous (fun t : PositivePathTime => collarConcatenationFun p γ t) := by
  apply collarCells_locallyFinite.continuous collarCells_cover_positive
  · intro n
    exact isClosed_Icc.preimage continuous_subtype_val
  · intro n
    apply ((collarPiece γ n).continuous.comp continuous_subtype_val).continuousOn.congr
    intro t ht
    exact collarConcatenation_on_cell p γ hjoin n ht

theorem collarConcatenation_continuous (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, γ n s ∈ V) :
    Continuous (collarConcatenationFun p γ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = ⊥
  · subst t
    change Tendsto _ _ (𝓝 (collarConcatenationFun p γ ⊥))
    have heq : collarConcatenationFun p γ ⊥ = p := by
      simp [collarConcatenationFun]
    rw [heq]
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨N, hN⟩ := htail V hV
    filter_upwards [gt_mem_nhds (collarTime_pos N)] with t ht
    change collarConcatenationFun p γ t ∈ V
    by_cases ht0 : t = ⊥
    · simpa only [collarConcatenationFun, ite_eq_left ht0] using mem_of_mem_nhds hV
    · have hpos : ⊥ < t := bot_lt_iff_ne_bot.mpr ht0
      have hidx : N ≤ collarPieceIndex t := by
        by_contra hn
        have hb := collarTime_strictAnti.antitone
          (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
        exact (ht.trans_le hb).not_ge (collarPieceIndex_spec hpos).1.le
      simp only [collarConcatenationFun, ite_eq_right ht0, collarPiece, ContinuousMap.comp_apply]
      exact hN _ hidx _
  · have hpos : t ∈ Ioi (⊥ : PathTime) := bot_lt_iff_ne_bot.mpr ht
    have hcont : ContinuousOn (collarConcatenationFun p γ) (Ioi ⊥) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (collarConcatenation_continuous_positive p γ hjoin)
    exact (hcont t hpos).continuousAt (isOpen_Ioi.mem_nhds hpos)

def collarConcatenation (p : X) (γ : ℕ → C(PathTime, X))
    (hjoin : ∀ n, γ (n + 1) ⊤ = γ n ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, γ n s ∈ V) : C(PathTime, X) :=
  ⟨collarConcatenationFun p γ, collarConcatenation_continuous p γ hjoin htail⟩

theorem collarConcatenation_affine (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (n : ℕ) (s : PathTime) :
    collarConcatenation p γ hjoin htail
      (affinePathTime (collarTime (n + 1)) (collarTime n) s) = γ n s := by
  change collarConcatenationFun p γ _ = _
  rw [collarConcatenation_on_cell p γ hjoin n
    (affinePathTime_mem_Icc (collarTime_strictAnti (Nat.lt_succ_self n)).le s)]
  change γ n _ = γ n s
  rw [rescale_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n))]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a rectifiable metric path, and its mean under a law.
The measure records arclength with multiplicity, including repeated traversals. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

instance instIsFiniteMeasurePathOccupation (γ : RectifiablePath X) : IsFiniteMeasure (pathOccupation γ) := by
  unfold pathOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagCodeSpace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Borel ambient codes and Borel simultaneous tag rules. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

instance instIsCompletelyMetrizableSpaceTagSlot : IsCompletelyMetrizableSpace TagSlot := by
  let : ∀ n : ℕ, IsCompletelyMetrizableSpace (TagParameters n) := fun _ => by infer_instance
  let : IsCompletelyMetrizableSpace TagData := by infer_instance
  change IsCompletelyMetrizableSpace (Unit ⊕ TagData)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instPolishSpaceTagSlot : PolishSpace TagSlot := by infer_instance

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

instance instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology [CompleteSpace X] [SecondCountableTopology X] : StandardBorelSpace (TaggedPath X) := by
  let : PolishSpace C(PathTime, X) := by infer_instance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RectifiableOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel occupation code on the Borel subset of rectifiable paths.
The total extension is zero off that subset; length finiteness is always
checked separately before it is used as physical occupation. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

instance instIsFiniteMeasureRectifiableOccupationCode (γ : C(PathTime, X)) : IsFiniteMeasure (rectifiableOccupationCode γ) := by
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableOccupationCode_eq hγ]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  · simp only [rectifiableOccupationCode, dite_eq_right hγ]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathLengthLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time arclength is local on closed intervals and adds at shared endpoints. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

instance instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode (γ : C(PathTime, X)) : IsFiniteMeasure (rectifiableLengthCode γ) := by
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableLengthCode_eq hγ]; infer_instance
  · simp only [rectifiableLengthCode, dite_eq_right hγ]; infer_instance

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalTimeSupport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The time arclength measure gives no mass to times outside the physical domain. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalStageTimeLength_compl (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageTimeLength e y₀ n γ.val (γ.val ⁻¹' U)ᶜ = 0 := by
  classical
  have hm := (hU.preimage γ.val.continuous).measurableSet.compl
  simp only [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) _ hr,
      Measure.restrict_apply hm]
    have he : (γ.val ⁻¹' U)ᶜ ∩ Icc (dyadicLeft n i) (dyadicRight n i) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro t ⟨ht, hcell⟩
      exact ht (hi hcell)
    rw [he, measure_empty]
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi, rectifiableLengthCode_const]

theorem physicalTimeLength_compl (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalTimeLength e y₀ γ (γ.val ⁻¹' U)ᶜ = 0 := by
  rw [physicalTimeLength_apply _ _ _ (hU.preimage γ.val.continuous).measurableSet.compl]
  simp [physicalStageTimeLength_compl e hU y₀ γ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DyadicOpenCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable cover of an open time set by closed dyadic intervals inside it. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_dyadicCell_mem (n : ℕ) (t : PathTime) :
    ∃ i : Fin (2 ^ n), t ∈ Icc (dyadicLeft n i) (dyadicRight n i) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    have hl : dyadicLeft 0 0 = ⊥ := (dyadicNode_left 0 0).symm.trans (dyadicNode_zero 0)
    have hr : dyadicRight 0 0 = ⊤ := (dyadicNode_right 0 0).symm.trans (dyadicNode_last 0)
    rw [hl, hr, Icc_bot_top]
    exact mem_univ t
  | succ n ih =>
    obtain ⟨i, hi⟩ := ih
    rw [dyadicCell_split] at hi
    rcases hi with hi | hi
    · exact ⟨dyadicEven n i, hi⟩
    · exact ⟨dyadicOdd n i, hi⟩

def insideDyadicCell {V : Set PathTime} (p : DyadicInside V) : Set PathTime :=
  Icc (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2)

theorem iUnion_insideDyadicCell {V : Set PathTime} (hV : IsOpen V) :
    (⋃ p : DyadicInside V, insideDyadicCell p) = V := by
  apply Subset.antisymm
  · exact iUnion_subset fun p => p.property
  · intro t ht
    obtain ⟨n, hn⟩ := exists_dyadic_cells_inside hV (a := t) (b := t) (by simpa)
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem n t
    have hgood := hn i ⟨t, hi, by simp⟩
    exact mem_iUnion.mpr ⟨⟨⟨n, i⟩, hgood⟩, hi⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalLengthCharacterization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness and compact-interval exhaustion of physical-domain arclength.
This identifies the dyadic construction with ordinary arclength on all open
domain-time components, including paths that revisit points. -/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem measure_eq_of_compact_time_restrictions {V : Set PathTime} (hV : IsOpen V)
    (μ ν : Measure PathTime) (hμ : μ Vᶜ = 0) (hν : ν Vᶜ = 0)
    (hlocal : ∀ a b : PathTime, a ≤ b → Icc a b ⊆ V →
      μ.restrict (Icc a b) = ν.restrict (Icc a b)) : μ = ν := by
  have hm : μ.restrict V = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hμ)
  have hn : ν.restrict V = ν := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hν)
  rw [← hm, ← hn, ← iUnion_insideDyadicCell hV]
  apply Measure.restrict_iUnion_congr.mpr
  intro p
  exact hlocal _ _ (dyadicLeft_le_right p.val.1 p.val.2) p.property

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalTimeLength_unique (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (μ : Measure PathTime)
    (hμ : μ (γ.val ⁻¹' U)ᶜ = 0)
    (hlocal : ∀ (a b : PathTime) (hab : a ≤ b)
      (hγ : γ.val ∈ pathsInsideOn U a b),
      μ.restrict (Icc a b) = rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)) :
    μ = physicalTimeLength e y₀ γ := by
  apply measure_eq_of_compact_time_restrictions (hU.preimage γ.val.continuous)
    μ _ hμ (physicalTimeLength_compl e hU y₀ γ)
  intro a b hab hγ
  exact (hlocal a b hab hγ).trans (physicalTimeLength_restrict_compact e hU y₀ γ hab hγ).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AffineTagRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual affine restriction of tagged paths. Reparameterized tags keep
their old tuples; empty and constant tag pieces become inactive. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def affineRestrictedTaggedPath (a b : PathTime) (Γ : TaggedPath X) : TaggedPath X :=
  (affineRestrictedPath a b Γ.1, fun k => affineRestrictedTag a b Γ.1 (Γ.2 k))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffineClippedIntervals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine time coordinates commute with clipping to an overlapping
 interval. This permits length estimates across collar junctions. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem affine_rescale_eq_clip {a b : PathTime} (hab : a < b) (t : PathTime) :
    affinePathTime a b (rescalePathTime a b t) = timeClip a b t := by
  rcases le_total t a with hta | hat
  · have hr : rescalePathTime a b t = ⊥ := by
      apply Subtype.ext
      rw [rescalePathTime_coe]
      have hq : ((t : ℝ) - a) / ((b : ℝ) - a) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hta) (sub_nonneg.mpr hab.le)
      change max 0 (min 1 _) = 0
      exact max_eq_left ((min_le_right _ _).trans hq)
    rw [hr, affinePathTime_zero]
    change a = max a (min b t)
    exact (max_eq_left ((min_le_right _ _).trans hta)).symm
  · rcases le_total b t with hbt | htb
    · have hr : rescalePathTime a b t = ⊤ := by
        apply Subtype.ext
        rw [rescalePathTime_coe]
        have hq : 1 ≤ ((t : ℝ) - a) / ((b : ℝ) - a) := by
          apply (le_div_iff₀ (sub_pos.mpr (show (a : ℝ) < b from hab))).mpr
          linarith [show (b : ℝ) ≤ t from hbt]
        change max 0 (min 1 _) = 1
        rw [min_eq_left hq]
        norm_num
      rw [hr, affinePathTime_one]
      change b = max a (min b t)
      rw [min_eq_left hbt, max_eq_right hab.le]
    · rw [affine_rescalePathTime hab ⟨hat, htb⟩]
      change t = max a (min b t)
      rw [min_eq_right htb, max_eq_right hat]

/-- The overlap assumption excludes the case of two disjoint clipping intervals. -/
theorem affine_clip_rescaled {a b : PathTime} (hab : a < b) {c d : PathTime}
    (hc : c ≤ b) (hd : a ≤ d) (t : PathTime) :
    affinePathTime a b (timeClip (rescalePathTime a b c) (rescalePathTime a b d) t) =
      timeClip c d (affinePathTime a b t) := by
  rw [affinePathTime_clip hab, affine_rescale_eq_clip hab, affine_rescale_eq_clip hab]
  have hm := affinePathTime_mem_Icc hab.le t
  change max (max a (min b c)) (min (max a (min b d)) _) = max c (min d _)
  rw [min_eq_right hc, min_max_distrib_right, min_eq_left hm.1,
    min_assoc, min_left_comm b d _, min_eq_right hm.2,
    ← max_assoc, max_right_comm a c a, max_self, max_assoc, max_left_comm a c _,
    max_eq_right (le_min hd hm.1)]

theorem rescalePathTime_monotone {a b : PathTime} (hab : a < b) :
    Monotone (rescalePathTime a b) := by
  intro s t hst
  change (rescalePathTime a b s : ℝ) ≤ (rescalePathTime a b t : ℝ)
  simp only [rescalePathTime_coe]
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  exact div_le_div_of_nonneg_right (sub_le_sub_right (show (s : ℝ) ≤ t from hst) _) (sub_nonneg.mpr hab.le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalPieceLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local physical arclength of a glued path is charged to the original
piece, without assuming in advance that the glued path is rectifiable. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalSubpath_piece_length (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (η : C(PathTime, X))
    {a b : PathTime} (hab : a < b)
    (hmatch : ∀ s, η (affinePathTime a b s) = γ.val s)
    {c d : PathTime} (hcd : c ≤ d) (hη : η ∈ pathsInsideOn U c d) :
    eVariationOn (physicalSubpath e hcd ⟨η, hη⟩) (Icc a b) ≤
      physicalTimeLength e y₀ γ (Icc (rescalePathTime a b c) (rescalePathTime a b d)) := by
  by_cases hi : (Icc c d ∩ Icc a b).Nonempty
  · obtain ⟨t, ht, htab⟩ := hi
    have hc : c ≤ b := ht.1.trans htab.2
    have hd : a ≤ d := htab.1.trans ht.2
    have hκ := rescalePathTime_monotone hab hcd
    have hγ : γ.val ∈ pathsInsideOn U (rescalePathTime a b c) (rescalePathTime a b d) := by
      intro s hs
      rw [← hmatch]
      apply hη
      constructor
      · have hh := (affinePathTime_strictMono hab).monotone hs.1
        rw [affine_rescale_eq_clip hab] at hh
        have hlo : c ≤ timeClip a b c := by
          change c ≤ max a (min b c)
          rw [min_eq_right hc]
          exact le_max_right _ _
        exact hlo.trans hh
      · have hh := (affinePathTime_strictMono hab).monotone hs.2
        rw [affine_rescale_eq_clip hab] at hh
        exact hh.trans (max_le hd (min_le_right _ _))
    have heq : (physicalSubpath e hcd ⟨η, hη⟩).comp (affinePathTime a b) =
        physicalSubpath e hκ ⟨γ.val, hγ⟩ := by
      apply ContinuousMap.ext
      intro s
      apply congrArg Subtype.val
      apply congrArg e.symm
      apply Subtype.ext
      change η (timeClip c d (affinePathTime a b s)) =
        γ.val (timeClip (rescalePathTime a b c) (rescalePathTime a b d) s)
      rw [← hmatch, affine_clip_rescaled hab hc hd]
    have hv := eVariationOn.comp_eq_of_monotoneOn
      (physicalSubpath e hcd ⟨η, hη⟩) (affinePathTime a b)
      ((affinePathTime_strictMono hab).monotone.monotoneOn univ)
    rw [image_univ, range_affinePathTime hab] at hv
    have hv' : eVariationOn ((physicalSubpath e hcd ⟨η, hη⟩).comp
        (affinePathTime a b)) univ = eVariationOn (physicalSubpath e hcd ⟨η, hη⟩) (Icc a b) := hv
    rw [← hv', heq, ← physicalTimeLength_compact_mass e hU y₀ γ hκ hγ]
  · have hconst := timeClip_eq_const_of_disjoint hcd hab.le hi
    have hz : eVariationOn (physicalSubpath e hcd ⟨η, hη⟩) (Icc a b) = 0 := by
      apply (eVariationOn.eq_zero_iff _).mpr
      intro s hs t ht
      have hst : timeClip c d s = timeClip c d t := by
        rcases hconst with hconst | hconst <;> exact (hconst hs).trans (hconst ht).symm
      have heq : physicalSubpath e hcd ⟨η, hη⟩ s = physicalSubpath e hcd ⟨η, hη⟩ t := by
        apply congrArg Subtype.val
        apply congrArg e.symm
        exact Subtype.ext (congrArg η hst)
      rw [heq, edist_self]
    rw [hz]
    exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountablePhysicalLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite physical length of the actual collar concatenation. The bound
is proved before applying allowed-path stability. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalDyadicLength_collarPieces_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : ℕ → FinitePhysicalPath e y₀) (η : C(PathTime, X))
    (hmatch : ∀ n s, η (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s)
    (k : ℕ) (i : Fin (2 ^ k)) :
    physicalDyadicLength e y₀ k i η ≤
      ∑' n, physicalTimeLength e y₀ (γ n)
        (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
          (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i))) := by
  by_cases hη : η ∈ pathsInsideOn U (dyadicLeft k i) (dyadicRight k i)
  · rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ k i η hη,
      collar_variation_sum]
    apply ENNReal.tsum_le_tsum
    intro n
    exact physicalSubpath_piece_length e hU y₀ (γ n) η
      (collarTime_strictAnti (Nat.lt_succ_self n)) (hmatch n) (dyadicLeft_le_right k i) hη
  · simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hη]
    have hz : eVariationOn (ContinuousMap.const PathTime y₀) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
    rw [hz]
    exact bot_le

theorem physicalDomainLength_collarPieces_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : ℕ → FinitePhysicalPath e y₀) (η : C(PathTime, X))
    (hmatch : ∀ n s, η (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s) :
    physicalDomainLength e y₀ η ≤ ∑' n, physicalDomainLength e y₀ (γ n).val := by
  apply iSup_le
  intro k
  calc
    physicalStageLength e y₀ k η ≤
        ∑ i : Fin (2 ^ k), ∑' n, physicalTimeLength e y₀ (γ n)
          (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
            (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i))) :=
      Finset.sum_le_sum fun i _ => physicalDyadicLength_collarPieces_le e hU y₀ γ η hmatch k i
    _ = ∑' n, ∑ i : Fin (2 ^ k), physicalTimeLength e y₀ (γ n)
          (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
            (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i))) := by
      simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun i : Fin (2 ^ k) =>
        fun n => physicalTimeLength e y₀ (γ n)
          (Icc (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicLeft k i))
            (rescalePathTime (collarTime (n + 1)) (collarTime n) (dyadicRight k i)))))
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [sum_monotone_dyadic_mass _ _
        (rescalePathTime_monotone (collarTime_strictAnti (Nat.lt_succ_self n))),
        ← physicalTimeLength_univ e y₀ (γ n)]
      exact measure_mono (subset_univ _)

def finitePhysicalCollarConcatenation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (p : X) (γ : ℕ → FinitePhysicalPath e y₀)
    (hjoin : ∀ n, (γ (n + 1)).val ⊤ = (γ n).val ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, (γ n).val s ∈ V)
    (hfinite : (∑' n, physicalDomainLength e y₀ (γ n).val) < ∞) :
    FinitePhysicalPath e y₀ :=
  ⟨collarConcatenation p (fun n => (γ n).val) hjoin htail,
    (physicalDomainLength_collarPieces_le e hU y₀ γ _
      (collarConcatenation_affine p (fun n => (γ n).val) hjoin htail)).trans_lt hfinite⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffineTimeMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise pullback of an arbitrary time measure to a retained affine
interval. This is the measure identity used for arclength restriction. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

theorem preimage_rescale_Icc {a b : PathTime} (hab : a < b) (c d : PathTime) :
    rescalePathTime a b ⁻¹' Icc c d ∩ Icc a b =
      Icc (affinePathTime a b c) (affinePathTime a b d) := by
  have hf := affinePathTime_strictMono hab
  ext t
  constructor
  · rintro ⟨ht, habt⟩
    have he := affine_rescalePathTime hab habt
    constructor
    · simpa only [he] using hf.monotone ht.1
    · simpa only [he] using hf.monotone ht.2
  · intro ht
    have hct := affinePathTime_mem_Icc hab.le c
    have hdt := affinePathTime_mem_Icc hab.le d
    have htab : t ∈ Icc a b := ⟨hct.1.trans ht.1, ht.2.trans hdt.2⟩
    have he := affine_rescalePathTime hab htab
    refine ⟨⟨?_, ?_⟩, htab⟩
    · apply hf.le_iff_le.mp
      rw [he]
      exact ht.1
    · apply hf.le_iff_le.mp
      rw [he]
      exact ht.2

theorem map_rescale_restrict_Icc (μ : Measure PathTime) {a b : PathTime}
    (hab : a < b) (c d : PathTime) :
    ((μ.restrict (Icc a b)).map (rescalePathTime a b)) (Icc c d) =
      μ (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
  rw [Measure.map_apply (rescalePathTime a b).continuous.measurable measurableSet_Icc,
    Measure.restrict_apply ((rescalePathTime a b).continuous.measurable measurableSet_Icc),
    preimage_rescale_Icc hab]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_AffineRectifiableLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arclength transformation of an affine restriction of a
rectifiable metric path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def affineRectifiablePath (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    RectifiablePath X :=
  ⟨affineRestrictedPath a b γ.val,
    lt_top_iff_ne_top.mp ((eVariationOn.comp_le_of_monotoneOn γ.val (affinePathTime a b)
      ((affinePathTime_strictMono hab).monotone.monotoneOn _) (fun _ _ => mem_univ _)).trans_lt
        (lt_top_iff_ne_top.mpr γ.property))⟩

theorem pathLengthMeasure_affine_Icc (γ : RectifiablePath X) {a b : PathTime}
    (hab : a < b) {c d : PathTime} (hcd : c ≤ d) :
    pathLengthMeasure (affineRectifiablePath γ hab) (Icc c d) =
      pathLengthMeasure γ (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
  rw [pathLengthMeasure_Icc _ hcd,
    pathLengthMeasure_Icc _ ((affinePathTime_strictMono hab).monotone hcd)]
  change eVariationOn (γ.val ∘ affinePathTime a b) (Icc c d) = _
  rw [eVariationOn.comp_eq_of_monotoneOn γ.val (affinePathTime a b)
    ((affinePathTime_strictMono hab).monotone.monotoneOn _),
    (affinePathTime a b).continuous.image_Icc_of_strictMono (affinePathTime_strictMono hab)]

theorem pathLengthMeasure_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    pathLengthMeasure (affineRectifiablePath γ hab) =
      ((pathLengthMeasure γ).restrict (Icc a b)).map (rescalePathTime a b) := by
  apply Measure.ext_of_Icc
  intro c d hcd
  rw [pathLengthMeasure_affine_Icc γ hab hcd, map_rescale_restrict_Icc _ hab]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_AffinePhysicalArclength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arclength of a physical compact subpath after affine restriction.
Constant extension outside the subpath adds no endpoint mass. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalSubpath_affine_lengthCode (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    {c d : PathTime} (hcd : c ≤ d)
    (hγ : affineRestrictedPath a b γ.val ∈ pathsInsideOn U c d) :
    rectifiableLengthCode (physicalSubpath e hcd ⟨affineRestrictedPath a b γ.val, hγ⟩) =
      (rectifiableLengthCode (physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
        ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩)).map (rescalePathTime a b) := by
  let β : RectifiablePath Y :=
    ⟨physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
      ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩,
      physicalSubpath_rectifiable e hU _ γ.val _ y₀ γ.property⟩
  have hfun : physicalSubpath e hcd ⟨affineRestrictedPath a b γ.val, hγ⟩ =
      (affineRectifiablePath β hab).val := physicalSubpath_affine e hab γ.val hcd hγ
  have hportion : pathLengthMeasure β =
      (pathLengthMeasure β).restrict
        (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
    have h := physicalSubpath_timeLength_portion e
      ((affinePathTime_strictMono hab).monotone hcd)
      ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩ β.property
    rw [rectifiableLengthCode_eq β.property] at h
    exact h
  have hsub : Icc (affinePathTime a b c) (affinePathTime a b d) ⊆ Icc a b := by
    intro t ht
    exact ⟨(affinePathTime_mem_Icc hab.le c).1.trans ht.1,
      ht.2.trans (affinePathTime_mem_Icc hab.le d).2⟩
  have hsupport : (pathLengthMeasure β).restrict (Icc a b) = pathLengthMeasure β := by
    nth_rw 1 [hportion]
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_right.mpr hsub, ← hportion]
  rw [hfun, rectifiableLengthCode_eq (affineRectifiablePath β hab).property,
    pathLengthMeasure_affine, hsupport, rectifiableLengthCode_eq β.property]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffinePhysicalTimeMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical-domain time measure of a restricted path. The proof
identifies local arclength and the support in the open domain. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalTimeLength_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalTimeLength e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) =
      ((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b) := by
  symm
  apply physicalTimeLength_unique e hU y₀ (affineFinitePhysicalPath e hU y₀ γ hab)
  · change (((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b))
      ((affineRestrictedPath a b γ.val) ⁻¹' U)ᶜ = 0
    have hmeas : MeasurableSet ((affineRestrictedPath a b γ.val) ⁻¹' U)ᶜ :=
      (hU.preimage (affineRestrictedPath a b γ.val).continuous).measurableSet.compl
    rw [Measure.map_apply (rescalePathTime a b).continuous.measurable hmeas,
      Measure.restrict_apply ((rescalePathTime a b).continuous.measurable hmeas)]
    apply measure_mono_null _ (physicalTimeLength_compl e hU y₀ γ)
    rintro t ⟨ht, htab⟩ hmem
    apply ht
    change γ.val (affinePathTime a b (rescalePathTime a b t)) ∈ U
    rwa [affine_rescalePathTime hab htab]
  · intro c d hcd hγ
    rw [Measure.restrict_map (rescalePathTime a b).continuous.measurable measurableSet_Icc,
      Measure.restrict_restrict ((rescalePathTime a b).continuous.measurable measurableSet_Icc),
      preimage_rescale_Icc hab,
      physicalTimeLength_restrict_compact e hU y₀ γ
        ((affinePathTime_strictMono hab).monotone hcd)
        (pathsInsideOn_affine_image hab γ.val hγ)]
    exact (physicalSubpath_affine_lengthCode e hU y₀ γ hab hcd hγ).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalPieceTimeMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The time measure of a restricted piece transported back to its original
parameter interval. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalTimeLength_piece (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (hmatch : ∀ s, η.val (affinePathTime a b s) = γ.val s) :
    (physicalTimeLength e y₀ η).restrict (Icc a b) =
      (physicalTimeLength e y₀ γ).map (affinePathTime a b) := by
  have heq : affineFinitePhysicalPath e hU y₀ η hab = γ := by
    apply Subtype.ext
    exact ContinuousMap.ext hmatch
  have hm : physicalTimeLength e y₀ γ =
      ((physicalTimeLength e y₀ η).restrict (Icc a b)).map (rescalePathTime a b) := by
    rw [← heq]
    exact physicalTimeLength_affine e hU y₀ η hab
  rw [hm, Measure.map_map (affinePathTime a b).continuous.measurable
    (rescalePathTime a b).continuous.measurable]
  have hid : (fun t => affinePathTime a b (rescalePathTime a b t)) =ᵐ[
      (physicalTimeLength e y₀ η).restrict (Icc a b)] id := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact affine_rescalePathTime hab ht
  simp only [Function.comp_def]
  rw [Measure.map_congr hid, Measure.map_id]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountablePhysicalCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical time and weighted occupation measures for collar
concatenations. Parameter multiplicity is preserved. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalTimeLength_collarPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η : FinitePhysicalPath e y₀) (γ : ℕ → FinitePhysicalPath e y₀)
    (hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s) :
    physicalTimeLength e y₀ η = Measure.sum (fun n =>
      (physicalTimeLength e y₀ (γ n)).map (affinePathTime (collarTime (n + 1)) (collarTime n))) := by
  rw [← sum_collar_restrict (physicalTimeLength e y₀ η)]
  congr 1
  funext n
  exact physicalTimeLength_piece e hU y₀ η (γ n)
    (collarTime_strictAnti (Nat.lt_succ_self n)) (hmatch n)

theorem physicalDomainLength_collarPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η : FinitePhysicalPath e y₀) (γ : ℕ → FinitePhysicalPath e y₀)
    (hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s) :
    physicalDomainLength e y₀ η.val = ∑' n, physicalDomainLength e y₀ (γ n).val := by
  rw [← physicalTimeLength_univ e y₀ η, physicalTimeLength_collarPieces e hU y₀ η γ hmatch,
    Measure.sum_apply _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Measure.map_apply (affinePathTime _ _).continuous.measurable MeasurableSet.univ,
    preimage_univ, physicalTimeLength_univ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_EmbeddedPathTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the tags of one path into an open piece of a larger path.
Every transported tag stays inside that piece and retains its level tuple. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def embeddedTag (a b : PathTime) : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr q => Sum.inr ⟨q.1, q.2.1, q.2.2.1,
      affinePathTime a b q.2.2.2.1, affinePathTime a b q.2.2.2.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ConcatenatedTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous path assembled from countably many open pieces receives
the transported tags of each piece. Disjointness prevents interference. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

def concatenatedTaggedPath (γ : C(PathTime, X)) (a b : ι → PathTime)
    (Γ : ι → TaggedPath X) : TaggedPath X :=
  (γ, assembleTags (fun i k => embeddedTag (a i) (b i) ((Γ i).2 k)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AllowedCollarConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed countable collar path is allowed when its actual
physical lengths are summable. No path-stability input is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace C(PathTime, X)]

def collarTaggedPath (p : X) (Γ : ℕ → TaggedPath X)
    (hjoin : ∀ n, (Γ (n + 1)).1 ⊤ = (Γ n).1 ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, (Γ n).1 s ∈ V) : TaggedPath X :=
  concatenatedTaggedPath (collarConcatenation p (fun n => (Γ n).1) hjoin htail)
    (fun n => collarTime (n + 1)) collarTime Γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitFragmentArray
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual triangular array of initial collar fragments. Entries before
the relevant collar is reached use the old path and are never selected. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def firstExitFragmentArray (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j)) (n j : ℕ) : TaggedPhysicalPath d :=
  if hj : j ≤ n then restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) else Γ n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LastEntryFragmentArray
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual final collar fragments, in the original time direction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def lastEntryFragmentArray (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1))) (n j : ℕ) : TaggedPhysicalPath d :=
  if hj : j ≤ n then restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) else Γ n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ActualOneEndedBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual retained prefixes and final fragments, with one common
subsequence and the correct one-ended limiting budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def prefixFragment (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0)) (n : ℕ) : TaggedPhysicalPath d :=
  restrictTaggedPhysicalPath d hU (Γ n) (hprefix n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ActualTwoEndedBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common limiting budget for actual first-exit, middle, and last-entry
restrictions of the original paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def middleFragment (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V W : ℕ → Set X)
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (n : ℕ) : TaggedPhysicalPath d := restrictTaggedPhysicalPath d hU (Γ n) (hmid n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeConstraints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting auxiliary dust and tuple exclusions maps an allowed endpoint
code into the base-code family without changing its path or tags. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem endpointCode_forget (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {Γ : TaggedPath X} (hΓ : EndpointCode d ν T Γ) :
    EndpointCode d 0 (fun _ _ => ∅) Γ :=
  ⟨allowedTaggedPath_forget d ν T hΓ.1, hΓ.2⟩

def forgetCode (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : {Γ : TaggedPath X // EndpointCode d ν T Γ}) : BasePathCode d :=
  ⟨Γ.val, endpointCode_forget d ν T Γ.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathCostMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three-part coding measure: physical occupation, countable
preterminal visits, and weighted tuples. Finiteness is a Borel code condition. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

variable [SecondCountableTopology X] [Countable D]

instance instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞) (Γ : FiniteCostCode d p c) :
    IsFiniteMeasure (pathCostMeasure d p c Γ.val) := ⟨Γ.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SparseBaseCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective retagging preserves the complete base-code conditions and cost finiteness.
It is a Borel operation on the actual code space. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem endpointCode_sparse (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (e : ℕ ↪ ℕ) {Γ : TaggedPath X} (hΓ : EndpointCode d ν T Γ) :
    EndpointCode d ν T (sparseTaggedPath e Γ) :=
  ⟨allowedTaggedPath_sparse d ν T e hΓ.1, hΓ.2⟩

def sparseBaseCode (d : PathCodeData X Y) (e : ℕ ↪ ℕ) (Γ : BasePathCode d) : BasePathCode d :=
  ⟨sparseTaggedPath e Γ.val, endpointCode_sparse d 0 (fun _ _ => ∅) e Γ.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RetaggedCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary tuple cost can be removed from an admissible metric's
lower bound. This is the retagging step in Section 4 of the manuscript. -/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)]

def nonTupleCost (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ y, h (costPhysical y) ∂baseCodeOccupation d Γ) +
    ∑' s, (c s * preterminalVisitCount Γ.val.1 (p s)) * h (costAtomic s)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_AdmissiblePathCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive perturbation of an admissible coding metric gives a genuine
physical-plus-preterminal cost lower bound on every allowed path. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSpace C(PathTime, X)]

def physicalAtomicCost (d : PathCodeData X Y) (p : D → X) (Γ : BasePathCode d)
    (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ y, g y ∂baseCodeOccupation d Γ) +
    ∑' s, m s * preterminalVisitCount Γ.val.1 (p s)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConstrainedCostCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite coding-measure family with a prescribed null
residual-image constraint, as a standard Borel space of codes. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def finiteCodeMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : FiniteCostCode d p c) : FiniteMeasure (PathCostSpace Y D) :=
  ⟨pathCostMeasure d p c Γ.val, inferInstance⟩

def constrainedCodeMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (Γ : ConstrainedCostCode d p c ν) : FiniteMeasure (PathCostSpace Y D) :=
  finiteCodeMeasure d p c Γ.val

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzIntervalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete paths obtained by traversing a real interval in a Lipschitz chart. -/

open Set Function Metric
open scoped NNReal ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem realIntervalPath_lipschitz (a b : ℝ) :
    LipschitzWith (nndist a b) (realIntervalPath a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (AffineMap.lineMap a b (s : ℝ)) (AffineMap.lineMap a b (t : ℝ)) ≤ _
  rw [dist_lineMap_lineMap, Subtype.dist_eq, coe_nndist, mul_comm]

theorem realIntervalPath_mem {a b : ℝ} (hab : a ≤ b) (s : PathTime) :
    realIntervalPath a b s ∈ Icc a b := by
  change AffineMap.lineMap a b (s : ℝ) ∈ Icc a b
  rw [AffineMap.lineMap_apply_module]
  simp only [smul_eq_mul]
  constructor <;> nlinarith [s.property.1, s.property.2]

theorem lipschitz_path_boundedVariation {X : Type*} [MetricSpace X]
    {γ : PathTime → X} {L : ℝ≥0} (hL : LipschitzWith L γ) :
    BoundedVariationOn γ univ := by
  have hid : BoundedVariationOn (id : PathTime → PathTime) univ := by
    change eVariationOn (id : PathTime → PathTime) univ ≠ ∞
    rw [← Icc_bot_top, variation_time_identity (bot_le : (⊥ : PathTime) ≤ ⊤)]
    exact edist_ne_top _ _
  exact hL.comp_boundedVariationOn hid

variable {X : Type*} [MetricSpace X]

theorem intervalChart_lipschitz (φ : ℝ → X) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) :
    LipschitzWith (L * nndist a b) (φ ∘ realIntervalPath a b) := by
    intro s t
    calc
      edist (φ (realIntervalPath a b s)) (φ (realIntervalPath a b t)) ≤
          L * edist (realIntervalPath a b s) (realIntervalPath a b t) :=
        hL (realIntervalPath_mem hab s) (realIntervalPath_mem hab t)
      _ ≤ (L * nndist a b : ℝ≥0) * edist s t := by
        calc
          _ ≤ (L : ℝ≥0∞) * ((nndist a b : ℝ≥0∞) * edist s t) :=
            mul_le_mul' le_rfl (realIntervalPath_lipschitz a b s t)
          _ = _ := by simp only [ENNReal.coe_mul, mul_assoc]

def intervalChartPath (φ : ℝ → X) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) : RectifiablePath X :=
  let hl := intervalChart_lipschitz φ hab hL
  ⟨⟨φ ∘ realIntervalPath a b, hl.continuous⟩, lipschitz_path_boundedVariation hl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_IntervalChartCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted cost of a chart interval, bounded by the ordinary line
integral of the pulled-back density. Parameter speed cancels exactly. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

def realRectifiableInterval (a b : ℝ) : RectifiablePath ℝ :=
  ⟨realIntervalPath a b, lipschitz_path_boundedVariation (realIntervalPath_lipschitz a b)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A binary continuous join with exact affine parametrizations of both
halves, for attaching collar tails to retained fragments. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem joinedPath_first (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) (s : PathTime) :
    joinedPath γ δ h (affinePathTime ⊥ (collarTime 1) s) = γ s := by
  change ((⟨γ, rfl, rfl⟩ : Path (γ ⊥) (γ ⊤)).trans
    (⟨δ, h.symm, rfl⟩ : Path (γ ⊤) (δ ⊤))) _ = _
  rw [Path.trans_apply]
  have hhalf : (affinePathTime ⊥ (collarTime 1) s : ℝ) ≤ 1/2 := by
    rw [affinePathTime_coe]
    simp only [collarTime, pow_one]
    change ((1:ℝ)/2 - 0) * (s : ℝ) + 0 ≤ 1/2
    nlinarith [s.property.2]
  rw [dite_eq_left hhalf]
  apply congrArg γ
  apply Subtype.ext
  simp only [affinePathTime_coe, collarTime, pow_one]
  change 2 * ((1/2 - 0) * (s : ℝ) + 0) = (s : ℝ)
  ring

theorem joinedPath_second (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) (s : PathTime) :
    joinedPath γ δ h (affinePathTime (collarTime 1) ⊤ s) = δ s := by
  change ((⟨γ, rfl, rfl⟩ : Path (γ ⊥) (γ ⊤)).trans
    (⟨δ, h.symm, rfl⟩ : Path (γ ⊤) (δ ⊤))) _ = _
  rw [Path.trans_apply]
  split_ifs with ht
  · have hs : (s : ℝ) = 0 := by
      have hs0 := s.property.1
      have hh : (1 - 1/2) * (s : ℝ) + 1/2 ≤ (1:ℝ)/2 := by
        rw [affinePathTime_coe] at ht
        simpa only [collarTime, pow_one, Set.Icc.coe_top] using ht
      linarith
    have hs' : s = ⊥ := Subtype.ext hs
    subst s
    change γ _ = δ ⊥
    rw [← h]
    apply congrArg γ
    apply Subtype.ext
    simp [affinePathTime_zero, collarTime]
  · apply congrArg δ
    apply Subtype.ext
    simp only [affinePathTime_coe, collarTime, pow_one]
    change 2 * ((1 - 1/2) * (s : ℝ) + 1/2) - 1 = (s : ℝ)
    ring

theorem joinedPath_collar_succ (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥)
    (n : ℕ) (s : PathTime) :
    joinedPath γ δ h (affinePathTime (collarTime (n+2)) (collarTime (n+1)) s) =
      γ (affinePathTime (collarTime (n+1)) (collarTime n) s) := by
  have he : affinePathTime (collarTime (n+2)) (collarTime (n+1)) s =
      affinePathTime ⊥ (collarTime 1)
        (affinePathTime (collarTime (n+1)) (collarTime n) s) := by
    apply Subtype.ext
    simp only [affinePathTime_coe, collarTime, pow_succ, pow_zero, one_mul]
    change ((1/2:ℝ)^n * (1/2) - (1/2)^n * (1/2) * (1/2)) * (s:ℝ) +
      (1/2)^n * (1/2) * (1/2) =
      ((1/2)-0) * (((1/2)^n - (1/2)^n*(1/2))*(s:ℝ) + (1/2)^n*(1/2)) + 0
    ring
  rw [he, joinedPath_first]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary joining preserves finite physical length and adds the exact
physical occupation costs. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

def collarRestrictions (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) : FinitePhysicalPath e y₀ :=
  affineFinitePhysicalPath e hU y₀ γ (collarTime_strictAnti (Nat.lt_succ_self n))

theorem collarRestrictions_length_sum (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    (∑'n, physicalDomainLength e y₀ (collarRestrictions e hU y₀ γ n).val) =
      physicalDomainLength e y₀ γ.val :=
  (physicalDomainLength_collarPieces e hU y₀ γ (collarRestrictions e hU y₀ γ)
    (fun _ _ => rfl)).symm

def joinedPhysicalPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) : ℕ → FinitePhysicalPath e y₀
  | 0 => δ
  | n+1 => collarRestrictions e hU y₀ γ n

theorem joinedPhysicalPieces_match (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) (h : γ.val ⊤ = δ.val ⊥) (n : ℕ) (s : PathTime) :
    joinedPath γ.val δ.val h (affinePathTime (collarTime (n+1)) (collarTime n) s) =
      (joinedPhysicalPieces e hU y₀ γ δ n).val s := by
  cases n with
  | zero =>
    change joinedPath γ.val δ.val h (affinePathTime (collarTime 1) (collarTime 0) s) = δ.val s
    rw [collarTime_zero]
    exact joinedPath_second γ.val δ.val h s
  | succ n => exact joinedPath_collar_succ γ.val δ.val h n s

theorem joinedPhysicalPieces_length_sum (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) :
    (∑'n, physicalDomainLength e y₀ (joinedPhysicalPieces e hU y₀ γ δ n).val) =
      physicalDomainLength e y₀ δ.val + physicalDomainLength e y₀ γ.val := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  exact congrArg (fun a => physicalDomainLength e y₀ δ.val + a)
    (collarRestrictions_length_sum e hU y₀ γ)

def joinedFinitePhysicalPath (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) (h : γ.val ⊤ = δ.val ⊥) : FinitePhysicalPath e y₀ :=
  ⟨joinedPath γ.val δ.val h, by
    apply (physicalDomainLength_collarPieces_le e hU y₀
      (joinedPhysicalPieces e hU y₀ γ δ) _ (joinedPhysicalPieces_match e hU y₀ γ δ h)).trans_lt
    rw [joinedPhysicalPieces_length_sum]
    exact ENNReal.add_lt_top.mpr ⟨δ.property, γ.property⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_JoinedPhysicalCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact interior cost addition for the allowed binary join. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def interiorPhysicalTollCost (d : PathCodeData X Y) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) : ℝ≥0∞ :=
  (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) +
    timeToll γ.val (Ioo (⊥ : PathTime) ⊤) m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_Conformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- Reflexivity of the concrete conformal-equivalence predicate. -/
theorem isConformalEquivalence_id (U : Set Sphere) :
    IsConformalEquivalence id U U := by
  refine ⟨fun p _ => isConformalAt_id p, fun _ h => h, id,
    fun p _ => isConformalAt_id p, fun _ h => h, ?_, ?_⟩
  · intro z _
    rfl
  · intro z _
    rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem frontier_sphere_image_jordanInterior (H : ℂ ≃ₜ ℂ) :
    frontier (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) := by
  have ho : IsOpen (((↑) : ℂ → Sphere) '' jordanInterior H) :=
    OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  rw [ho.frontier_eq, closure_sphere_image_jordanInterior,
    (jordanInterior_isOpen H).frontier_eq, Set.image_sdiff OnePoint.coe_injective]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MetricChartEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_self _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.chart_infty_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy of the actual metric-conformal chart differential

The Gram equations defining metric conformality identify the source
metric with a scalar multiple of the pulled-back Euclidean metric.
Consequently the covector energy changes by the positive Jacobian.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem metric_eq_scaled_chart_gram
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p) (hg : (sphereChartMetric g p).IsSymm) :
    ∃ c : ℝ, 0 < c ∧ sphereChartMetric g p = c •
      ((complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)))ᵀ *
        complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p))) := by
  obtain ⟨_, _, scale, hscale, hxx, hyy, hxy, _⟩ := hf
  refine ⟨scale⁻¹, inv_pos.mpr hscale, ?_⟩
  have hsym : sphereChartMetric g p 1 0 = sphereChartMetric g p 0 1 := by
    exact congrFun (congrFun hg 0) 1
  have hgram :
      (complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)))ᵀ *
        complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)) =
      scale • sphereChartMetric g p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexRealMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
      nlinarith [hxx, hyy, hxy, hsym]
  rw [hgram, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereRealDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite real chart of a metric-conformal sphere map

This identifies the actual real derivative matrix of the finite-chart
map with the complex chart derivative used in metric conformality.
-/

open Set Filter Matrix
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem sphereRealMap_hasFDerivAt
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {x : ℝ × ℝ}
    (hf : IsMetricConformalAt g f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    HasFDerivAt (sphereRealMap f)
      (complexToRealDerivative (fderiv ℝ
        (sphereLocalMap f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
        (Complex.equivRealProdCLM.symm x))) x := by
  let p : Sphere := ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)
  have hd : HasFDerivAt (sphereLocalMap f p)
      (fderiv ℝ (sphereLocalMap f p) (Complex.equivRealProdCLM.symm x))
      (Complex.equivRealProdCLM.symm x) := by
    simpa only [p, chart, OnePoint.coe_ne_infty, ite_false, if_false, finiteCoord,
      OnePoint.elim_some, id_eq] using hf.2.1.hasFDerivAt
  have hc := Complex.equivRealProdCLM.hasFDerivAt.comp x
    (hd.comp x Complex.equivRealProdCLM.symm.hasFDerivAt)
  have heq : sphereRealMap f =
      Complex.equivRealProdCLM ∘ sphereLocalMap f p ∘ Complex.equivRealProdCLM.symm := by
    funext y
    simp only [sphereRealMap, sphereLocalMap, p, chart, chartSymm,
      OnePoint.coe_ne_infty, ite_false, if_false, hfinite, Function.comp_apply]
  simpa only [heq, complexToRealDerivative] using hc

theorem metric_conformal_real_chart
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {x : ℝ × ℝ}
    (hf : IsMetricConformalAt g f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere))
    (hg : (g x).PosDef)
    (hfinite : f ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ≠ OnePoint.infty) :
    DifferentiableAt ℝ (sphereRealMap f) x ∧
      0 < (fderiv ℝ (sphereRealMap f) x).det ∧
      ∃ c : ℝ, 0 < c ∧ g x = c •
        ((planeDerivativeMatrix (fderiv ℝ (sphereRealMap f) x))ᵀ *
          planeDerivativeMatrix (fderiv ℝ (sphereRealMap f) x)) := by
  let p : Sphere := ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere)
  have hmetric : sphereChartMetric g p = g x := by
    simp only [p, sphereChartMetric, OnePoint.coe_ne_infty, ite_false, if_false, finiteCoord,
      OnePoint.elim_some, id_eq, ContinuousLinearEquiv.apply_symm_apply]
  have hcenter : chart p p = Complex.equivRealProdCLM.symm x := by
    simp only [p, chart, OnePoint.coe_ne_infty, ite_false, if_false, finiteCoord, OnePoint.elim_some, id_eq]
  have hd := sphereRealMap_hasFDerivAt hf hfinite
  have hmat : planeDerivativeMatrix (fderiv ℝ (sphereRealMap f) x) =
      complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)) := by
    rw [hd.fderiv, planeMatrix_complexToRealDerivative, hcenter]
  refine ⟨hd.differentiableAt, ?_, ?_⟩
  · rw [← det_planeDerivativeMatrix, hmat, det_complexRealMatrix]
    exact hf.2.2.choose_spec.2.2.2.2
  · have hsym : (sphereChartMetric g p).IsSymm := by
      rw [hmetric]
      exact Matrix.isHermitian_iff_isSymm.mp hg.isHermitian
    obtain ⟨c, hc, heq⟩ := metric_eq_scaled_chart_gram hf hsym
    change sphereChartMetric g p = _ at heq
    rw [hmetric] at heq
    refine ⟨c, hc, ?_⟩
    rw [hmat]
    exact heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ExteriorSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trapping the bounded side of a circle-model image

A compact exterior piece has closed image. Its open interior has open
image, and their difference is the image of the boundary circle. A
connected set avoiding that boundary and meeting the open image must
lie entirely in the image. This supplies the topological part of the
uniform bound for finite circle models.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem connected_set_subset_image_of_boundary_avoidance
    {f fi : Sphere → Sphere} {U V E S A : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi U V) (hV : IsOpen V)
    (hE : IsCompact E) (hEU : E ⊆ U) (hS : IsOpen S) (hSE : S ⊆ E)
    (hA : IsPreconnected A) (hmeet : (A ∩ f '' S).Nonempty)
    (havoid : Disjoint A (f '' (E \ S))) : A ⊆ f '' S := by
  have hES : f '' S ⊆ f '' E := image_mono hSE
  have hclosed : IsClosed (f '' E) := (hE.image_of_continuousOn
    (fun x hx => (hf.smooth x (hEU hx)).1.continuousWithinAt)).isClosed
  have hcover : A ⊆ f '' S ∪ (f '' E)ᶜ := by
    intro y hy
    by_cases he : y ∈ f '' E
    · obtain ⟨x, hx, rfl⟩ := he
      by_cases hs : x ∈ S
      · exact Or.inl ⟨x, hs, rfl⟩
      · exact (Set.disjoint_left.mp havoid hy ⟨x, ⟨hx, hs⟩, rfl⟩).elim
    · exact Or.inr he
  have hdisj : Disjoint (f '' S) (f '' E)ᶜ := by
    exact disjoint_compl_right.mono_left hES
  exact hA.subset_left_of_subset_union (hf.isOpen_image hV hS (hSE.trans hEU))
    hclosed.isOpen_compl hdisj hcover hmeet

/-- A geometric boundary inclusion traps every exterior target point in
an exterior source image. The coefficient bound will supply the inclusion. -/
theorem sphere_exterior_subset_image
    {f fi : Sphere → Sphere} {U V : Set Sphere} (hf : IsSmoothSphereEquivalence f fi U V)
    (hV : IsOpen V) {r L : ℝ} (_hr : 0 < r) (hL : 0 ≤ L)
    (hEU : ((((↑) : ℂ → Sphere) '' Metric.ball 0 r)ᶜ) ⊆ U)
    (hfix : f OnePoint.infty = OnePoint.infty)
    (hboundary : ∀ z : ℂ, ‖z‖ = r → f (z : Sphere) ∈
      ((↑) : ℂ → Sphere) '' Metric.closedBall 0 L) :
    ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 L)ᶜ) ⊆
      f '' ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 r)ᶜ) := by
  let E : Set Sphere := (((↑) : ℂ → Sphere) '' Metric.ball 0 r)ᶜ
  let S : Set Sphere := (((↑) : ℂ → Sphere) '' Metric.closedBall 0 r)ᶜ
  let A : Set Sphere := (((↑) : ℂ → Sphere) '' Metric.closedBall 0 L)ᶜ
  have hE : IsCompact E := (OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball).isClosed_compl.isCompact
  have hS : IsOpen S := ((isCompact_closedBall (0 : ℂ) r).image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hSE : S ⊆ E := compl_subset_compl.mpr (image_mono Metric.ball_subset_closedBall)
  have hinfS : OnePoint.infty ∈ S := by simp [S]
  have hmeet : (A ∩ f '' S).Nonempty := by
    refine ⟨OnePoint.infty, ?_, OnePoint.infty, hinfS, hfix⟩
    simp [A]
  apply connected_set_subset_image_of_boundary_avoidance hf hV hE hEU hS hSE
    (isConnected_sphere_exterior_closedBall (0 : ℂ) hL).isPreconnected hmeet
  apply Set.disjoint_left.mpr
  rintro y hy ⟨x, hx, rfl⟩
  cases x using OnePoint.rec with
  | infty => exact hx.2 hinfS
  | coe z =>
    have hnlo : r ≤ ‖z‖ := by
      have hz : z ∉ Metric.ball (0 : ℂ) r := by
        intro hz
        exact hx.1 ⟨z, hz, rfl⟩
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hnhi : ‖z‖ ≤ r := by
      have hz : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 r :=
        not_not.mp hx.2
      obtain ⟨w, hw, hwz⟩ := hz
      have heq : w = z := OnePoint.coe_injective hwz
      simpa only [heq, Metric.mem_closedBall, dist_zero_right] using hw
    exact hy (hboundary z (le_antisymm hnhi hnlo))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedUniformBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One uniform bound for normalized finite circle models

The exterior coefficient estimate controls a physical circle and the
annulus outside it. The compact-exterior separation argument traps all
other image points and every omitted point on its bounded side.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem normalized_model_uniform_bound
    (harea : ExteriorCoefficientAreaTheorem)
    {f fi : Sphere → Sphere} {U V : Set Sphere} (heq : IsSmoothSphereEquivalence f fi U V)
    (hV : IsOpen V) {R : ℝ} (hR : 0 < R)
    (hsource : ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ U)
    (hf : IsConformalOn f ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : IsPrincipalNormalized f) :
    (∀ p ∈ Vᶜ, p ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (3 * R)) ∧
      ∀ z : ℂ, (z : Sphere) ∈ U → ‖z‖ ≤ 4 * R →
        f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (5 * R) := by
  have hinf : OnePoint.infty ∈ U := hsource (by simp)
  have hfinite (z : ℂ) (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty :=
    heq.finite_forward hinf hnorm.1 hz
  let F : ℂ → ℂ := fun z => finiteCoord (f (z : Sphere))
  have hF : DifferentiableOn ℂ F {z | R < ‖z‖} := by
    intro z hz
    change R < ‖z‖ at hz
    have hzExt : (z : Sphere) ∈ ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ) := by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
        dist_zero_right, mem_compl_iff, not_le] using hz
    obtain ⟨_, d, _, hd⟩ := hf z hzExt
    have hzU : (z : Sphere) ∈ U := hsource (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hz.le)
    have he : (fun w => chart (f (z : Sphere)) (f (chartSymm (z : Sphere) w))) = F := by
      funext w
      simp only [chart, hfinite z hzU, ite_false, if_false, chartSymm_coe_apply, F]
    rw [he, chart_coe_self] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hFi : InjOn F {z | R < ‖z‖} := by
    intro z hz w hw he
    have hzU : (z : Sphere) ∈ U := hsource (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hz.le)
    have hwU : (w : Sphere) ∈ U := hsource (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hw.le)
    apply OnePoint.coe_injective
    apply heq.bijOn.injOn hzU hwU
    calc
      f (z : Sphere) = ((F z : ℂ) : Sphere) := (coe_finiteCoord (hfinite z hzU)).symm
      _ = ((F w : ℂ) : Sphere) := congrArg ((↑) : ℂ → Sphere) he
      _ = f (w : Sphere) := coe_finiteCoord (hfinite w hwU)
  have hb : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ R :=
    harea.scaled_exterior_bound hR hF hFi hnorm.2
  have hEU : ((((↑) : ℂ → Sphere) '' Metric.ball 0 (2 * R))ᶜ) ⊆ U := by
    apply Subset.trans _ hsource
    exact compl_subset_compl.mpr (image_mono (Metric.ball_subset_ball (by linarith)))
  have hboundary : ∀ z : ℂ, ‖z‖ = 2 * R →
      f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (3 * R) := by
    intro z hz
    have hzU : (z : Sphere) ∈ U := hEU (by
      simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
        dist_zero_right, mem_compl_iff, not_lt] using hz.ge)
    refine ⟨F z, ?_, coe_finiteCoord (hfinite z hzU)⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖F z‖ ≤ ‖F z - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ 3 * R := by linarith [hb z hz.ge]
  have hexterior := sphere_exterior_subset_image heq hV (by linarith : 0 < 2 * R)
    (by positivity : 0 ≤ 3 * R) hEU hnorm.1 hboundary
  constructor
  · intro p hp
    by_contra houtside
    obtain ⟨x, hx, rfl⟩ := hexterior houtside
    exact hp (heq.mapsTo (hEU (compl_subset_compl.mpr
      (image_mono Metric.ball_subset_closedBall) hx)))
  · intro z hzU hzn
    refine ⟨F z, ?_, coe_finiteCoord (hfinite z hzU)⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hz : 2 * R ≤ ‖z‖
    · calc
        ‖F z‖ ≤ ‖F z - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
        _ ≤ 5 * R := by linarith [hb z hz]
    · have hsmall : f (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 (3 * R) := by
        by_contra hout
        obtain ⟨x, hx, hfx⟩ := hexterior hout
        have hxU : x ∈ U := hEU (compl_subset_compl.mpr
          (image_mono Metric.ball_subset_closedBall) hx)
        have hxeq : x = (z : Sphere) := heq.bijOn.injOn hxU hzU hfx
        rw [hxeq] at hx
        have hn : 2 * R < ‖z‖ := by
          simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
            dist_zero_right, mem_compl_iff, not_le] using hx
        exact hz hn.le
      obtain ⟨w, hw, hwz⟩ := hsmall
      have he : w = F z := by
        apply OnePoint.coe_injective
        exact hwz.trans (coe_finiteCoord (hfinite z hzU)).symm
      rw [Metric.mem_closedBall, dist_zero_right, he] at hw
      linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DomainPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rectifiable physical path entirely in the original domain projects
to an allowed quotient path, with exactly its original physical length. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalDyadicPath_project (e : G ≃ₜ U) (y₀ : Y)
    (β : C(PathTime, Y)) (hβ : ∀ t, β t ∈ G) (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicPath e y₀ n i (projectDomainPath e β hβ) =
      β.comp (timeClip (dyadicLeft n i) (dyadicRight n i)) := by
  have hi : projectDomainPath e β hβ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i) :=
    fun t _ => projectDomainPath_mem e β hβ t
  rw [physicalDyadicPath_of_mem e y₀ n i _ hi]
  ext t
  change (e.symm ⟨(e ⟨β (timeClip _ _ t), hβ _⟩).val, _⟩).val = β (timeClip _ _ t)
  exact congrArg Subtype.val (e.symm_apply_apply _)

theorem physicalStageLength_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) (n : ℕ) :
    physicalStageLength e y₀ n (projectDomainPath e β.val hβ) = eVariationOn β.val univ := by
  have he (i : Fin (2 ^ n)) :
      physicalDyadicLength e y₀ n i (projectDomainPath e β.val hβ) =
        pathLengthMeasure β (Icc (dyadicLeft n i) (dyadicRight n i)) := by
    rw [physicalDyadicLength, physicalDyadicPath_project, variation_timeClip _ (dyadicLeft_le_right n i),
      pathLengthMeasure_Icc β (dyadicLeft_le_right n i)]
  have hsum := congrArg (fun μ : Measure PathTime => μ univ) (sum_dyadic_restrict (pathLengthMeasure β) n)
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.restrict_apply_univ,
    pathLengthMeasure_univ] at hsum
  simpa only [physicalStageLength, he] using hsum

theorem physicalDomainLength_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) :
    physicalDomainLength e y₀ (projectDomainPath e β.val hβ) = eVariationOn β.val univ := by
  simp only [physicalDomainLength, physicalStageLength_project, iSup_const]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DomainPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a path contained in the physical domain, the dyadic occupation
kernel is exactly ordinary arclength occupation, with multiplicity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

def finiteProjectedPhysicalPath (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) : FinitePhysicalPath e y₀ :=
  ⟨projectDomainPath e β.val hβ, by
    rw [physicalDomainLength_project]
    exact lt_top_iff_ne_top.mpr β.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityContraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-linear conductivity equation is solved in the actual complex
L2 space by contraction. The operator parameter is only the contraction
property of the Beurling operator; the fixed point and its support are
constructed here. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 def conductivityProduct (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) (k : ℝ≥0)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) (f : ComplexPlaneL2) : ComplexPlaneL2 :=
  ((Lp.memLp f).of_le_mul (c := (k : ℝ)) (hq.smul (Lp.aestronglyMeasurable f))
    (by filter_upwards [hb] with x hx
        change ‖q x • f x‖ ≤ (k : ℝ) * ‖f x‖
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))).toLp (fun x => q x • f x)

 def conductivityConj (f : ComplexPlaneL2) : ComplexPlaneL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLp f

 def conductivitySource (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume) : ComplexPlaneL2 :=
  (hq.ofReal : MemLp (fun x => (q x : ℂ)) 2 volume).toLp (fun x => (q x : ℂ))

 def conductivityIteration (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (f : ComplexPlaneL2) : ComplexPlaneL2 :=
  conductivitySource q hq +
    conductivityProduct q hq.aestronglyMeasurable k hb (conductivityConj (S f))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakHeightIdentification
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of weak error-gradient limits with the derivatives
of the actual continuous height limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def heightLimitWitness (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    (hw : DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) v univ) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 v (ball 0 R) where
  memLp := continuous_memLp_ball hv R
  weakGrad := heightLimitGradient G₀ G₁
  weakGrad_component_memLp := by
    intro i
    let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    fin_cases i
    · exact (Lp.memLp G₀).restrict _
    · exact ((Lp.memLp G₁).restrict _).add (memLp_const 1)
  isWeakGrad := fun i => weakPartial_restrict_from_univ (hw i) _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalScalarSolver
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar transport data for conductivity postcomposition, constructed
from smooth principal maps. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def PrincipalConductivityScalarSolver : Prop :=
  ∀ F : Set EuclideanPlane, IsCompact F → ∀ n : ℕ, 1 ≤ n →
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue F n x*D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue F n x*D.imagGradient x 0) ∧
      CompactScalarPullback φ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneQuotientRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Descend a physical planar function through the actual domain homeomorphism. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

def quotientPlaneRepresentative (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (x : X) : ℝ := by
  classical
  exact if hx : x ∈ d.quotientDomain then
    sphereFromPlaneFunction w (d.domainEquiv.symm ⟨x, hx⟩).val else 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem interior_closedTerminalCap (H : ℂ ≃ₜ ℂ) :
    interior (closedTerminalCap H) = ((↑) : ℂ → Sphere) '' jordanInterior H := by
  ext p
  cases p using OnePoint.rec with
  | infty =>
    have hnot : OnePoint.infty ∉ closedTerminalCap H := by
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    simp only [OnePoint.infty_notMem_image_coe, iff_false]
    exact fun h => hnot (interior_subset h)
  | coe z =>
    change z ∈ ((↑) : ℂ → Sphere) ⁻¹' interior (closedTerminalCap H) ↔ _
    rw [OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
      OnePoint.continuous_coe]
    simp only [closedTerminalCap, OnePoint.coe_injective.preimage_image,
      interior_closure_jordanInterior, OnePoint.coe_injective.mem_set_image]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceTargetEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A target component corresponding to a source component

For the same sequence of matched boundary labels, the nested source disks
intersect in the original complementary component and the nested target
disks intersect in a full target complementary component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem corresponding_target_end_of_source_of_continuous_open
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere), p ∈ (f '' G)ᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap (J (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (J n (b n)) := by
  have hcarriercover : (⋃ n, (C n).carrier) = G := by
    apply Subset.antisymm (iUnion_subset fun n => (C n).subset)
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    exact mem_iUnion.mpr ⟨n, interior_subset hn⟩
  obtain ⟨b, hb, hsourcenest, _⟩ := component_eq_nested_jordan_end
    (fun n => (C n).disk) (fun n => (C n).disjoint) (fun n => (C n).carrier)
    (fun _ => compl_compl _) hstrict hcarriercover hq
  have hfrontG (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxfront : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxfront
  have htargetnest (n : ℕ) : closedTerminalCap (J (n + 1) (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J n (b n)) :=
    (matched_jordan_disk_subset_iff hi ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1))) (hfrontG _ _) (hboundary _ _) (hside _ _)).mp
      (hsourcenest n)
  have hanti : Antitone (fun n => closedTerminalCap (J n (b n))) := by
    apply antitone_nat_of_succ_le
    intro n x hx
    obtain ⟨z, hz, he⟩ := htargetnest n hx
    exact ⟨z, subset_closure hz, he⟩
  have hclosed (n : ℕ) (i : Fin (C n).count) : IsClosed (closedTerminalCap (J n i)) :=
    (isCompact_closedTerminalCap (J n i)).isClosed
  have hconnected (n : ℕ) : IsConnected (closedTerminalCap (J n (b n))) :=
    ⟨(nontrivial_closedTerminalCap (J n (b n))).nonempty,
      isPreconnected_closedTerminalCap (J n (b n))⟩
  have hnonempty := (isConnected_nested_sphere_intersection (fun n => hclosed n (b n)) hconnected hanti).nonempty
  obtain ⟨p, hp⟩ := hnonempty
  have hAe (n : ℕ) : f '' (C n).carrier = closedJordanCore (J n) := by
    apply compl_injective
    simpa only [closedJordanCore, compl_compl] using hJe n
  have hcap (n : ℕ) (i : Fin (C n).count) :
      closedTerminalCap (J n i) ⊆ (interior (f '' (C n).carrier))ᶜ := by
    rw [hAe n, interior_closedJordanCore]
    intro x hx hxint
    exact hxint (mem_iUnion.mpr ⟨i, hx⟩)
  have hmiss : (⋂ n, closedTerminalCap (J n (b n))) ⊆ (f '' G)ᶜ := by
    rintro x hx ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hy)
    apply hcap n (b n) (mem_iInter.mp hx n)
    rw [interior_image_of_continuous_open hf ho hG hi (C n).subset]
    exact mem_image_of_mem _ hn
  have hEcover (n : ℕ) : (f '' G)ᶜ ⊆ ⋃ i, closedTerminalCap (J n i) := by
    intro x hx
    have hxa : x ∈ (f '' (C n).carrier)ᶜ := fun h => hx (image_mono (C n).subset h)
    obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp (hJe n ▸ hxa)
    exact mem_iUnion.mpr ⟨i, z, subset_closure hz, he⟩
  have hcomponent := connectedComponentIn_eq_nested_end (fun n i => closedTerminalCap (J n i)) b
    hclosed hconnected (fun n => disjoint_closedTerminalCaps (J n) (hJd n)) hEcover hanti hmiss hp
  exact ⟨b, p, hmiss hp, hb, hcomponent, htargetnest⟩

theorem corresponding_target_end_of_source
    {G : Set Sphere} (hG : IsOpen G) {f : Sphere → Sphere}
    (hf : IsConformalOn f G) (hi : InjOn f G)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere), p ∈ (f '' G)ᶜ ∧
      connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      ∀ n, closedTerminalCap (J (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (J n (b n)) :=
  corresponding_target_end_of_source_of_continuous_open hG
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi C J hstrict hcover hJd hJe hboundary hside hq


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteMarkedTrapping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked-disk trapping for the actual finite terminal assignment

The assignment is constructed from a finite model. Once a fixed source
core is retained, a terminal inside one of its holes has its target disk
inside the corresponding image contour. Uniform convergence on that
contour passes this containment to the limiting closed disk.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def SmoothJordanCore.inDomain {G Q : Set Sphere} (A : SmoothJordanCore G)
    (h : A.carrier ⊆ Q) : SmoothJordanCore Q where
  count := A.count
  disk := A.disk
  curve := A.curve
  disjoint := A.disjoint
  subset_domain := h
  smooth := A.smooth
  embedding := A.embedding
  boundary := A.boundary

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalBoundaryLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse images approach the assigned terminal boundary

A target sequence approaching an assigned complementary component has
preimages eventually in every neighborhood of the corresponding physical
terminal boundary. Compactness and the proved component assignment replace
any assumption of a boundary extension of the uniformizing map.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.source_cluster_mem_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {q y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q))
    (hxQ : ∀ᶠ n in atTop, x n ∈ openCompletedRegion T)
    (hfx : Tendsto (f ∘ x) atTop (𝓝 y)) :
    q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) := by
  have hyout : y ∈ Vᶜ := connectedComponentIn_subset _ _ hy
  have hqout : q ∉ openCompletedRegion T := by
    intro hq
    have hflim := ((hf.smooth q hq).1.tendsto).comp hx
    have heq : y = f q := tendsto_nhds_unique hfx hflim
    exact hyout (heq.symm ▸ hf.mapsTo hq)
  have hqunion : q ∈ ⋃ j, closedTerminalCap (T j) := not_not.mp hqout
  obtain ⟨j, hqj⟩ := mem_iUnion.mp hqunion
  have hyj := a.cluster j q hqj x hx hxQ y hfx
  have hji : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp (a.disjoint hne) hyj hy
  subst j
  have hQavoid : openCompletedRegion T ⊆ (closedTerminalCap (T i))ᶜ := by
    intro z hz hzi
    exact hz (mem_iUnion.mpr ⟨i, hzi⟩)
  have hqclosure : q ∈ closure (openCompletedRegion T) := mem_closure_of_tendsto hx hxQ
  have hqnot : q ∉ interior (closedTerminalCap (T i)) := by
    change q ∈ (interior (closedTerminalCap (T i)))ᶜ
    simpa only [closure_compl] using closure_mono hQavoid hqclosure
  obtain ⟨z, hz, rfl⟩ := hqj
  refine ⟨z, ?_, rfl⟩
  rw [(jordanInterior_isOpen (T i)).frontier_eq]
  refine ⟨hz, ?_⟩
  intro hzi
  apply hqnot
  rw [interior_closedTerminalCap]
  exact mem_image_of_mem _ hzi

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedTerminalBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cluster oscillation of transported terminal branches

The finite model's actual inverse transports a real branch near a physical
terminal. All its cluster values at the assigned complementary component
come from the physical boundary. Thus the physical square-sum oscillation
estimate survives uniformization without a boundary-extension hypothesis.
-/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.cluster_values_subset_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : Sphere → ℝ)
    (hw : ∀ q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)),
      ContinuousAt w q) :
    componentClusterValues V (a.point i) (w ∘ fi) ⊆
      w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i))) := by
  rintro t ⟨y, hy, yn, hyn, hynV, ht⟩
  obtain ⟨q, _, s, hs, hqs⟩ := isCompact_univ.tendsto_subseq
    (fun n => mem_univ (fi (yn n)))
  have hxQ : ∀ᶠ n in atTop, fi (yn (s n)) ∈ openCompletedRegion T := by
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact hf.mapsTo_inv hn
  have hfy : Tendsto (fun n => f (fi (yn (s n)))) atTop (𝓝 y) := by
    apply (hyn.comp hs.tendsto_atTop).congr'
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact (hf.right_inv _ hn).symm
  have hq := a.source_cluster_mem_boundary hf hy hqs hxQ hfy
  refine ⟨q, hq, ?_⟩
  exact tendsto_nhds_unique ((hw q hq).tendsto.comp hqs) (ht.comp hs.tendsto_atTop)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TransportedRealEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-chart energy of the actual transported real function

Both integrability and the energy identity follow from the Jacobian
formula. Restriction to the bounded disk used by line payment only
decreases this energy.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_sphereRealFunction_eq
    (w : (ℝ × ℝ) → ℝ) (fi : Sphere → Sphere) :
    (sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere) =
      (w ∘ sphereRealMap fi) ∘ Complex.equivRealProdCLM := by
  funext z
  simp only [sphereRealFunction, sphereRealMap, comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPlaneEnergyTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal energy identity in the Euclidean-plane
coordinates used by the Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

def planeInverseTransport (fi : Sphere → Sphere) (u : EuclideanPlane → ℝ) :
    EuclideanPlane → ℝ :=
  u ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap fi ∘ euclideanPlaneCoordinates

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalHeightDifference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattened height minus the genuine vertical coordinate has an
explicit local weak gradient and a controlled compact cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def subtractSobolevWitness {U : Set EuclideanPlane} {u v : EuclideanPlane → ℝ}
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U) :
    DeGiorgi.MemW1pWitness 2 (fun x => u x-v x) U :=
  (Wu.add (Wv.smul (-1))).congr_ae (Eventually.of_forall (fun x => by ring))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mean occupation, atomic and tuple measures of a law on base
codes. Their sum is exactly the barycenter of the coding measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def meanCodeAtomic (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) : Measure D :=
  (P : Measure (BasePathCode d)).bind (fun Γ => atomicVisitMeasure p c Γ.val.1)

def meanCodeCost (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) : Measure (PathCostSpace Y D) :=
  (P : Measure (BasePathCode d)).bind (pathCostMeasure d p c)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SlotLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each fixed slot distribution is dominated by the mean weighted tuple
measure, and hence inherits its absolute continuity. Inactive slots have
zero mass, so these are subprobability measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def baseCodeSlot (d : PathCodeData X Y) (k : ℕ) (Γ : BasePathCode d) : Measure LevelTuple :=
  slotTupleMeasure (Γ.val.2 k)

def slotLaw (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (k : ℕ) :
    Measure LevelTuple := (P : Measure (BasePathCode d)).bind (baseCodeSlot d k)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeHitMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for complete path images. At free points, tuple absolute
continuity reduces a path hit to a residual hit; residual nullity then
annihilates the integrated whole-image hit probability. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def codeResidualGraph (d : PathCodeData X Y) : Set (BasePathCode d × X) :=
  {q | q.2 ∈ residualImage d.dust q.1.val}

def codeResidualProbability (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (x : X) : ℝ≥0∞ :=
  (P : Measure (BasePathCode d)) {Γ | x ∈ residualImage d.dust Γ.val}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeanVisitDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density on a countable cost atom records the actual mean number
of preterminal visits. The squared density budget therefore bounds the
counting square norm independently of the auxiliary positive weights. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def meanCodePreVisits (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (x : X) : ℝ≥0∞ :=
  ∫⁻ Γ : BasePathCode d, preterminalVisitCount Γ.val.1 x ∂(P : Measure (BasePathCode d))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodePathLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting the optional tags produces the actual path law. Its full
mean visit function differs from the preterminal function by exactly one
unit at the prescribed terminal point. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

variable [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X]

omit [BorelSpace X] [SecondCountableTopology X] in
theorem pathHitProbability_codePathLaw (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    pathHitProbability (codePathLaw d P) x = codeHitProbability d P x := by
  exact Measure.map_apply (measurable_codePath d) (isClosed_paths_hitting x).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ReversedPhysicalLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing time preserves the actual physical-domain length. Dyadic
cells are matched with their reversed indices before summing. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalDyadicPath_reversed (e : G ≃ₜ U) (y₀ : Y)
    (γ : C(PathTime, X)) (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicPath e y₀ n i (reversedPath γ) =
      reversedPath (physicalDyadicPath e y₀ n i.rev γ) := by
  by_cases hnew : reversedPath γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hold : γ ∈ pathsInsideOn U (dyadicLeft n i.rev) (dyadicRight n i.rev) := by
      simpa only [symm_dyadicRight, symm_dyadicLeft] using
        (pathsInsideOn_reversed_iff γ _ _).mp hnew
    rw [physicalDyadicPath_of_mem e y₀ n i _ hnew,
      physicalDyadicPath_of_mem e y₀ n i.rev _ hold]
    apply ContinuousMap.ext
    intro t
    change (e.symm ⟨γ (unitInterval.symm (timeClip (dyadicLeft n i) (dyadicRight n i) t)), _⟩).val =
      (e.symm ⟨γ (timeClip (dyadicLeft n i.rev) (dyadicRight n i.rev) (unitInterval.symm t)), _⟩).val
    apply congrArg Subtype.val
    apply congrArg e.symm
    apply Subtype.ext
    apply congrArg γ
    rw [symm_timeClip (dyadicLeft_le_right n i), symm_dyadicRight, symm_dyadicLeft]
  · have hold : γ ∉ pathsInsideOn U (dyadicLeft n i.rev) (dyadicRight n i.rev) := by
      intro h
      apply hnew
      apply (pathsInsideOn_reversed_iff γ _ _).mpr
      simpa only [symm_dyadicRight, symm_dyadicLeft] using h
    simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hnew, dite_eq_right hold]
    rfl

theorem physicalDomainLength_reversed (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    physicalDomainLength e y₀ (reversedPath γ) = physicalDomainLength e y₀ γ := by
  unfold physicalDomainLength
  congr 1
  funext n
  unfold physicalStageLength physicalDyadicLength
  simp_rw [physicalDyadicPath_reversed, variation_reversedPath]
  exact Equiv.sum_comp (Fin.revPerm (n := 2 ^ n))
    (fun i => eVariationOn (physicalDyadicPath e y₀ n i γ) univ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteSphericalArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicitly defined stereographic spherical area has finite mass.
Only integrability, not the exact value of the total area, is needed here. -/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

instance finiteSphericalArea : IsFiniteMeasure sphericalArea := by
  let : IsFiniteMeasure (volume.withDensity (fun z => ENNReal.ofReal (sphericalAreaDensity z))) :=
    isFiniteMeasure_withDensity integrable_sphericalAreaDensity.lintegral_lt_top.ne
  unfold sphericalArea
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_SmoothMetricUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth finite metric circle models and their inverses

The smooth version of the same compact uniformization input records
that the uniformizing map is a diffeomorphism for the original smooth
structure. This is the smooth-isothermal-coordinate conclusion of
Jost, *Compact Riemann Surfaces*, third edition (2006), Theorem 3.11.1,
pp. 155--158, followed by Ahlfors, *Conformal Invariants* (1973),
Theorem 10-3, p. 142. Only a smooth metric on the sphere, standard near
infinity, is required. The weaker metric-only input follows immediately.
-/

open Set Filter Function
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def SmoothCompactMetricSphereUniformization : Prop :=
  ∀ (g : (ℝ × ℝ) → PlanarMetric), ContDiff ℝ ∞ g → (∀ z, (g z).PosDef) →
    (∃ R : ℝ, 0 < R ∧ ∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) →
    ∃ e : Sphere ≃ₜ Sphere, (∀ p, IsMetricConformalAt g e p) ∧
      (∀ p, IsSmoothSphereAt e p) ∧ (∀ p, IsSmoothSphereAt e.symm p)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealCoordinateFamily
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual bounded physical coordinates and their square-summable
band budgets into the coordinate family consumed by finite transfer. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem boundary_width_nonneg {U : Set Sphere} {f : Sphere → ℝ}
    (hf : ∀ x ∈ U, |f x| ≤ 1) {x : Sphere} (hx : x ∈ closure U) :
    0 ≤ limsup f (𝓝[U] x) - liminf f (𝓝[U] x) := by
  obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hf hx
  have hm := subset_intervalFiberHull (clusterGraph U f) ht
  have he := intervalFiberHull_clusterGraph_eq_boundary_band hf hx
  have hi : t ∈ Icc (liminf f (𝓝[U] x)) (limsup f (𝓝[U] x)) := by
    rw [← he]
    exact hm
  exact sub_nonneg.mpr (hi.1.trans hi.2)

def realCoordinateDataFamily
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (M : Set Sphere) (hMB : M ⊆ d.dust)
    (w : ℕ → Sphere → ℝ≥0∞) (hw : ∀ i, (∑' x, w i x ^ 2) < ∞)
    (hsupport : ∀ i x, x ∈ d.dust → w i x ≠ 0 → x ∈ M)
    (hbudget : ∀ i x, x ∈ d.dust →
      ENNReal.ofReal (limsup (Q i).quotient (𝓝[d.quotientDomain] x) -
        liminf (Q i).quotient (𝓝[d.quotientDomain] x)) ≤ w i x)
 :
    FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val) := by
  let lo (i : ℕ) (x : Sphere) := liminf (Q i).quotient (𝓝[d.quotientDomain] x)
  let hi (i : ℕ) (x : Sphere) := limsup (Q i).quotient (𝓝[d.quotientDomain] x)
  have hunit (i : ℕ) (x : Sphere) (_ : x ∈ d.quotientDomain) : |(Q i).quotient x| ≤ 1 := by
    rw [abs_of_nonneg ((Q i).quotient_unit x).1]
    exact ((Q i).quotient_unit x).2
  have hclosure (x : Sphere) : x ∈ closure d.quotientDomain := by
    rw [hdense.closure_eq]
    trivial
  have hnn (i : ℕ) (x : Sphere) : 0 ≤ hi i x - lo i x :=
    boundary_width_nonneg (hunit i) (hclosure x)
  have hband (i : ℕ) (x : Sphere) :
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (Q i).quotient)} =
        Icc (lo i x) (hi i x) :=
    intervalFiberHull_clusterGraph_eq_boundary_band (hunit i) (hclosure x)
  have hsum (i : ℕ) : Summable (fun x : M => (hi i x.val - lo i x.val) ^ 2) := by
    have hfinite : (∑' x : M, ENNReal.ofReal ((hi i x.val - lo i x.val) ^ 2)) < ∞ := by
      calc
        _ = ∑' x : M, (ENNReal.ofReal (hi i x.val - lo i x.val)) ^ 2 := by
          congr 1
          funext x
          exact ENNReal.ofReal_pow (hnn i x.val) 2
        _ ≤ ∑' x : M, w i x.val ^ 2 :=
          ENNReal.tsum_le_tsum (fun x => pow_le_pow_left' (hbudget i x.val (hMB x.property)) 2)
        _ ≤ ∑' x, w i x ^ 2 :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun x => w i x ^ 2)
        _ < ∞ := hw i
    exact (ENNReal.summable_toReal hfinite.ne).congr
      (fun x => ENNReal.toReal_ofReal (sq_nonneg _))
  refine {
    source := d.quotientDomain
    source_open := hU
    coordinate := fun i => (Q i).quotient
    coordinate_continuous := fun i => (Q i).quotient_continuous
    bound := fun _ => 1
    coordinate_bounded := hunit
    physical := fun i => (Q i).physical
    physical_measurable := fun i => (Q i).physical_measurable
    physical_smooth := fun i => (Q i).physical_smooth
    physical_energy := fun i => (Q i).physical_energy
    source_map := ?_
    pullback := fun i => (Q i).pullback
    labels_injective := Subtype.val_injective
    labels_dust := fun x => hB ▸ hMB x.property
    labels_closure := fun x => hclosure x.val
    lower := fun i x => lo i x.val
    upper := fun i x => hi i x.val
    width_nonneg := fun i x => hnn i x.val
    width_summable := hsum
    band := fun i x => hband i x.val
    free_trace := ?_ }
  · intro z hz
    rw [← he ⟨(z : Sphere), hz⟩]
    exact (d.domainEquiv ⟨(z : Sphere), hz⟩).property
  · intro x hx hfree i
    have hxB : x ∈ d.dust := hB.symm ▸ hx
    have hxM : x ∉ M := by
      intro h
      exact hfree ⟨⟨x, h⟩, rfl⟩
    have hw0 : w i x = 0 := by
      by_contra h
      exact hxM (hsupport i x hxB h)
    have hzero : hi i x - lo i x = 0 := le_antisymm
      ((ENNReal.ofReal_eq_zero.mp (le_antisymm (by simpa only [hw0] using hbudget i x hxB)
        bot_le))) (hnn i x)
    refine ⟨lo i x, ?_⟩
    rw [hband, sub_eq_zero.mp hzero, Icc_self]

def realCoordinateFamily
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (M : Set Sphere) (hMB : M ⊆ d.dust)
    (w : ℕ → Sphere → ℝ≥0∞) (hw : ∀ i, (∑' x, w i x ^ 2) < ∞)
    (hsupport : ∀ i x, x ∈ d.dust → w i x ≠ 0 → x ∈ M)
    (hbudget : ∀ i x, x ∈ d.dust →
      ENNReal.ofReal (limsup (Q i).quotient (𝓝[d.quotientDomain] x) -
        liminf (Q i).quotient (𝓝[d.quotientDomain] x)) ≤ w i x)
    (_hcompat : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ M) (circleBandGraph d.quotientDomain (Q j).quotient)
          (fun i => circleBandGraph d.quotientDomain (Q i).quotient) labels) = 0) :
    FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val) :=
  realCoordinateDataFamily d hU hdense π he hB Q M hMB w hw hsupport hbudget

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TerminalPathMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reparametrization of the path after its last collar hit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def terminalPath (γ : C(PathTime, X)) (a : PathTime) : C(PathTime, X) :=
  γ.comp (affinePathTime a ⊤)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereJordanCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex disk and measurable circle coordinates for a spherical
Jordan collar. -/

open Set Function Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem range_sphereJordanBoundary (K : ℂ ≃ₜ ℂ) :
    range (sphereJordanBoundary K) = frontier (((↑) : ℂ → Sphere) '' jordanInterior K) := by
  rw [frontier_sphere_image_jordanInterior, frontier_jordanInterior]
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨_, ⟨standardCirclePoint θ,
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero θ).property, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective ⟨z, hz⟩
    exact ⟨θ, congrArg (fun z : Circle => ((K (z : ℂ) : ℂ) : Sphere)) hθ⟩

local instance localInst_rab1c54_1 : BorelSpace Sphere := ⟨rfl⟩
theorem measurableEmbedding_sphereJordanBoundary (K : ℂ ≃ₜ ℂ) :
    MeasurableEmbedding (sphereJordanBoundary K) := by
  have hi : Topology.IsEmbedding (sphereJordanBoundary K) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp (K.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).isEmbedding))
  exact hi.measurableEmbedding (by rw [range_sphereJordanBoundary]; exact isClosed_frontier.measurableSet)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_IntervalPath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

noncomputable section
namespace CircleDomainRigidity

def intervalPath {X : Type*} [MetricSpace X] (γ : C(PathTime, X)) (a b : PathTime) :
    Path (γ a) (γ b) where
  toContinuousMap := affineRestrictedPath a b γ
  source' := by
    have h0 : (0 : PathTime) = ⊥ := Subtype.ext rfl
    change γ (affinePathTime a b 0) = γ a
    rw [h0, affinePathTime_zero]
  target' := by
    have h1 : (1 : PathTime) = ⊤ := Subtype.ext rfl
    change γ (affinePathTime a b 1) = γ b
    rw [h1, affinePathTime_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleComponentCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Center and radius coordinates of circle-domain components

If a circle domain contains infinity, every complementary component
is an ordinary closed disk, allowing radius zero. A bound on the whole
complement bounds both parameters. Thus no choice of disk coordinates
is an extra hypothesis in the marked-disk compactness argument.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem circleDomain_component_eq_closedBall
    {V : Set Sphere} (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {p : Sphere} (hp : p ∈ Vᶜ) :
    ∃ (c : ℂ) (r : ℝ), 0 ≤ r ∧
      connectedComponentIn Vᶜ p = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  have hnot : OnePoint.infty ∉ connectedComponentIn Vᶜ p := by
    intro h
    exact connectedComponentIn_subset Vᶜ p h hinf
  rcases hV.2.2 p hp with ⟨q, hq⟩ | hq
  · have hqfinite : q ≠ OnePoint.infty := by
      intro h
      apply hnot
      rw [hq, ← h]
      exact mem_singleton q
    refine ⟨finiteCoord q, 0, le_rfl, ?_⟩
    rw [Metric.closedBall_zero, image_singleton, coe_finiteCoord hqfinite]
    exact hq
  · obtain ⟨c, r, hr, he⟩ := isRoundClosedDisk_eq_euclidean hq hnot
    exact ⟨c, r, hr.le, he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteTerminalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Round disk coordinates for the actual terminal assignment

The finite model's complementary disks are constructed from its circle
domain property. Their labels are exactly the physical terminal labels,
and their union is the full complement in the finite chart.
-/

open Set Function Metric

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.exists_disk_coordinates
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V) (hV : IsCircleDomain V)
    (hinf : OnePoint.infty ∈ V) :
    ∃ (c : I → ℂ) (r : I → ℝ), (∀ i, 0 ≤ r i) ∧
      (∀ i, connectedComponentIn Vᶜ (a.point i) =
        ((↑) : ℂ → Sphere) '' closedBall (c i) (r i)) ∧
      Pairwise (Disjoint on fun i => closedBall (c i) (r i)) ∧
      ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ := by
  choose c r hr he using fun i => circleDomain_component_eq_closedBall hV hinf (a.outside i)
  refine ⟨c, r, hr, he, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro z hzi hzj
    have hi : (z : Sphere) ∈ connectedComponentIn Vᶜ (a.point i) := by
      rw [he i]
      exact mem_image_of_mem _ hzi
    have hj : (z : Sphere) ∈ connectedComponentIn Vᶜ (a.point j) := by
      rw [he j]
      exact mem_image_of_mem _ hzj
    exact disjoint_left.mp (a.disjoint hij) hi hj
  · ext z
    change (z : Sphere) ∈ V ↔ z ∉ ⋃ i, closedBall (c i) (r i)
    constructor
    · intro hz hball
      obtain ⟨i, hi⟩ := mem_iUnion.mp hball
      have hc : (z : Sphere) ∈ connectedComponentIn Vᶜ (a.point i) := by
        rw [he i]
        exact mem_image_of_mem _ hi
      exact (connectedComponentIn_subset Vᶜ _ hc) hz
    · intro hz
      by_contra hnot
      obtain ⟨i, hi⟩ := a.covers (z : Sphere) hnot
      have hc := mem_connectedComponentIn (show (z : Sphere) ∈ Vᶜ from hnot)
      rw [hi, he i] at hc
      have hball : z ∈ closedBall (c i) (r i) := OnePoint.coe_injective.mem_set_image.mp hc
      exact hz (mem_iUnion.mpr ⟨i, hball⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted collars in the physical plane and their actual open quotient
neighborhoods. Compact containment survives projection. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

structure WeightedCollar (G : Set Sphere) (π : Sphere → Sphere) (B : Set Sphere)
    (p : Sphere) (g : ℂ → ℝ≥0∞) where
  disk : ℂ ≃ₜ ℂ
  curve : Circle → ℂ
  function : ℂ → ℝ
  level : ℝ
  fiber_inside : {z : ℂ | π (z : Sphere) = p} ⊆ jordanInterior disk
  curve_smooth : ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) curve
  curve_embedding : Topology.IsEmbedding curve
  frontier_eq : frontier (jordanInterior disk) = range curve
  frontier_level : frontier (jordanInterior disk) ⊆ {z | function z = level}
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) function
  regular : IsPlanarRegularValue function level
  level_good : ∀z, function z = level → (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B
  cost_finite : (∫⁻z in {z | function z = level}, g z ∂(μH[1] : Measure ℂ)) < ∞

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

def region : Set Sphere := π '' (((↑) : ℂ → Sphere) '' jordanInterior D.disk)

end WeightedCollar

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalTagPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local payment measure is formed from actual physical time length
and the flagged visit toll. Its total mass is bounded by the selected
path law’s cost. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

def physicalTagPayment (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) : Measure PathTime :=
  tagPaymentMeasure (physicalTimeLength e y₀ γ)
    (fun t => g (physicalValue e y₀ (γ.val t))) γ.val m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ParametricNullTuples
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel scalar-level envelopes remain Borel after forming finite tuples
and active slots, also when they depend on an earlier sampled path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω : Type*} [MeasurableSpace Ω]

def badSlotGraph (N : Ω → ℕ → Set UnitAddCircle) : Set (Ω × TagSlot) :=
  {p | ∃ q, p.2 = Sum.inr q ∧ tagDataTuple q ∈ tuplesWithBadLevel (N p.1)}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SlotPairNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent active tag tuples avoid every product-null tuple event.
Inactive slots carry no tuple mass. -/

open Set Filter Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def activeSlotPairs (E : Set (LevelTuple × LevelTuple)) : Set (TagSlot × TagSlot) :=
  {p | ∃ q r, p.1 = Sum.inr q ∧ p.2 = Sum.inr r ∧ (tagDataTuple q, tagDataTuple r) ∈ E}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_IndependentTagLevel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute continuity of tag tuples supplies the independent-level
singleton conclusion for almost every path and almost every level. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

def activeSlotParameterEvent {T : Type*} (E : Set (LevelTuple × T)) :
    Set (TagSlot × T) :=
  {p | ∃ q, p.1 = Sum.inr q ∧ (tagDataTuple q, p.2) ∈ E}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FullDomainPhysicalLift
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An arbitrary finite physical path wholly in the quotient domain has
an actual rectifiable physical lift with exactly the original occupation. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def fullDomainPhysicalLift (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) : RectifiablePath Y :=
  ⟨physicalSubpath d.domainEquiv (show (⊥ : PathTime) ≤ ⊤ from bot_le) ⟨γ.val, fun t _ => hγ t⟩,
    physicalSubpath_rectifiable d.domainEquiv hU (show (⊥ : PathTime) ≤ ⊤ from bot_le) γ.val (fun t _ => hγ t)
      d.basePoint γ.property⟩

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_mem (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) (t : PathTime) :
    (fullDomainPhysicalLift d hU γ hγ).val t ∈ d.physicalDomain :=
  physicalSubpath_mem d.domainEquiv (show (⊥ : PathTime) ≤ ⊤ from bot_le) _ t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodePairOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proximity integral of independent physical path occupations is
controlled by their local square energies. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

def codePairProximity (d e : PathCodeData X Y) (A : Set Y) (a : ℝ≥0)
    (p : BasePathCode d × BasePathCode e) : ℝ≥0∞ :=
  ∫⁻ z, ballPairKernel A a z ∂(baseCodeOccupation d p.1).prod (baseCodeOccupation e p.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved outputs retained at one stage of the endpoint-law recursion.
The candidate includes actual densities and quantitative mark budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RecursiveLawWitness
variable {d : PathCodeData Sphere Sphere} {marks : Set Sphere}
  {ω : TupleType → ℝ≥0∞} (W : RecursiveLawWitness d marks ω)
local instance localInst_rab1c54_2 : BorelSpace Sphere := ⟨rfl⟩
abbrev candidate := W.2.property.1
def hitConstant : ℝ := Classical.choose W.2.property.2
theorem finite_hit_tests : ∀ F : Finset d.dust,
    ∑ x ∈ F, pathHitReal (codePathLaw d W.law) x.val ^ 2 ≤ W.hitConstant ^ 2 :=
  (Classical.choose_spec W.2.property.2).1
theorem countable_dust_hits : {x | x ∈ d.dust ∧ 0 < codeHitProbability d W.law x}.Countable :=
  (Classical.choose_spec W.2.property.2).2
end RecursiveLawWitness

namespace RecursiveCodeLaw

variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  (L : RecursiveCodeLaw base π flags ω)

abbrev physical_eq := L.geometry.physical_eq
abbrev quotient_eq := L.geometry.quotient_eq
abbrev dust_eq := L.geometry.dust_eq
abbrev levels_eq := L.geometry.levels_eq
abbrev weights_eq := L.geometry.weights_eq
abbrev domain_agrees := L.geometry.domain_agrees
abbrev target_dust := L.geometry.target_dust
abbrev presentation := L.geometry.presentation
abbrev prior_deletions_eq := L.geometry.prior_deletions_eq
abbrev flag_deletions_eq := L.geometry.flag_deletions_eq
local instance localInst_rab1c54_3 : BorelSpace Sphere := ⟨rfl⟩
abbrev candidate := L.witness.candidate
abbrev hitConstant := L.witness.hitConstant
abbrev finite_hit_tests := L.witness.finite_hit_tests
abbrev countable_dust_hits := L.witness.countable_dust_hits
abbrev occupationMass := L.witness.budgets.occupationMass
abbrev tupleMass := L.witness.budgets.tupleMass
abbrev energy := L.witness.budgets.energy
abbrev visitConstant := L.witness.budgets.visitConstant
abbrev occupationMass_finite := L.witness.budgets.occupationMass_finite
abbrev energy_finite := L.witness.budgets.energy_finite
abbrev visitConstant_finite := L.witness.budgets.visitConstant_finite

def density : Sphere → ℝ≥0∞ := Classical.choose L.candidate.1.2

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ReversedPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time reversal preserves the actual dyadic physical occupation measure
and its weighted cost, including the endpoint conventions used in splicing. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

def reversedFinitePhysicalPath {G : Set Y} {U : Set X} (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) : FinitePhysicalPath e y₀ :=
  ⟨reversedPath γ.val, by rw [physicalDomainLength_reversed]; exact γ.property⟩

variable [MeasurableSpace C(PathTime, X)]

def reversedTaggedPhysicalPath (d : PathCodeData X Y) (Γ : TaggedPhysicalPath d) :
    TaggedPhysicalPath d :=
  (reversedFinitePhysicalPath d.domainEquiv d.basePoint Γ.1, fun k => reversedTag (Γ.2 k))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_InitialBlockPiece
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace the first true piece of a grouped chain. This operation is
used when consecutive true edges are joined during chain normalization. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

def replaceInitialTruePiece (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) : JumpBlockCode d P where
  paths := Fin.cons (Fin.cons γ (fun j => Z.paths 0 j.succ)) (fun b => Z.paths b.succ)
  disks := Z.disks

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrependNewBlockJump
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepend one new jump and its initial true piece to a grouped chain.
The original first true piece follows the new jump unchanged. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

def prependNewBlockJump (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (V : Set X) :
    JumpBlockCode d (prependNewJumpPattern P) where
  paths := Fin.cons (Fin.cons γ (Z.paths 0)) (fun b => Z.paths b.succ)
  disks := Fin.cons (Fin.cons V (Z.disks 0)) (fun b => Z.disks b.succ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrependOldBlockJump
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepend an old jump, creating a new first block with one true piece.
The old disk label and its toll are retained exactly. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

def prependOldBlockJump (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (i : I) :
    JumpBlockCode d (prependOldJumpPattern P i) where
  paths := Fin.cons (fun _ => γ) Z.paths
  disks := Fin.cons Fin.elim0 Z.disks

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ConstrainedCodeLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting the constrained finite-code subtype produces an actual law
on base paths, retaining the residual nullity and finite-cost properties. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def constrainedCodeToBase (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (Γ : ConstrainedCostCode d p c ν) : BasePathCode d := Γ.val.val

omit [BorelSpace X] [BorelSpace D] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] in
theorem measurable_constrainedCodeToBase (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) :
    Measurable (constrainedCodeToBase d p c ν) :=
  measurable_subtype_coe.comp measurable_subtype_coe

def constrainedCodeLaw (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) :
    ProbabilityMeasure (BasePathCode d) := P.map (f := (constrainedCodeToBase d p c ν)) (by first | (apply Measurable.aemeasurable; apply measurable_constrainedCodeToBase <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FusionSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sigma-ideal of path-law candidates failing a prescribed countable/atomless
test. A finite atomless measure dominating any countable list of such tests is
constructed from the existing finite-measure representative of an s-finite measure. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def PassesHitTests (C : ℝ) (μ : ProbabilityMeasure C(PathTime, X))
    (D : Set X) (ν : Measure X) : Prop :=
  (∀ F : Finset X, (↑F : Set X) ⊆ D → ∑ x ∈ F, pathHitReal μ x ^ 2 ≤ C ^ 2) ∧
    ∫⁻ x, pathHitProbability μ x ∂ν = 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveLawConstruction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Insert the actual prior-law presentation into the path-code data, and
retain all quantitative outputs of the positive-law theorem in a recursion stage. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def endpointCodeData (base : PathCodeData Sphere Sphere) (p : Sphere)
    {flags : Set Sphere} {μ : ℕ → Measure C(PathTime, Sphere)}
    (R : PriorLawPresentation base.dust flags μ) (contours gates : ℕ → Set Sphere) :
    PathCodeData Sphere Sphere :=
  { base with
    target := p
    priorLaws := μ
    priorDeletions := R.priorDeletions
    flagDeletions := R.flagDeletions
    gateContours := contours
    gateSets := gates }

def RecursiveCodeGeometry.of_presentation
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (he : ∀ y : base.physicalDomain, (base.domainEquiv y).val = π y.val)
    (p : Sphere) (hp : p ∈ base.dust)
    {flags : Set Sphere} {μ : ℕ → Measure C(PathTime, Sphere)}
    (R : PriorLawPresentation base.dust flags μ) (contours gates : ℕ → Set Sphere) :
    RecursiveCodeGeometry base π flags where
  data := endpointCodeData base p R contours gates
  physical_eq := rfl
  quotient_eq := rfl
  dust_eq := rfl
  anchor_eq := rfl
  levels_eq := rfl
  weights_eq := rfl
  domain_agrees := he
  target_dust := hp
  presentation := R
  prior_deletions_eq := rfl
  flag_deletions_eq := rfl

def positiveRecursiveBudgets (ω : TupleType → ℝ≥0∞) (r : ℝ≥0) (hr : 0 < r) :
    RecursiveLawBudgets where
  occupationMass := densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹
  tupleMass := densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹
  energy := (r : ℝ≥0∞)⁻¹
  visitConstant := (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1
  occupationMass_finite := densityMassBound_lt_top sphericalArea
    (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hr))
  energy_finite := ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hr)
  visitConstant_finite := ENNReal.add_lt_top.mpr ⟨ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hr.ne')), by simp⟩

local instance localInst_rab1c54_4 : BorelSpace Sphere := ⟨rfl⟩
def RecursiveCodeLaw.of_positive_candidate
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {flags : Set Sphere}
    (G : RecursiveCodeGeometry base π flags) (ω : TupleType → ℝ≥0∞)
    (r : ℝ≥0) (hr : 0 < r) (ε : ℝ)
    (P : ProbabilityMeasure (BasePathCode G.data))
    (hP : CodeLawCandidate G.data (fun x : G.presentation.marks => x.val)
      sphericalArea (tupleReference ω)
      (densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹)
      (densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹)
      (r : ℝ≥0∞)⁻¹ (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1) ^ 2) P)
    (hfinite : ∀ F : Finset G.data.dust,
      ∑ x ∈ F, pathHitReal (codePathLaw G.data P) x.val ^ 2 ≤
        (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1).toReal + ε) ^ 2)
    (hcount : {x : Sphere | x ∈ G.data.dust ∧
      0 < pathHitProbability (codePathLaw G.data P) x}.Countable) :
    RecursiveCodeLaw base π flags ω :=
  ⟨G, ⟨positiveRecursiveBudgets ω r hr, P, hP,
    ((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1).toReal + ε, hfinite,
    by simpa only [pathHitProbability_codePathLaw] using hcount⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SourceMapNeighborhood
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open conditions on finitely many source traces retain compact target anchors,
Jordan sides, and separation from the compact set excluded from the energy integral. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem jordan_circle_range (H : ℂ ≃ₜ ℂ) :
    range (fun t : Circle => H (t : ℂ)) = frontier (jordanInterior H) := by
  rw [frontier_jordanInterior]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

 def sourceJordanCircle {G : Set Sphere} (H : ℂ ≃ₜ ℂ)
    (hH : frontier (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G) :
    C(Circle, FiniteSource G) :=
  ⟨fun t => ⟨H t, hH ((jordan_circle_range H).symm ▸ mem_range_self t)⟩,
    (H.continuous.comp continuous_subtype_val).subtype_mk _⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedRealSmallness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At every unmarked end the actual selected family contains arbitrarily
small anchored plateaus, with its real boundary-band norm. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

def SmallAnchoredPlateaus {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (F : FiniteTransfer.CountableRealCoordinates G π σ)
    (EStar : Set Sphere) (p : Sphere) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (i : ℕ) (U : Set Sphere), IsOpen U ∧ p ∈ U ∧
    (∀ x ∈ U ∩ F.source, F.coordinate i x = 1) ∧
    (∀ x ∈ EStar, F.coordinate i x = 0) ∧
    Real.sqrt (∫ x in FiniteTransfer.realChartDomain G,
      FiniteTransfer.gradientEnergy (F.physical i)
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) +
    Real.sqrt (∑' s, (F.upper i s - F.lower i s) ^ 2) < δ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcPointAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point avoidance outside the original law's positive-hit set survives
the actual subarc selector and compact conditioning. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def RecursiveCodeLaw.extendedHitFlags
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω) :
    Set Sphere := Flags ∪ {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetargetedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport a constructed weighted collar along an equality of target
points without changing its physical disk or quotient region. -/
open Set
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity.WeightedCollar
variable {G B : Set Sphere} {π : Sphere → Sphere} {p q : Sphere} {g : ℂ → ℝ≥0∞}

def retarget (D : WeightedCollar G π B p g) (h : q = p) : WeightedCollar G π B q g := by
  subst q
  exact D

end CircleDomainRigidity.WeightedCollar

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PersistentSavedBarriers
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual recursive construction preserves every saved separating
barrier at every later finite stage. No infinite pair-nullity is needed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def SavedSeparatingFamily.Holds {G : Set Sphere} {a η : ℝ}
    {p q : EuclideanPlane → ℝ}
    {Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G)}
    {Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G)}
    (S : SavedSeparatingFamily G a η p q Wp Wq) (p' q' : EuclideanPlane → ℝ) : Prop :=
  ∀ i,
    (∀ z ∈ S.neighborhood i, S.barrier i (planePair (p' (complexPlaneCoordinates.symm z))
      (q' (complexPlaneCoordinates.symm z))) = 1) ∧
    (∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
      S.barrier i (planePair (p' (complexPlaneCoordinates.symm z))
        (q' (complexPlaneCoordinates.symm z))) = 0) ∧
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => S.barrier i (planePair (p' x) (q' x)))
      (physicalPlaneDomain G ∩ ball 0 (65*a)),
      (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConjugateBeltramiL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Beurling operator in the physical plane. Its exact L2
isometry supplies the operator previously parameterized in conductivity
contraction; no second fixed-point argument is needed. -/
open MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

 def complexLpToPhysical : PlaneL2 →ₗᵢ[ℂ] ComplexPlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ complexPlaneCoordinates complexPlaneCoordinates_measurePreserving

 def physicalLpToComplex : ComplexPlaneL2 →ₗᵢ[ℂ] PlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ complexPlaneCoordinates.symm
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)

 def physicalBeurling : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2 :=
  (complexLpToPhysical.toContinuousLinearMap.comp
    (beurling.comp physicalLpToComplex.toContinuousLinearMap)).restrictScalars ℝ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SignedScalarTests
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact real tests can be encoded by unit-interval tests and a common
cutoff. On the dust this is an affine coordinate change, so pair-nullity
is preserved exactly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def signedScalarEncoding_witness
    {U : Set EuclideanPlane} {η u : EuclideanPlane → ℝ}
    (Hη : DeGiorgi.MemW1pWitness 2 η U) (Hu : DeGiorgi.MemW1pWitness 2 u U) (C : ℝ) :
    DeGiorgi.MemW1pWitness 2 (signedScalarEncoding η u C) U :=
  ((Hη.add (Hu.smul C⁻¹)).smul (2 : ℝ)⁻¹).congr_ae (Eventually.of_forall fun x => by
    simp only [signedScalarEncoding, div_eq_mul_inv]
    ring)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_EmptyDustScalarModel
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The empty-dust case uses the identity and the original Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 def compactScalarCircleModel_identity {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) univ) :
    CompactScalarCircleModel univ u := by
  have hf : extendAtInfinity (id : ℂ → ℂ) = (id : Sphere → Sphere) := by
    funext p
    cases p using OnePoint.rec <;> rfl
  refine {
    function := id
    normalized := ?_
    conformal := ?_
    circle := ?_
    projection := id
    projection_continuous := continuous_id
    projection_inverse := ?_
    projection_outside := ?_
    projection_component := ?_
    witness := fun i => (H i).congr_ae (Eventually.of_forall fun x => ?_)
    gradient_zero := ?_ }
  · rw [hf]
    refine ⟨rfl, ?_⟩
    simpa only [id_eq, finiteCoord_coe, sub_self] using
      (Asymptotics.isBigO_zero (E' := ℂ) (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ))
  · simpa only [hf, image_id] using isConformalEquivalence_id (univ : Set Sphere)
  · simpa only [hf, image_id] using isCircleDomain_univ
  · intro p _
    rw [hf]
    rfl
  · intro p hp
    exact (hp (by rw [hf, image_id]; trivial)).elim
  · intro p hp
    exact (hp (by rw [hf, image_id]; trivial)).elim
  · simp only [id_eq, planeSphere, sphereFromPlaneFunction_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  · intro i j
    exact Eventually.of_forall fun x hx => (hx (by rw [hf, image_id]; trivial)).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.SquareMeshConnected
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFinitePlaneProdFinOfNatNatK33Graph _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.Schoenflies.CellStructure.Realization.finite_graph _root_.Schoenflies.decidableCrosses
set_option linter.all false
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The inner grid of the anchored square mesh: 2-connectivity and the outer cycle

`Schoenflies/SquareMesh.lean` delivers the geometry of `prop:anchored-square-mesh` — the
diameter bound, the anchors, the inward edges at the fresh points, and connectedness of
`|T| ∖ S` — and leaves two clauses open, both of them combinatorial:

* clause 5, *the skeleton of `T` is 2-connected*, is absent;
* clause 3 is proved only as a point-set equation, never as a **cycle** of the graph.

This module supplies both for the object the blueprint's own proof of the proposition is about:
the **rectangular grid**. See "What this does and does not close" below for exactly what the
integrator still has to do.

## The grid, concretely

Two coordinate functions `xc yc : ℕ → ℝ` and two sizes `m n : ℕ` fix a grid: the vertices are
the `(m+1)(n+1)` points `gridPt xc yc i j = (xc i, yc j)`, the edges are the `m(n+1)`
horizontal steps `gridHEdge` and the `(m+1)n` vertical steps `gridVEdge`. Everything is a
`def` — an existentially quantified grid could not be refined against a second one, which is
what Part II does.

The hypotheses on the coordinates are exactly as strong as each statement needs, and no
stronger: 2-connectivity needs only that **consecutive** coordinates differ, the outer cycle
needs the coordinates **distinct** (`Set.InjOn xc (Set.Iic m)`), and only the drawing — the
clause that makes the grid a plane graph — needs them **increasing**
(`StrictMonoOn xc (Set.Iic m)`).

The graph is `pieceListGraph (gridEdges xc yc m n)`, where `pieceListGraph` is the general
"a list of straight segments, read as a graph" constructor: an edge is a `Piece`, and it links
exactly its two ends. `pieceListGraph` is `overlayGraph` without the subdivision — the vertices
are the ends of the listed segments and nothing is cut — and its point is that
`pieceListGraph l₁ ∪ pieceListGraph l₂ = pieceListGraph (l₁ ++ l₂)` **on the nose**
(`pieceListGraph_union`), so that the blueprint's "add these finitely many cycles one at a
time" is list concatenation and every union is an equation rather than an inclusion.

## 2-connectivity: two nested chains of `lem:union-two-connected`

The blueprint says "the inner grid is 2-connected by the same ear construction used for `K`".
The ear construction is replaced here by two applications of `Graph.IsTwoConnected.union`,
which is shorter and needs no ear at all:

* one **cell** — the boundary of a single rectangle of the grid — is a quadrilateral, and
  `Graph.isTwoConnected_of_quad` proves any quadrilateral 2-connected directly from the
  definition (delete a vertex; the other three are still a path);
* a **strip** (one column of cells) is the union of its cells, consecutive cells sharing the
  horizontal edge between them, hence two vertices;
* the **grid** is the union of its strips, consecutive strips sharing the whole vertical line
  between them, hence again two vertices.

Both chains need at least two vertices in common at every step, so both need `1 ≤ m` and
`1 ≤ n`: a grid with a single row of points is a path and is not 2-connected. That is the
degenerate case, and it is a hypothesis, not an oversight.

## The outer cycle

The boundary walk goes once round the four sides, `gridBoundaryEdge` and `gridBoundaryPt`
naming the `2m + 2n` edges and vertices in order by a four-way `if` on the index. Everything
about the walk is then arithmetic in `ℕ`, which `omega` decides.
`gridGraph_isCycleThrough_boundary` is a `Graph.IsCycleThrough` of the grid graph — the
distinguished outer cycle — and `edgesCover_gridBoundary` computes what it occupies: for
increasing coordinates it is exactly the frame of the bounding rectangle, and for the grid on
`[-1,1]²` that frame is `modelCurve`, i.e. `S` (`edgesCover_gridBoundary_modelCurve`,
`gridGraph_outer_cycle`). That is the cycle `thm:finite-transfer`(b) asks for, in the form it
asks for it.

The grid is also shown to be a **plane graph** (`gridGraph_isDrawing`), so the outer cycle is a
Jordan curve (`gridBoundary_isJordanCurve`) and the whole face machinery applies to it.

## What this does and does not close

**Closed.** Both clauses, for the rectangular grid, from an explicit construction, together
with the drawing that makes the grid a plane graph.

**Not closed.** Neither clause is transported to `Schoenflies.squareMesh`, and the reason is
structural, not a matter of effort: `squareMesh` is `overlayGraph` applied to a list of
segments *and an unspecified list of cut points* obtained from `exists_cut_points` by choice.
Its edges are therefore the pieces of a subdivision nobody can enumerate, so neither "the
edges on `S` form a cycle" nor "the rings are cycles glued along the spokes" is available
without first proving that the subdivision of a segment at a finite point set is a **path** —
a theorem no module on `main` has. The honest statement of the missing collar step is
`Graph.IsTwoConnected.attach_cycles` below: it takes a 2-connected hub `K` and finitely many
2-connected pieces each meeting `K` in two distinct vertices, and concludes for the union.
Instantiating it at `squareMesh` needs the collar rectangles of the mesh as cycles, which is
exactly the enumeration that is missing.

**A degenerate case that would have to be excluded.** `squareMesh δ fresh anchors` is *not*
2-connected when `fresh` has fewer than two distinct points, so the missing theorem cannot be
stated without a hypothesis. With `fresh = []` the mesh is `meshCount δ` pairwise disjoint
concentric ring frames and is not even connected. With one fresh point `z` the spoke at `z` is
the only thing joining the rings, so every vertex of that spoke is a cut vertex: deleting the
one at radius `k/N` separates the rings inside it from the rings outside. Two fresh points are
what make the rings and the two spokes a chain of quadrilaterals, which is the same picture the
grid presents here. The corresponding hypothesis for the grid is `1 ≤ m` and `1 ≤ n`, and it is
carried explicitly by every theorem below that needs it.

## Blueprint

* `prop:anchored-square-mesh`, clause 5, for the inner grid — `gridGraph_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 3, as a cycle — `gridGraph_isCycleThrough_boundary`
  together with `edgesCover_gridBoundary`, `edgesCover_gridBoundary_modelCurve` and the
  packaged `gridGraph_outer_cycle`.
* `lem:polygonal-overlay`, the drawing clause, for the grid — `gridGraph_isDrawing`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union`; iterated here as
  `Graph.IsTwoConnected.attach_cycles`, which is the blueprint's "adding these finitely many
  cycles one at a time".
* `pieceListGraph`, `pieceListGraph_union` — the list-of-segments graph, and the fact that its
  unions are concatenations.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### The graph carried by a list of segments

`overlayGraph` subdivides; this does not. When the segments are already in general position —
which for a grid they are, by construction — no subdivision is wanted, and what is gained is
that unions are concatenations.

`Schoenflies/ArcComplement.lean` has the same construction indexed by a `Set Piece`, under the
name `segGraph`, and `pieceListGraph l` is `segGraph {P | P ∈ l}`. The two were written in
parallel and collided at merge; they are kept apart for now because this module's proofs run on
the list and the other's on the set. If a third consumer appears, hoist the set version into
`Schoenflies/OverlayGraph.lean` beside `endSet` and derive this one from it. -/

instance pieceListGraph_finite (l : List Piece) : Graph.Finite (pieceListGraph l) where
  finite_vertexSet := finite_endSet l
  finite_edgeSet := l.finite_toSet

/-! ### The rectangular grid

Two coordinate functions and two sizes. Nothing here asks the coordinates to be sorted: the
combinatorics needs only that **consecutive** coordinates differ, which is exactly what makes
each cell a genuine quadrilateral. Sortedness enters only with the geometry of the outer
cycle. -/

/-! ### The cell -/

/-! ### The strip, then the grid

Two chains of `Graph.IsTwoConnected.union`, and the two shared vertices are in each case the
two ends of one edge that both parts contain. -/

/-! ### Which grid edges exist

Two membership lemmas, both by the same trick: a horizontal edge at height `n` is the *top*
of a cell rather than the bottom of one, and a vertical edge on the line `i = m` is the *right*
side of a cell rather than the left. -/

/-! ### The outer cycle

The boundary of the grid, walked once anticlockwise from the corner `(0,0)`: `m` steps right
along the bottom, `n` up the right side, `m` back along the top, `n` down the left side. The
walk is parametrised by an index `t < 2m + 2n`, and both the vertex and the edge at index `t`
are given by a four-way `if`. Everything about the walk then reduces to arithmetic in `ℕ`,
which `omega` decides; the geometry enters only in `edgesCover_gridBoundary` at the end. -/

/-! ### What the outer cycle occupies

Up to here nothing has been asked of the order of the coordinates. It is asked now: the union
of the boundary edges is the frame of the bounding rectangle only if the coordinates increase,
and the proof is the one-dimensional fact `Set.Icc_union_Icc_eq_Icc` transported along
`Schoenflies.mem_segment_horiz` / `mem_segment_vert`. -/

/-! ### Consecutive intervals -/

/-! ### The grid is a plane graph

Sorted coordinates make the drawing clause a coordinate computation. A point of a horizontal
grid edge has the row's `y`-coordinate and an `x`-coordinate in one closed coordinate interval;
strict monotonicity turns "`xc a` lies in `[xc i, xc (i+1)]`" into "`a = i` or `a = i+1`", and
that single step settles both remaining clauses of `Graph.IsDrawing`. -/

end Schoenflies
end


