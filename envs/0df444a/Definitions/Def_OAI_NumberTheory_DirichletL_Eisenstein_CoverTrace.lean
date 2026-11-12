-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T08:12:12.99174+00:00
-- url     : https://prove2.me/theorems/6536dd3a-37ee-4933-a7cd-fc5639b38d46
-- title:
--   Cover Trace
-- statement:
--   Definitions and structural lemmas for Cover Trace, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CoverTrace.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFundamentalSet_isFundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_integralCoverDomain_isFundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_integralCoverMap_measurable
import Theorems.Thm_OAI_CubicEisenstein_integralCoverSheet_measurable
import Theorems.Thm_OAI_CubicEisenstein_integralCoverSheet_pairwiseDisjoint
import Theorems.Thm_OAI_CubicEisenstein_integralOrbitProjection_eq
import Theorems.Thm_OAI_CubicEisenstein_integralQuotientVolume_independent
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_SixthPowerAverage_outsideWeight_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedCoeff_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedMoebius_zero
import Theorems.Thm_OAI_SmoothMobiusCorrection_mem_primeSet
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_succ
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_zero
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.cubicUnitGaussSum_one
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply
attribute [local simp] OAI.SixthPowerAverage.outsideWeight_zero
attribute [local simp] OAI.SixthPowerAverage.weightedCoeff_zero
attribute [local simp] OAI.SixthPowerAverage.weightedMoebius_zero
attribute [local simp] OAI.SmoothMobiusCorrection.mem_primeSet
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply


set_option autoImplicit false
namespace OAI
noncomputable section
namespace CubicEisenstein
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
lemma integralCoverSheet_measure (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K)
    (S : Set (IntegralOrbitQuotient K)) (hS : MeasurableSet S) :
    hyperbolicVolume ((integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q)=
      integralQuotientVolume K S := by
  have he : (integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q=
      (fun w=>integralCoverRep H K q • w) ⁻¹'
        ((integralOrbitProjection K) ⁻¹' S ∩ hyperbolicFundamentalSet K) := by
    ext w
    change (integralOrbitProjection K w∈S ∧ integralCoverRep H K q•w∈hyperbolicFundamentalSet K) ↔
      (integralOrbitProjection K (integralCoverRep H K q•w)∈S ∧
        integralCoverRep H K q•w∈hyperbolicFundamentalSet K)
    rw [integralSubgroup_smul,integralOrbitProjection_eq]
  rw [he,measure_preimage_smul]
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS)]
theorem integralCoverMap_measure {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Measure.map (integralCoverMap hHK) (integralQuotientVolume H)=
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hH : H≤CubicKubota.levelThree := hHK.trans hK
  rw [←integralQuotientVolume_independent H hH (integralCoverDomain H K)
    (integralCoverDomain_isFundamentalDomain hHK hK)]
  rw [Measure.map_map (integralCoverMap_measurable hHK) (measurable_integralOrbitProjection H)]
  change Measure.map (integralOrbitProjection K) (hyperbolicVolume.restrict (integralCoverDomain H K))=_
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS),Measure.smul_apply,smul_eq_mul]
  rw [integralCoverDomain,Set.inter_iUnion]
  rw [measure_iUnion]
  · simp_rw [integralCoverSheet_measure H K _ S hS]
    rw [tsum_fintype]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
  · intro q r hqr
    exact (integralCoverSheet_pairwiseDisjoint H K hK hqr).mono Set.inter_subset_right Set.inter_subset_right
  · intro q
    exact ((measurable_integralOrbitProjection K) hS).inter (integralCoverSheet_measurable H K q)
lemma integralCoverMap_measurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralCoverMap hHK) (integralQuotientVolume H)
      ((H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) :=
  ⟨integralCoverMap_measurable hHK,integralCoverMap_measure hHK hK⟩
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace InnerProduct
open Finset AddChar MulChar EisensteinEmbedding
section
local notation "O" => ActualEisensteinCubic.O
abbrev IntegralQuotientL2 (H : Subgroup (SL(2,ActualEisensteinCubic.O))) :=
  Lp ℂ 2 (integralQuotientVolume H)
def integralCoverPullback {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 K→L[ℂ]IntegralQuotientL2 H :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl)
def integralCoverTrace {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 H→L[ℂ]IntegralQuotientL2 K :=
  ContinuousLinearMap.adjoint (integralCoverPullback hHK hK)
def integralCoverAverage {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 H→L[ℂ]IntegralQuotientL2 K :=
  (H.relIndex K:ℂ)⁻¹ • integralCoverTrace hHK hK
end
local notation "O" => ActualEisensteinCubic.O
def integralCoverFiberPoint (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) : IntegralOrbitQuotient H :=
  Quotient.liftOn' q (fun r : K=>integralOrbitProjection H (r⁻¹•w)) (by
    intro a b hab
    have hh : b⁻¹*a∈H.subgroupOf K := by
      have h : a⁻¹*b∈H.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev,inv_inv] using (H.subgroupOf K).inv_mem h
    apply Quotient.sound
    refine ⟨⟨((b⁻¹*a:K):SL(2,ActualEisensteinCubic.O)),hh⟩,?_⟩
    change (b⁻¹*a)•(a⁻¹•w)=b⁻¹•w
    simp only [mul_smul,smul_inv_smul])
lemma integralCoverFiberPoint_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (k : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K (k•q) (k•w)=integralCoverFiberPoint H K q w := by
  induction q using Quotient.inductionOn with
  | _ r =>
    change integralOrbitProjection H ((k*r)⁻¹•(k•w))=integralOrbitProjection H (r⁻¹•w)
    rw [mul_inv_rev,mul_smul,inv_smul_smul]
def integralCoverTraceLift (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (w : HyperbolicSpace) : ℂ :=
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)
lemma integralCoverTraceLift_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (k : K) (w : HyperbolicSpace) :
    integralCoverTraceLift H K f (k•w)=integralCoverTraceLift H K f w := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  unfold integralCoverTraceLift
  rw [←(MulAction.bijective k).sum_comp (fun q=>f (integralCoverFiberPoint H K q (k•w)))]
  simp only [integralCoverFiberPoint_smul]
def integralCoverTraceFunction (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) : IntegralOrbitQuotient K→ℂ :=
  Quotient.lift (integralCoverTraceLift H K f) (by
    rintro w u ⟨k,rfl⟩
    exact (integralCoverTraceLift_smul H K f k w).symm)
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
def IntegralCoverIntertwines {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) : Prop :=
  ∀h : H,g*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (e h:SL(2,ActualEisensteinCubic.O))*g
lemma integralCoverIntertwines_action {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (h : H) (w : HyperbolicSpace) : g•(h•w)=(e h)•(g•w) := by
  rw [integralSubgroup_smul,integralSubgroup_smul,←mul_smul,he, mul_smul]
lemma integralCoverIntertwines_inverse {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralCoverIntertwines e.symm g⁻¹ := by
  intro j
  have hh := he (e.symm j)
  rw [e.apply_symm_apply] at hh
  have hh' := congrArg (fun A : SL(2,ℂ)=>g⁻¹*A*g⁻¹) hh
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh'.symm
def integralConjugateMap {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient J :=
  Quotient.map' (fun w=>g•w) (by
    rintro w u ⟨h,rfl⟩
    exact ⟨e h,(integralCoverIntertwines_action e g he h w).symm⟩)
lemma integralConjugateMap_measurable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    Measurable (integralConjugateMap e g he) := by
  apply measurable_from_quotient.mpr
  exact (measurable_integralOrbitProjection J).comp (measurable_const_smul g)
lemma integralConjugateMap_continuous {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    Continuous (integralConjugateMap e g he) :=
  (continuous_hyperbolic_action g).quotient_map' _
lemma integralConjugateMap_inverse {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
      (integralConjugateMap e g he q)=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection H (g⁻¹•(g•w))=integralOrbitProjection H w
    rw [inv_smul_smul]
def integralConjugateHomeomorph {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H≃ₜIntegralOrbitQuotient J where
  toFun := integralConjugateMap e g he
  invFun := integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
  left_inv := integralConjugateMap_inverse e g he
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ w =>
      change integralOrbitProjection J (g•(g⁻¹•w))=integralOrbitProjection J w
      rw [smul_inv_smul]
  continuous_toFun := integralConjugateMap_continuous e g he
  continuous_invFun := integralConjugateMap_continuous e.symm g⁻¹ _
lemma integralConjugate_fundamentalDomain {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) :
    IsFundamentalDomain J ((fun w : HyperbolicSpace=>g•w) '' hyperbolicFundamentalSet H)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain H hH).image_of_equiv
    (MulAction.toPerm g)
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm g).symm
      hyperbolicVolume hyperbolicVolume from
      (measurePreserving_smul g⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    e.symm.toEquiv
  intro j w
  change g•(e.symm j•w)=j•(g•w)
  simpa only [e.apply_symm_apply] using integralCoverIntertwines_action e g he (e.symm j) w
theorem integralConjugateMap_measurePreserving {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    MeasurePreserving (integralConjugateMap e g he) (integralQuotientVolume H)
      (integralQuotientVolume J) := by
  refine ⟨integralConjugateMap_measurable e g he,?_⟩
  have hmap := (measurePreserving_smul g hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul g) (hyperbolicFundamentalSet H)
  change Measure.map (integralConjugateMap e g he)
    (Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)))=_
  rw [Measure.map_map (integralConjugateMap_measurable e g he) (measurable_integralOrbitProjection H)]
  change Measure.map ((integralOrbitProjection J) ∘ (fun w : HyperbolicSpace=>g•w))
    (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))=_
  rw [←Measure.map_map (measurable_integralOrbitProjection J) (measurable_const_smul g),hmap.map_eq]
  exact integralQuotientVolume_independent J hJ _ (integralConjugate_fundamentalDomain e g he hH)
def integralConjugatePullback {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    Lp ℂ 2 (integralQuotientVolume J)→ₗᵢ[ℂ]Lp ℂ 2 (integralQuotientVolume H) :=
  Lp.compMeasurePreservingₗᵢ ℂ (integralConjugateMap e g he)
    (integralConjugateMap_measurePreserving e g he hH hJ)
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
lemma complex_upper_triangular_bottom_ne_zero (T : SL(2,ℂ)) (hT : T 1 0=0) : T 1 1≠0 := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using T.property
  intro hz
  rw [hz,mul_zero] at hdet
  exact zero_ne_one hdet
end CubicEisenstein
end
end OAI


