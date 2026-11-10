-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T07:17:12.51975+00:00
-- url     : https://prove2.me/theorems/e9cc103d-290d-421d-8dfe-daf0db0e3b64
-- title:
--   Literal Sources
-- statement:
--   Definitions and structural lemmas for Literal Sources, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_continuous_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_le_levelThree
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFrobenius_continuous
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_integral_frobenius_sublevel_finite
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_subgroup_action_free
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
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
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
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply


set_option autoImplicit false
namespace OAI
noncomputable section
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
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
open ActualEisensteinCubic
open JointLogSeparation (frequencyTwist)
open SecondPassIntegration (densityChildEnergy)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalSecondLiteralBinSource (γ : GlobalSecondData ι → ℂ)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) : ℂ :=
  ∑ ray : SecondRayIndex,∑ x∈globalLogSector p s side j,
    γ x * globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g₁ g₂ W ell Y side x
end
end SecondPassArithmetic
namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
local notation "O" => ActualEisensteinCubic.O
lemma complex_norm_mul_add_sq (a b c d : ℂ) :
    ‖a*c+b*d‖^2≤(‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have ht : ‖a*c+b*d‖≤‖a‖*‖c‖+‖b‖*‖d‖ := by simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  have hs := pow_le_pow_left₀ (norm_nonneg (a*c+b*d)) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]
lemma matrixFrobenius_nonneg (g : SL(2,ℂ)) : 0≤matrixFrobenius g := by
  unfold matrixFrobenius rowEnergy
  positivity
lemma matrixFrobenius_mul_le (g h : SL(2,ℂ)) :
    matrixFrobenius (g*h)≤matrixFrobenius g*matrixFrobenius h := by
  have hb (i j : Fin 2) := complex_norm_mul_add_sq (g i 0) (g i 1) (h 0 j) (h 1 j)
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  nlinarith only [hb 0 0,hb 0 1,hb 1 0,hb 1 1]
lemma matrixFrobenius_inv (g : SL(2,ℂ)) : matrixFrobenius g⁻¹=matrixFrobenius g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow]
  change ‖g 1 1‖^2+‖-g 0 1‖^2+(‖-g 1 0‖^2+‖g 0 0‖^2)=_
  simp only [norm_neg]
  ring
lemma hyperbolicFrobenius_nonneg (w : HyperbolicSpace) : 0≤hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ g => exact matrixFrobenius_nonneg g
lemma matrixFrobenius_le_displacement (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    matrixFrobenius g≤hyperbolicFrobenius (g • w)*hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change matrixFrobenius g≤matrixFrobenius (g*h)*matrixFrobenius h
    have hb := matrixFrobenius_mul_le (g*h) h⁻¹
    simpa only [mul_inv_cancel_right,matrixFrobenius_inv] using hb
instance integralSubgroupContinuousAction (H : Subgroup (SL(2,O))) :
    ContinuousConstSMul H HyperbolicSpace :=
  ⟨fun M => continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))⟩
instance integralSubgroupProperlyDiscontinuous (H : Subgroup (SL(2,O))) :
    ProperlyDiscontinuousSMul H HyperbolicSpace where
  finite_disjoint_inter_image := by
    intro source target hsource htarget
    obtain ⟨C,hC⟩ := hsource.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    obtain ⟨D,hD⟩ := htarget.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    have hfin : Set.Finite {M : H | matrixFrobenius (integralComplexMatrix (M:SL(2,O)))≤
        max D 0*max C 0} := by
      have hf := Set.Finite.preimage (f := fun M : H => (M:SL(2,O))) Subtype.val_injective.injOn
        (integral_frobenius_sublevel_finite 1 (max D 0*max C 0))
      simpa only [mul_one,Set.preimage_ofPred_eq] using hf
    apply hfin.subset
    rintro M ⟨u,⟨w,hw,rfl⟩,hu⟩
    have hb := matrixFrobenius_le_displacement (integralComplexMatrix (M:SL(2,O))) w
    apply hb.trans
    apply mul_le_mul
    · exact ((le_abs_self _).trans (hD _ hu)).trans (le_max_left _ _)
    · exact ((le_abs_self _).trans (hC _ hw)).trans (le_max_left _ _)
    · exact hyperbolicFrobenius_nonneg _
    · exact le_max_right _ _
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
namespace CubicEisenstein
section
local notation "O" => ActualEisensteinCubic.O
instance upperCoordinatesLocallyCompact : LocallyCompactSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).locallyCompactSpace
instance hyperbolicLocallyCompact : LocallyCompactSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
instance hyperbolicSecondCountable : SecondCountableTopology HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.secondCountableTopology
instance upperCoordinatesPolish : PolishSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).polishSpace
instance hyperbolicPolish : PolishSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isClosedEmbedding.polishSpace
lemma integralOrbitRel_eq (H : Subgroup (SL(2,O))) :
    integralOrbitRel H=MulAction.orbitRel H HyperbolicSpace := by
  ext u v
  change (∃M:H,M • u=v) ↔ ∃M:H,M • v=u
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩
instance integralOrbitQuotientT2 (H : Subgroup (SL(2,O))) : T2Space (IntegralOrbitQuotient H) := by
  change T2Space (Quotient (integralOrbitRel H))
  rw [integralOrbitRel_eq]
  infer_instance
lemma integralSubgroupFree (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCancelSMul H HyperbolicSpace :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (subgroup_action_free H hH)
lemma integralOrbitProjection_eq_iff (H : Subgroup (SL(2,O))) (u v : HyperbolicSpace) :
    integralOrbitProjection H u=integralOrbitProjection H v ↔ u∈MulAction.orbit H v := by
  constructor
  · intro he
    obtain ⟨M,hM⟩ := Quotient.exact he.symm
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨M,hM⟩
theorem integralOrbitProjection_quotientCovering (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) : IsQuotientCoveringMap (integralOrbitProjection H) H := by
  let : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  have hq : Topology.IsQuotientMap (integralOrbitProjection H) := isQuotientMap_quotient_mk'
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (integralOrbitProjection_eq_iff H _ _)
lemma integralOrbitProjection_covering (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCoveringMap (integralOrbitProjection H) :=
  (integralOrbitProjection_quotientCovering H hH).isCoveringMap
lemma integralOrbitProjection_openQuotient (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsOpenQuotientMap (integralOrbitProjection H) :=
  ⟨Quotient.mk_surjective,continuous_integralOrbitProjection H,
    (integralOrbitProjection_covering H hH).isOpenMap⟩
instance kernelQuotientLocallyCompact : LocallyCompactSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).locallyCompactSpace
instance kernelQuotientSecondCountable : SecondCountableTopology (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).isQuotientMap.secondCountableTopology
    (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).isOpenMap
instance kernelQuotientBorel : BorelSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  Quotient.borelSpace
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
@[ext] structure GlobalFirstData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι
namespace GlobalFirstData
variable {ι : Type*}
def append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : GlobalSecondData ι :=
  ⟨b.cube,b.firstCommon,b.common,b.firstDivisor,x⟩
end GlobalFirstData
namespace GlobalSecondData
variable {ι : Type*}
def first (x : GlobalSecondData ι) : GlobalFirstData ι :=
  ⟨x.cube,x.firstCommon,x.common,x.firstDivisor⟩
end GlobalSecondData
section
variable {ι : Type*} [DecidableEq ι]
def globalFirstRawPool (pool : Finset ι) (b : GlobalFirstData ι) : Finset ι :=
  (pool\(b.cube.support∪b.common))\b.firstCommon
def globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : Finset (GlobalSecondData ι) :=
  s.biUnion (fun b => (secondExpansionPool (globalFirstRawPool pool b) (cutoff b)).image b.append)
end
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalFirstBlockColumnScale (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  ell/(primeProductNorm p (b.cube.sideDivisor side)*primeProductNorm p b.common)
def globalFirstBlockLabel (b : GlobalFirstData ι) : O :=
  secondBaseLabel p b.cube.support b.common b.cube.leftExponent b.cube.rightExponent b.cube.leftBit b.cube.rightBit
def globalFirstBlockBadLabel (b : GlobalFirstData ι) : O :=
  b0Label p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
def globalFirstBlockTest (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : Finset ι → ℂ :=
  normalizedColumn p (fun A => g (columnLog p
    (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) A))
def globalFirstTruncatedSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondSource p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalFirstCoreRow (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayCharacter)
    (r : FirstCoreIndex) (t : ℝ) (b : GlobalFirstData ι) (z : O) : ℂ :=
  firstCoreInputRow p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t z
def globalFirstCoreCorrection (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) : ℝ :=
  ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b)) side t b.firstCommon ∅‖^2
def globalFirstSourceTail (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    secondSourceTail p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)
def globalFirstSourceZero
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondZero p hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)
end SecondPassArithmetic
end
end OAI


