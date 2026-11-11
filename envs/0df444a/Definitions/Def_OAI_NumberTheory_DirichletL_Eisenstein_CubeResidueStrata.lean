-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:20:46.204225+00:00
-- url     : https://prove2.me/theorems/583b358a-1e92-4bb7-8da8-e11da376a1d8
-- title:
--   Cube Residue Strata
-- statement:
--   Definitions and structural lemmas for Cube Residue Strata, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_PrimaryCongruences
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_span
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_unit_eq_sign_omega
import Theorems.Thm_OAI_CubicKubota_cube_average_cusp_reduction
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
import Theorems.Thm_OAI_GaussianShiftedPartition_representative_spec
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_lambda_prime_actual
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_primaryGenerator_span_ne_zero_iff
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
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
end SubexponentialBesselCoefficients
end
open scoped BigOperators Classical MatrixGroups Matrix
section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal GoodElement)
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)
lemma halfPrimary_lambda_dvd_three : ramLambda ∣ (3:Eis) := by
  exact (dvd_pow_self ramLambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
lemma halfPrimary_lambda_not_dvd_one : ¬ramLambda ∣ (1:Eis) := by
  intro h
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h)
lemma halfPrimary_omega_pow (j:ℕ) : ramLambda ∣ omega^j-1 := by
  simpa only [one_pow] using sub_dvd_pow_sub_pow omega (1:Eis) j
lemma halfPrimary_not_negative (j:ℕ) : ¬ramLambda ∣ -(omega^j)-1 := by
  intro h
  have h2 : ramLambda ∣ (2:Eis) := by
    have hh:=dvd_add h (halfPrimary_omega_pow j)
    convert dvd_neg.mpr hh using 1 ;ring
  apply halfPrimary_lambda_not_dvd_one
  convert dvd_sub halfPrimary_lambda_dvd_three h2 using 1 ;ring
abbrev HalfPrimary := {b:Eis // ramLambda ∣ b-1}
lemma halfPrimary_not_dvd (b:HalfPrimary) : ¬ramLambda∣b.val := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  convert dvd_sub h b.2 using 1 ;ring
def halfPrimaryFromAssociate (p:Fin 3×PrimaryLower) : HalfPrimary :=
  ⟨omega^p.1.val*p.2.val,by
    have ha:ramLambda∣p.2.val-1:=halfPrimary_lambda_dvd_three.trans p.2.2
    convert dvd_add ((halfPrimary_omega_pow p.1.val).mul_right p.2.val) ha using 1 ;ring⟩
lemma halfPrimaryFromAssociate_injective : Function.Injective halfPrimaryFromAssociate := by
  intro p q hpq
  have he:omega^p.1.val*p.2.val=omega^q.1.val*q.2.val:=congrArg Subtype.val hpq
  have hunit (j:Fin 3):IsUnit (omega^j.val):=(omega_primitive.isUnit (by decide)).pow _
  have hs:(Ideal.span {p.2.val}:Ideal Eis)=Ideal.span {q.2.val}:=by
    simpa only [Ideal.span_singleton_mul_left_unit (hunit p.1),
      Ideal.span_singleton_mul_left_unit (hunit q.1)] using
      congrArg (fun z:Eis=>(Ideal.span {z}:Ideal Eis)) he
  have hab:p.2=q.2:=by
    apply Subtype.ext
    have hg:=congrArg primaryGenerator hs
    simpa only [primaryGenerator_span p.2.val (primaryLower_ne_zero p.2) (primaryLower_primary p.2),
      primaryGenerator_span q.2.val (primaryLower_ne_zero q.2) (primaryLower_primary q.2)] using hg
  have hj:p.1=q.1:=by
    apply Fin.ext
    apply omega_primitive.pow_inj p.1.isLt q.1.isLt
    rw [hab] at he
    exact mul_right_cancel₀ (primaryLower_ne_zero q.2) he
  exact Prod.ext hj hab
lemma halfPrimaryFromAssociate_surjective : Function.Surjective halfPrimaryFromAssociate := by
  intro b
  let z:GoodElement:=⟨b.val,PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff b.val |>.mpr
    (halfPrimary_not_dvd b)⟩
  let p:=PrimaryIdealUnitReindex.unitIdealEquiv.symm z
  have he:(p.1:Eis)*primaryGenerator p.2.val=b.val:=
    congrArg Subtype.val (PrimaryIdealUnitReindex.unitIdealEquiv.apply_symm_apply z)
  let a:PrimaryLower:=primaryLowerIdealEquiv.symm p.2
  have ha:a.val=primaryGenerator p.2.val:=rfl
  have hea:(p.1:Eis)*a.val=b.val:=by simpa only [ha] using he
  have hu:ramLambda∣(p.1:Eis)-1:=by
    have hpa:ramLambda∣a.val-1:=halfPrimary_lambda_dvd_three.trans a.2
    have hh:=dvd_sub b.2 (hpa.mul_left (p.1:Eis))
    rw [←hea] at hh
    convert hh using 1 ;ring
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega p.1
  · exact ⟨(j,a),Subtype.ext (by simpa only [halfPrimaryFromAssociate,hj] using hea)⟩
  · exact (halfPrimary_not_negative j.val (by simpa only [hj] using hu)).elim
def halfPrimaryAssociateEquiv : Fin 3×PrimaryLower ≃ HalfPrimary :=
  Equiv.ofBijective halfPrimaryFromAssociate
    ⟨halfPrimaryFromAssociate_injective,halfPrimaryFromAssociate_surjective⟩
end
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
def unitCuspUpper (b : Eis) : SL(2,Eis) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def unitCuspDiagonal (u : Eisˣ) : SL(2,Eis) := ⟨!![(u:Eis),0;0,(↑u⁻¹:Eis)],by
  simp [Matrix.det_fin_two]⟩
end CubicEisenstein
open scoped Classical MatrixGroups
namespace CubicEisenstein
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
abbrev CubeResidueStrata (p:Eis) := Σj:Fin 4,CubicUnitResidue (p^(3-j.val))
def cubeResidueStratumMap (p:Eis) (x:CubeResidueStrata p) : Eis⧸Ideal.span {p^3} :=
  Ideal.Quotient.mk _ (p^x.1.val * GaussianShiftedPartition.representative (p^(3-x.1.val)) x.2.1)
lemma unit_rep_coprime (c:Eis) (x:CubicUnitResidue c) :
    IsCoprime c (GaussianShiftedPartition.representative c x.1) := by
  apply (isUnit_quotient_span_iff c _).mp
  simpa only [GaussianShiftedPartition.representative_spec] using x.2
lemma cube_strata_exponents (p:Eis) (hp:Prime p) (j k:Fin 4)
    (b d:Eis) (hb:IsCoprime (p^(3-j.val)) b)
    (he:p^3∣p^j.val*b-p^k.val*d) : ¬j.val<k.val := by
  intro hjk
  have hj3:j.val+1≤3:=by omega
  have hjk':j.val+1≤k.val:=by omega
  have h1:p^(j.val+1)∣p^j.val*b-p^k.val*d:=
    (pow_dvd_pow p hj3).trans he
  have h2:p^(j.val+1)∣p^k.val*d:=
    dvd_mul_of_dvd_left (pow_dvd_pow p hjk') d
  have h3:p^(j.val+1)∣p^j.val*b:=by
    simpa only [sub_add_cancel] using dvd_add h1 h2
  rw [pow_succ] at h3
  have hpb:p∣b:=(mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp h3
  have hpc:IsCoprime p b:=hb.of_isCoprime_of_dvd_left
    (dvd_pow_self p (by omega:3-j.val≠0))
  exact (hp.coprime_iff_not_dvd.mp hpc) hpb
lemma cubeResidueStratumMap_injective (p:Eis) (hp:Prime p) :
    Function.Injective (cubeResidueStratumMap p) := by
  rintro ⟨j,b⟩ ⟨k,d⟩ he
  have hd:p^3∣p^j.val*GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      p^k.val*GaussianShiftedPartition.representative (p^(3-k.val)) d.1 :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)
  have hle:=cube_strata_exponents p hp j k _ _ (unit_rep_coprime _ b) hd
  have hge:=cube_strata_exponents p hp k j _ _ (unit_rep_coprime _ d)
    (by simpa only [neg_sub] using dvd_neg.mpr hd)
  have hjk:j=k:=Fin.ext (by omega)
  subst k
  have hpow:p^3=p^j.val*p^(3-j.val):=by rw [←pow_add,Nat.add_sub_of_le (by omega:j.val≤3)]
  rw [hpow,←mul_sub] at hd
  have hrep:p^(3-j.val)∣GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      GaussianShiftedPartition.representative (p^(3-j.val)) d.1:=
    (mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp hd
  have hbd:b=d:=by
    apply Subtype.ext
    rw [←GaussianShiftedPartition.representative_spec (p^(3-j.val)) b.1,
      ←GaussianShiftedPartition.representative_spec (p^(3-j.val)) d.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hrep)
  subst d
  rfl
lemma cubeResidueStratumMap_surjective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    Function.Surjective (cubeResidueStratumMap p) := by
  intro r
  let a:=GaussianShiftedPartition.representative (p^3) r
  let A:SL(2,Eis):=⟨!![a,-1;1,0],by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨j,hj,N,hx,hc,hNA,hjN,hupper⟩:=cube_average_cusp_reduction A p 0 hp hprimary
  have ha:a=p^j*N 0 0:=by simpa [A] using hx
  have hc':p^3=p^j*N 1 0:=by simpa [A] using hc
  have hpow:p^3=p^j*p^(3-j):=by rw [←pow_add,Nat.add_sub_of_le hj]
  have hN10:N 1 0=p^(3-j):=by
    apply mul_left_cancel₀ (pow_ne_zero j hp.ne_zero)
    exact hc'.symm.trans hpow
  have hcop:IsCoprime (p^(3-j)) (N 0 0):=by
    refine ⟨-N 0 1,N 1 1,?_⟩
    have hd:N 0 0*N 1 1-N 0 1*N 1 0=1:=by
      simpa only [Matrix.det_fin_two] using N.property
    rw [hN10] at hd
    linear_combination hd
  let b:CubicUnitResidue (p^(3-j)):=⟨Ideal.Quotient.mk _ (N 0 0),
    (isUnit_quotient_span_iff _ _).mpr hcop⟩
  refine ⟨⟨⟨j,by omega⟩,b⟩,?_⟩
  change Ideal.Quotient.mk (Ideal.span {p^3})
      (p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1)=r
  rw [←GaussianShiftedPartition.representative_spec (p^3) r]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1-a
  rw [ha,←mul_sub,hpow]
  exact mul_dvd_mul_left (p^j) (gaussRep_mk_congr (p^(3-j)) (N 0 0))
def cubeResidueStrataEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeResidueStrata p≃(Eis⧸Ideal.span {p^3}) :=
  Equiv.ofBijective (cubeResidueStratumMap p)
    ⟨cubeResidueStratumMap_injective p hp,cubeResidueStratumMap_surjective p hp hprimary⟩
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
def cubeStratumSymbol (p C:Eis) (j:Fin 4) (b:CubicUnitResidue (p^(3-j.val))) : ℂ :=
  eisEmbedding (symbol (GaussianShiftedPartition.representative (p^(3-j.val)) b.1*C) (p^(3-j.val)))
end CubicEisenstein
open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
end CubicKubota
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
lemma cube_affine_coefficient_unit (p C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)) := by
  obtain ⟨t,ht⟩:=(three_dvd_primary_sub_one p hprimary)
  have hp3:IsCoprime p (3:Eis):=by
    refine ⟨1,-t,?_⟩
    linear_combination ht
  apply (isUnit_quotient_span_iff _ _).mpr
  exact hp3.pow_left.mul_right hC.symm.pow_left
def cubeCuspAffineEquiv (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    (Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}) := by
  let a:=Ideal.Quotient.mk (Ideal.span {p^3}) A
  let u:Units (Eis⧸Ideal.span {p^3}):=(cube_affine_coefficient_unit p C hprimary hC).unit
  exact {
    toFun:=fun r=>a+(u:_) * r
    invFun:=fun r=>(↑u⁻¹:_)*(r-a)
    left_inv:=by
      intro r
      simp only [add_sub_cancel_left,←mul_assoc,Units.inv_mul,one_mul]
    right_inv:=by
      intro r
      simp only [←mul_assoc,Units.mul_inv,one_mul,add_sub_cancel] }
end CubicEisenstein
open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
structure CubeCuspData (A:SL(2,Eis)) (p q:Eis) where
  exponent : Fin 4
  matrix : SL(2,Eis)
  first : A 0 0+3*q*A 1 0=p^exponent.val*matrix 0 0
  second : p^3*A 1 0=p^exponent.val*matrix 1 0
  congruent : matrix*A⁻¹∈levelThree
def actualCubeCuspData (A:SL(2,Eis)) (p q:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeCuspData A p q := by
  let h:=cube_average_cusp_reduction A p q hp hprimary
  let j:=Classical.choose h
  have hj:j≤3:=(Classical.choose_spec h).1
  let N:=Classical.choose (Classical.choose_spec h).2
  have hN:=(Classical.choose_spec (Classical.choose_spec h).2)
  exact ⟨⟨j,by omega⟩,N,hN.1,hN.2.1,hN.2.2.1⟩
namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}
lemma lower_eq (d:CubeCuspData A p q) (hp:p≠0) :
    d.matrix 1 0=p^(3-d.exponent.val)*A 1 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d.exponent.val hp)
  rw [←d.second,←mul_assoc,←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
lemma unit_top (d:CubeCuspData A p q) (hp:p≠0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^(3-d.exponent.val)}) (d.matrix 0 0)) := by
  apply (isUnit_quotient_span_iff _ _).mpr
  refine ⟨-d.matrix 0 1*A 1 0,d.matrix 1 1,?_⟩
  have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
    simpa only [Matrix.det_fin_two] using d.matrix.property
  rw [d.lower_eq hp] at hd
  linear_combination hd
def stratum (d:CubeCuspData A p q) (hp:p≠0) : CubeResidueStrata p :=
  ⟨d.exponent,⟨Ideal.Quotient.mk _ (d.matrix 0 0),d.unit_top hp⟩⟩
end CubeCuspData
end CubicKubota
end
end OAI


