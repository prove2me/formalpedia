-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T16:23:32.852635+00:00
-- url     : https://prove2.me/theorems/de8e52bd-de1b-46d6-96f0-014d1d0f3eeb
-- title:
--   Ramified Gauss Series
-- statement:
--   Definitions and structural lemmas for Ramified Gauss Series, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedGaussSeries.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedGauss_embedding_lambda_ne_zero
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_coprime_of_dvd_sub_one
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
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_lambda_prime_actual
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
open scoped BigOperators Classical
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
lemma ramifiedElement_ne_zero (u : Eisˣ) (n : ℕ) : u.val*lambda^n≠0 := by
  have hl : lambda≠0:=by
    intro hh
    apply CompletedGauss.embedding_lambda_ne_zero
    rw [hh,map_zero]
  exact mul_ne_zero u.ne_zero (pow_ne_zero _ hl)
lemma ramifiedElement_level (u : Eisˣ) (n : ℕ) (hn : 2≤n) :
    (3:Eis)∣u.val*lambda^n :=
  dvd_mul_of_dvd_right (three_dvd_lambda_sq.trans (pow_dvd_pow lambda hn)) _
lemma ramified_denominator_condition (u : Eisˣ) (n : ℕ) (d : Eis)
    (hd : (3:Eis)∣d-1) : denominatorCondition (u.val*lambda^n) d := by
  have hu : IsCoprime u.val d:=⟨u.inv,0,by simp⟩
  have hl3 : lambda∣(3:Eis):=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  have hld : IsCoprime lambda d:=coprime_of_dvd_sub_one lambda d (hl3.trans hd)
  exact ⟨hu.mul_left hld.pow_left,hd⟩
lemma primary_add_nine (d w : Eis) (hd : (3:Eis)∣d-1) :
    (3:Eis)∣d+9*w-1 := by
  convert dvd_add hd (show (3:Eis)∣9*w from ⟨3*w,by ring⟩) using 1 ; ring
def ramifiedResidueAdd (u : Eisˣ) (n : ℕ) (w : Eis)
    (r : AdmissibleResidue (u.val*lambda^n)) : AdmissibleResidue (u.val*lambda^n) :=
  let c:=u.val*lambda^n
  let d:=denominatorRep c r.1+9*w
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) d,
    (denominatorCondition_congr c _ d (denominatorRep_mk_congr c d)).mpr
      (ramified_denominator_condition u n d (primary_add_nine _ _ r.2.2))⟩
lemma ramifiedResidueAdd_injective (u : Eisˣ) (n : ℕ) (w : Eis) :
    Function.Injective (ramifiedResidueAdd u n w) := by
  intro r q heq
  have hh:=congrArg Subtype.val heq
  change Ideal.Quotient.mk (Ideal.span {3*(u.val*lambda^n)}) (denominatorRep _ r.1+9*w)=
    Ideal.Quotient.mk (Ideal.span {3*(u.val*lambda^n)}) (denominatorRep _ q.1+9*w) at hh
  simp only [map_add,denominatorRep_spec] at hh
  exact Subtype.ext (add_right_cancel hh)
def ramifiedResidueAddEquiv (u : Eisˣ) (n : ℕ) (w : Eis) :
    AdmissibleResidue (u.val*lambda^n) ≃ AdmissibleResidue (u.val*lambda^n) := by
  letI : Finite (AdmissibleResidue (u.val*lambda^n)):=
    finite_admissibleResidue _ (ramifiedElement_ne_zero u n)
  exact Equiv.ofBijective (ramifiedResidueAdd u n w)
    ⟨ramifiedResidueAdd_injective u n w,
      Finite.surjective_of_injective (ramifiedResidueAdd_injective u n w)⟩
end
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedFrequencyBound (h : Eis) : ℕ:=Nat.log 3 (9*Ideal.absNorm (Ideal.span {h}))
end
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O
abbrev NonzeroLevelLower := {c : LevelLower // c.1≠0}
def ramifiedLower (u : Eisˣ) (n : ℕ) (I : GoodIdeal) : Eis :=
  (u.val*lambda^(n+2))*primaryGenerator I.1
lemma ramifiedLower_ne_zero (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    ramifiedLower u n I≠0:=mul_ne_zero (ramifiedElement_ne_zero u (n+2)) I.2
lemma ramifiedLower_level (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    (3:Eis)∣ramifiedLower u n I:=
  dvd_mul_of_dvd_left (ramifiedElement_level u (n+2) (by omega)) _
lemma ramifiedLower_span (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {ramifiedLower u n I}=ramifiedIdeal^(n+2)*I.1 := by
  unfold ramifiedLower
  rw [mul_assoc,Ideal.span_singleton_mul_left_unit u.isUnit,lambdaFactor_generator_span]
def ramifiedLowerMap (p : Eisˣ × ℕ × GoodIdeal) : NonzeroLevelLower:=
  ⟨⟨ramifiedLower p.1 p.2.1 p.2.2,ramifiedLower_level _ _ _⟩,ramifiedLower_ne_zero _ _ _⟩
lemma ramifiedLowerMap_injective : Function.Injective ramifiedLowerMap := by
  rintro ⟨u,n,I⟩ ⟨v,m,J⟩ h
  have hc : ramifiedLower u n I=ramifiedLower v m J:=congrArg (fun c:NonzeroLevelLower=>c.1.1) h
  have hs:=congrArg (fun x:Eis=>Ideal.span {x}) hc
  rw [ramifiedLower_span,ramifiedLower_span] at hs
  have hh:lambdaFactorMap (n+2,I)=lambdaFactorMap (m+2,J):=Subtype.ext hs
  have he:=lambdaFactorMap_bijective.1 hh
  have hnm:n=m:=by have ht:=congrArg Prod.fst he; omega
  have hIJ:I=J:=congrArg Prod.snd he
  subst m
  subst J
  have huv:u=v:=by
    apply Units.ext
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero) I.2)
    simpa only [ramifiedLower,mul_assoc] using hc
  subst v
  rfl
lemma ramifiedLowerMap_surjective : Function.Surjective ramifiedLowerMap := by
  intro c
  let C:NonzeroIdeal:=⟨Ideal.span {c.1.1},Ideal.span_singleton_eq_bot.not.mpr c.2⟩
  obtain ⟨⟨k,I⟩,hCI⟩:=lambdaFactorMap_bijective.2 C
  have hfact:ramifiedIdeal^k*I.1=Ideal.span {c.1.1}:=congrArg Subtype.val hCI
  have hp2:ramifiedIdeal^2∣ramifiedIdeal^k*I.1:=by
    rw [hfact]
    change (Ideal.span {lambda}:Ideal Eis)^2∣_
    rw [Ideal.span_singleton_pow,Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton]
    exact lambda_sq_dvd_three.trans c.1.2
  have hk:2≤k:=by
    by_contra hh
    have hcases:k=0∨k=1:=by omega
    have hnot:=((goodIdeal_iff_not_ramified I.1).mp I.2)
    rcases hcases with rfl|rfl
    · simp only [pow_zero,one_mul] at hp2
      exact hnot ((dvd_pow_self ramifiedIdeal (by decide : (2:ℕ)≠0)).trans hp2)
    · rw [pow_one,pow_two] at hp2
      exact hnot ((mul_dvd_mul_iff_left ramifiedIdeal_prime.ne_zero).mp hp2)
  obtain ⟨n,hn⟩:=Nat.exists_eq_add_of_le hk
  have hk':k=n+2:=by omega
  subst k
  have hspan : Ideal.span {lambda^(n+2)*primaryGenerator I.1}=Ideal.span {c.1.1}:=
    (lambdaFactor_generator_span (n+2) I).trans (by simpa only [Nat.add_comm] using hfact)
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨(u,n,I),Subtype.ext (Subtype.ext ?_)⟩
  change ramifiedLower u n I=c.1.1
  simpa only [ramifiedLower,mul_assoc,mul_comm,mul_left_comm] using hu
def ramifiedLowerEquiv : Eisˣ × ℕ × GoodIdeal ≃ NonzeroLevelLower:=
  Equiv.ofBijective ramifiedLowerMap ⟨ramifiedLowerMap_injective,ramifiedLowerMap_surjective⟩
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O
def unramifiedCubicGaussSeries (s : ℂ) (h : Eis) : ℂ:=
  ∑'I:GoodIdeal,(Ideal.absNorm I.1:ℂ)^(-s)*cubicUnitGaussSum h (primaryGenerator I.1)
end
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O
end CubicEisenstein
end
end OAI


