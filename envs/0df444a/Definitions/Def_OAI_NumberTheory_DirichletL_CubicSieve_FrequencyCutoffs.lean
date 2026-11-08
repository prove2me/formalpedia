-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:48:57.626807+00:00
-- url     : https://prove2.me/theorems/5ee3ef83-d3c3-4079-87b8-758b5ed8191f
-- title:
--   Frequency Cutoffs
-- statement:
--   Definitions and structural lemmas for Frequency Cutoffs, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FrequencyCutoffs.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalTruncation
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_CubicEisenstein_residue_lambda_prime
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_JointLogSeparation_halfNormalizationCLM_apply
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_PrimaryIdealUnitReindex_primaryGenerator_span_ne_zero_iff
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm primeProductNorm_pos)
open ConcreteTraceCRT (eisEmbedding)
def secondFrequencyCutoff (scale H : ℝ) : Finset O :=
  ShortDraftLatticeCount.rowNormBall ⌈H/scale⌉₊
end
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
def truncatedSecondZero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (K : Finset ι → Finset ι → Finset O) : ℂ :=
  (Y : ℂ) * paperRadialFourier W 0 *
    ∑ G ∈ F.powerset,
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) * star (H G) * H G *
      ∑ E : G.powerset, if 0 ∈ K G E.val then
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)
        else 0
end
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
def ramifiedIdeal : Ideal O := Ideal.span {lambda}
lemma ramifiedIdeal_prime : Prime ramifiedIdeal := by
  exact Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero)
    ((Ideal.span_singleton_prime residue_lambda_prime.ne_zero).mpr residue_lambda_prime)
lemma goodIdeal_iff_not_ramified (I : Ideal O) :
    primaryGenerator I ≠ 0 ↔ ¬ ramifiedIdeal ∣ I := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I,
    PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff,
    Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]
lemma prime_power_remainder_multiplicity {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] {p a : R} (hp : Prime p) (ha : ¬ p ∣ a) (n : ℕ) :
    multiplicity p (p^n*a)=n := by
  apply multiplicity_eq_of_dvd_of_not_dvd ⟨a,rfl⟩
  intro hd
  rw [pow_succ] at hd
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)).mp hd)
abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}
def lambdaFactorMap (p : ℕ × GoodIdeal) : NonzeroIdeal :=
  ⟨ramifiedIdeal^p.1*p.2.1,mul_ne_zero (pow_ne_zero _ ramifiedIdeal_prime.ne_zero)
    (primaryGenerator_ne_zero_ideal _ p.2.2)⟩
lemma lambdaFactorMap_bijective : Function.Bijective lambdaFactorMap := by
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh : ramifiedIdeal^n*I.1=ramifiedIdeal^m*J.1 := congrArg Subtype.val heq
    have hn : n=m := by
      have hm := congrArg (multiplicity ramifiedIdeal) hh
      rw [prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified I.1).mp I.2),
        prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified J.1).mp J.2)] at hm
      exact hm
    subst m
    have hIJ : I=J := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n ramifiedIdeal_prime.ne_zero) hh)
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩ := (FiniteMultiplicity.of_prime_left ramifiedIdeal_prime I.2).exists_eq_pow_mul_and_not_dvd
    refine ⟨(multiplicity ramifiedIdeal I.1,⟨J,(goodIdeal_iff_not_ramified J).mpr hnot⟩), ?_⟩
    exact Subtype.ext hJ.symm
def lambdaFactorEquiv : ℕ × GoodIdeal ≃ NonzeroIdeal :=
  Equiv.ofBijective lambdaFactorMap lambdaFactorMap_bijective
lemma ideal_pow_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun I : Ideal O => I^n) := by
  intro I J h
  dsimp only at h
  apply le_antisymm
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]
lemma lambdaFactor_generator_span (n : ℕ) (I : GoodIdeal) :
    Ideal.span {lambda^n*primaryGenerator I.1}=ramifiedIdeal^n*I.1 := by
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    (primaryGenerator_spec I.1 I.2).1]
  rfl
lemma three_dvd_lambda_sq : (3:O) ∣ lambda^2 := by
  have h := three_dvd_primary_sub_one (lambda^2+1) (show lambda^2 ∣ lambda^2+1-1 by simp)
  simpa only [add_sub_cancel_right] using h
lemma unit_cube_eq_sign (u : Oˣ) : (u:O)^3=1 ∨ (u:O)^3= -1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · left; simp [h]
  · right; norm_num [h]
  · left; simpa only [h,hη] using omega_primitive.pow_eq_one
  · right
    rw [h,Units.val_neg,hη]
    have hh := omega_primitive.pow_eq_one
    linear_combination -hh
  · left
    rw [h,Units.val_pow_eq_pow_val,hη,show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one]
    simp
  · right
    rw [h,Units.val_neg,Units.val_pow_eq_pow_val,hη]
    simp only [neg_pow,show (-1:O)^3= -1 by norm_num,
      show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one,one_pow,mul_one]
def cubeSign : Bool → O
  | false => 1
  | true => -1
lemma cubeSign_isUnit (b : Bool) : IsUnit (cubeSign b) := by
  cases b <;> simp [cubeSign]
lemma cubeSign_cube (b : Bool) : (cubeSign b)^3=cubeSign b := by
  cases b <;> norm_num [cubeSign]
lemma cubeSign_injective : Function.Injective cubeSign := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals norm_num [cubeSign] at h
def cubeBase (n : ℕ) (I : GoodIdeal) : O := lambda^(n+1)*primaryGenerator I.1
def cubeColumn (b : Bool) (n : ℕ) (I : GoodIdeal) : O := cubeSign b*(cubeBase n I)^3
lemma cubeBase_ne_zero (n : ℕ) (I : GoodIdeal) : cubeBase n I ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero) I.2
lemma cubeColumn_ne_zero (b : Bool) (n : ℕ) (I : GoodIdeal) : cubeColumn b n I ≠ 0 :=
  mul_ne_zero (cubeSign_isUnit b).ne_zero (pow_ne_zero 3 (cubeBase_ne_zero n I))
lemma cubeColumn_cube (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=(cubeSign b*cubeBase n I)^3 := by
  rw [mul_pow,cubeSign_cube]
  rfl
lemma cubeColumn_level (b : Bool) (n : ℕ) (I : GoodIdeal) : (3:O) ∣ cubeColumn b n I := by
  have h3 : (3:O) ∣ lambda^(3*(n+1)) := three_dvd_lambda_sq.trans (pow_dvd_pow lambda (by omega))
  have heq : cubeColumn b n I=cubeSign b*(lambda^(3*(n+1))*(primaryGenerator I.1)^3) := by
    simp only [cubeColumn,cubeBase,mul_pow,← pow_mul]
    congr 2
    ring
  rw [heq]
  exact (h3.mul_right _).mul_left _
lemma cubeColumn_span (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {cubeColumn b n I}=(ramifiedIdeal^(n+1)*I.1)^3 := by
  rw [cubeColumn,Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),
    ← Ideal.span_singleton_pow]
  change (Ideal.span {lambda^(n+1)*primaryGenerator I.1})^3=_
  rw [lambdaFactor_generator_span]
abbrev CubeLower := {c : LevelLower // c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3}
def cubeColumnMap (p : Bool × ℕ × GoodIdeal) : CubeLower :=
  ⟨⟨cubeColumn p.1 p.2.1 p.2.2,cubeColumn_level p.1 p.2.1 p.2.2⟩,
    cubeColumn_ne_zero p.1 p.2.1 p.2.2,⟨cubeSign p.1*cubeBase p.2.1 p.2.2,
      cubeColumn_cube p.1 p.2.1 p.2.2⟩⟩
lemma cubeColumnMap_injective : Function.Injective cubeColumnMap := by
  rintro ⟨b,n,I⟩ ⟨d,m,J⟩ h
  have hc : cubeColumn b n I=cubeColumn d m J := congrArg (fun c : CubeLower => c.1.1) h
  have hs := congrArg (fun a : O => Ideal.span {a}) hc
  rw [cubeColumn_span,cubeColumn_span] at hs
  have hr := ideal_pow_injective (by decide : (3:ℕ) ≠ 0) hs
  have hp : lambdaFactorMap (n+1,I)=lambdaFactorMap (m+1,J) := Subtype.ext hr
  have he := lambdaFactorMap_bijective.1 hp
  have hnm : n=m := Nat.succ.inj (congrArg Prod.fst he)
  have hIJ : I=J := congrArg Prod.snd he
  subst m; subst J
  have hbd : b=d := cubeSign_injective (mul_right_cancel₀
    (pow_ne_zero 3 (cubeBase_ne_zero n I)) hc)
  subst d
  rfl
lemma cubeColumnMap_surjective : Function.Surjective cubeColumnMap := by
  intro c
  obtain ⟨a,ha⟩ := c.2.2
  have ha0 : a ≠ 0 := by intro h; rw [h,zero_pow (by decide)] at ha; exact c.2.1 ha
  let A : NonzeroIdeal := ⟨Ideal.span {a},Ideal.span_singleton_eq_bot.not.mpr ha0⟩
  obtain ⟨⟨k,I⟩,hAI⟩ := lambdaFactorMap_bijective.2 A
  have hfact : ramifiedIdeal^k*I.1=Ideal.span {a} := congrArg Subtype.val hAI
  have hla : lambda ∣ a := by
    apply residue_lambda_prime.dvd_of_dvd_pow
    have hlam3 : lambda ∣ (3:O) :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
    rw [← ha]
    exact hlam3.trans c.1.2
  have hk : k ≠ 0 := by
    intro hk
    have hIeq : I.1=Ideal.span {a} := by simpa only [hk,pow_zero,one_mul] using hfact
    apply (goodIdeal_iff_not_ramified I.1).mp I.2
    rw [hIeq,Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]
    exact hla
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hspan : Ideal.span {cubeBase n I}=Ideal.span {a} :=
    (lambdaFactor_generator_span (n+1) I).trans hfact
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases unit_cube_eq_sign u with hu1 | hum1
  · refine ⟨(false,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn false n I=c.1.1
    rw [ha,← hu,mul_pow,hu1,mul_one]
    simp only [cubeColumn,cubeSign,one_mul]
  · refine ⟨(true,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn true n I=c.1.1
    rw [ha,← hu,mul_pow,hum1]
    simp only [cubeColumn,cubeSign]
    ring
def cubeColumnEquiv : Bool × ℕ × GoodIdeal ≃ CubeLower :=
  Equiv.ofBijective cubeColumnMap ⟨cubeColumnMap_injective,cubeColumnMap_surjective⟩
def ramifiedRatio (s : ℂ) : ℂ := (3:ℂ)^(3-3*s)
end CubicEisenstein
end
end OAI


