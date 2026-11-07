-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayCoefficients
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_RayCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:44:50.190476+00:00
-- url     : https://prove2.me/theorems/c1d3e4b4-a471-4c9c-b6ec-55f811410d22
-- title:
--   Ray Coefficients
-- statement:
--   Definitions and structural lemmas for Ray Coefficients, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RayCoefficients.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_primary_unit_eq_one
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicJacobiGlobal_primary_ne_zero
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_denominator_congr
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_denominator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_neg_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_reciprocity
import Theorems.Thm_OAI_CubicRamified_cubicValue_ne_zero
import Theorems.Thm_OAI_CubicRamified_exists_primaryCoord
import Theorems.Thm_OAI_CubicRamified_primaryCoord_eq
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
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_RayFourExpansion_rayCharacter_mul
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
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


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
open scoped BigOperators Classical
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open MixedCrossSeparation (columnG columnPrimeCoprime quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)
def rayMonoid (χ : RayCharacter) : O →* ℂ where
  toFun := rayCharacter χ
  map_one' := by simp [rayCharacter]
  map_mul' := RayFourExpansion.rayCharacter_mul χ
def conjugateRayMonoid (χ : RayCharacter) : O →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp (rayMonoid χ)
@[simp] theorem rayMonoid_apply (χ : RayCharacter) (a : O) :
    rayMonoid χ a = rayCharacter χ a := rfl
@[simp] theorem conjugateRayMonoid_apply (χ : RayCharacter) (a : O) :
    conjugateRayMonoid χ a = star (rayCharacter χ a) := rfl
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def secondInputCoefficient (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * H S
end
section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)
abbrev SecondRayIndex := (RayCharacter × RayCharacter) × (RayCharacter × RayCharacter)
def secondRayCoefficient (r : SecondRayIndex) : ℂ :=
  crossCoeff r.2.1 r.2.2 * gCoeff r.1.2 * star (gCoeff r.1.1)
def secondRayMinus (Ψ : O →* ℂ) (r : SecondRayIndex) : O →* ℂ :=
  conjugateRayMonoid r.2.2 * (conjugateRayMonoid r.1.2 * Ψ)
def secondRayPlus (Ψ : O →* ℂ) (r : SecondRayIndex) : O →* ℂ :=
  rayMonoid r.2.1 * (conjugateRayMonoid r.1.1 * Ψ)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def secondActualPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S *
      secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
    (supportMobius (fun i => Ideal.span {p i}) T *
      secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k else 0
def secondTotalWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (z : SecondRayIndex × Finset ι) : ℂ :=
  secondRayCoefficient z.1 *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ₁ z.1) (secondRayPlus Ψ₂ z.1)
      m r c d e k (-k) z.2
def secondTotalEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) : ℝ :=
  ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V)‖ *
      ‖secondChildSum p hp hcop hg F V
        (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
        m r c d e (if negative then k else -k) H‖ ^ 2
end
open ActualEisensteinCubic
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end SecondPassArithmetic
namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified
theorem symbol_ne_zero_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ≠ 0 := by
  classical
  have ha0 := primary_ne_zero a ha
  have hI0 : (Ideal.span {a} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr ha0
  rw [symbol, idealSymbol, if_neg hI0]
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨P,hP,hzero⟩ := Multiset.mem_map.mp hzero
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
  have haP : a ∈ P := hle (Ideal.subset_span (by simp))
  have hg := primary_maximal_divisor_good a ha P haP
  have hxP : x ∉ P := by
    intro hxP
    obtain ⟨r,s,hrs⟩ := hcop
    have hmem := P.add_mem (P.mul_mem_left r hxP) (P.mul_mem_left s haP)
    rw [hrs] at hmem
    exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
      ((Ideal.eq_top_iff_one P).mpr hmem)
  rw [primeValue_eq P hg] at hzero
  exact cubicValue_ne_zero P hg x hxP hzero
theorem primary_mul (a b : O) (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) :
    lambda ^ 2 ∣ a*b-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left ha b) hb
  convert h using 1 ; ring
theorem primary_add_multiple_three (a c t : O) (ha : lambda ^ 2 ∣ a-1) :
    lambda ^ 2 ∣ (a+3*t*c)-1 := by
  have h := dvd_add ha (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left lambda_sq_dvd_three t) c)
  convert h using 1 ; ring
theorem kubota_mul_of_isCoprime (a b c d e g : O)
    (hdet : a*d-b*c=1) (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hg : (3 : O) ∣ g) (hag : IsCoprime a g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  let productA := a*e+b*g
  let productC := c*e+d*g
  have hA : lambda ^ 2 ∣ productA-1 := by
    have h := dvd_add (primary_mul a e ha he)
      (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans hb) g)
    convert h using 1 ; dsimp [productA] ; ring
  have hrelation : a*productC-c*productA=g := by
    dsimp [productA,productC]
    linear_combination g*hdet
  have hcop : IsCoprime a productA := by
    obtain ⟨r,s,hrs⟩ := hag
    refine ⟨r+s*productC,-s*c,?_⟩
    linear_combination hrs + s*hrelation
  have hnonzero := symbol_ne_zero_of_isCoprime a productA hA hcop
  have h1 : symbol a productA * symbol productC productA = symbol g productA := by
    rw [← symbol_mul_numerator _ _ productA hA]
    exact symbol_congr ⟨c, by linear_combination hrelation⟩
  have h2 : symbol a productA * symbol c a = symbol g a := by
    rw [symbol_reciprocity a productA (primary_ne_zero a ha) (primary_ne_zero productA hA) ha hA,
      ← symbol_mul_numerator _ _ a ha]
    calc
      symbol (productA*c) a = symbol (-g) a := by
        apply symbol_congr
        refine ⟨productC,?_⟩
        linear_combination -hrelation
      _ = symbol g a := symbol_neg_numerator g a ha
  have h3 : symbol g productA = symbol g a * symbol g e := by
    rw [← symbol_mul_denominator]
    apply symbol_denominator_congr g productA (a*e) hA (primary_mul a e ha he)
    · obtain ⟨b0,hb0⟩ := hb
      obtain ⟨g0,hg0⟩ := hg
      refine ⟨b0*g0,?_⟩
      dsimp [productA]
      rw [hb0,hg0]
      ring
    · exact ⟨b,by dsimp [productA];ring⟩
  change symbol productC productA = _
  apply mul_left_cancel₀ hnonzero
  rw [h1,h3,← h2]
  ring
lemma three_dvd_primary_sub_one (a : O) (ha : lambda ^ 2 ∣ a-1) : (3 : O) ∣ a-1 := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  rw [primaryCoord_eq]
  exact ⟨(A : O)+(B : O)*omega,by ring⟩
theorem exists_coprime_three_shift (a c g : O)
    (ha : lambda ^ 2 ∣ a-1) (hac : IsCoprime a c) (hg0 : g ≠ 0) :
    ∃ t : O, IsCoprime (a+3*t*c) g := by
  classical
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (UniqueFactorizationMonoid.normalizedFactors g).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, ?_⟩
  apply IsCoprime.symm
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hg0 h)
  intro p hp hpg hpnew
  by_cases hpa : p ∣ a
  · have hp3 : ¬p ∣ (3 : O) := by
      intro h3
      have hsub : p ∣ a-1 := h3.trans (three_dvd_primary_sub_one a ha)
      have hone : p ∣ (1 : O) := by
        convert dvd_sub hpa hsub using 1 ; ring
      exact hp.not_dvd_one hone
    have hpc : ¬p ∣ c := by
      intro hpc
      exact hp.not_isUnit (hac.isUnit_of_dvd' hpa hpc)
    have hps : ¬p ∣ s.prod := by
      intro hdiv
      obtain ⟨q,hqs,hpq⟩ := hp.exists_mem_multiset_dvd hdiv
      have hqs' : q ∈ UniqueFactorizationMonoid.normalizedFactors g ∧ ¬q ∣ a :=
        Multiset.mem_filter.mp hqs
      have hqprime := UniqueFactorizationMonoid.prime_of_normalized_factor q hqs'.1
      have hqp : q ∣ p := (hp.associated_of_dvd hqprime hpq).dvd'
      exact hqs'.2 (hqp.trans hpa)
    have hpterm : p ∣ 3*s.prod*c := by
      convert dvd_sub hpnew hpa using 1 ; ring
    rcases hp.dvd_or_dvd hpterm with hleft | hright
    · rcases hp.dvd_or_dvd hleft with h3 | hs
      · exact hp3 h3
      · exact hps hs
    · exact hpc hright
  · obtain ⟨q,hq,hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hg0 hp.irreducible hpg
    have hqa : ¬q ∣ a := fun hqa => hpa (hpq.dvd.trans hqa)
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,hqa⟩
    have hps : p ∣ s.prod := hpq.dvd.trans (Multiset.dvd_prod hqs)
    have hpterm : p ∣ 3*s.prod*c :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hps 3) c
    have hpa' : p ∣ a := by
      convert dvd_sub hpnew hpterm using 1 ; ring
    exact hpa hpa'
lemma symbol_three_shift (c a t : O) (ha : lambda ^ 2 ∣ a-1) (hc : (3 : O) ∣ c) :
    symbol c (a+3*t*c) = symbol c a := by
  apply symbol_denominator_congr c (a+3*t*c) a (primary_add_multiple_three a c t ha) ha
  · obtain ⟨c0,hc0⟩ := hc
    refine ⟨t*c0,?_⟩
    rw [hc0]
    ring
  · exact ⟨3*t,by ring⟩
theorem kubota_mul (a b c d e f g h : O)
    (hdet : a*d-b*c=1) (hdet' : e*h-f*g=1)
    (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ c) (hg : (3 : O) ∣ g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  by_cases hg0 : g = 0
  · have heh : e*h=1 := by simpa only [hg0,mul_zero,sub_zero] using hdet'
    have he1 : e=1 := A3_primary_unit_eq_one e (IsUnit.of_mul_eq_one h heh) he
    simp only [hg0,he1,mul_one,mul_zero,add_zero,symbol_one]
  have hac : IsCoprime a c := by
    refine ⟨d,-b,?_⟩
    linear_combination hdet
  obtain ⟨t,ht⟩ := exists_coprime_three_shift a c g ha hac hg0
  have hdetShift : (a+3*t*c)*d-(b+3*t*d)*c=1 := by linear_combination hdet
  have hbShift : (3 : O) ∣ b+3*t*d :=
    dvd_add hb (dvd_mul_of_dvd_left (dvd_mul_right 3 t) d)
  have hcalc := kubota_mul_of_isCoprime (a+3*t*c) (b+3*t*d) c d e g
    hdetShift (primary_add_multiple_three a c t ha) he hbShift hg ht
  have hC : (3 : O) ∣ c*e+d*g :=
    dvd_add (dvd_mul_of_dvd_left hc e) (dvd_mul_of_dvd_right hg d)
  have hA : lambda ^ 2 ∣ (a*e+b*g)-1 := by
    have hh := dvd_add (primary_mul a e ha he)
      (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans hb) g)
    convert hh using 1 ; ring
  calc
    symbol (c*e+d*g) (a*e+b*g) =
        symbol (c*e+d*g) ((a*e+b*g)+3*t*(c*e+d*g)) :=
      (symbol_three_shift _ _ _ hA hC).symm
    _ = symbol c (a+3*t*c) * symbol g e := by
      convert hcalc using 1 ; congr 1 ; ring
    _ = symbol c a * symbol g e := by rw [symbol_three_shift c a t ha hc]
end CubicJacobiGlobal
open scoped BigOperators Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified
end CubicJacobiGlobal
namespace CubicKubota
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified
def levelThree : Subgroup (SL(2, O)) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)}))).ker
lemma levelThree_entry (M : levelThree) (i j : Fin 2) :
    (3 : O) ∣ (M : SL(2,O)) i j - (if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3 : O)})) (M : SL(2,O)) = 1 := M.property
  have h := congrArg (fun N : SL(2, O ⧸ (Ideal.span {(3 : O)})) => N i j) hm
  change (Ideal.Quotient.mk (Ideal.span {(3 : O)})) ((M : SL(2,O)) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ (Ideal.span {(3 : O)}))) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h
lemma levelThree_primary (M : levelThree) :
    lambda ^ 2 ∣ (M : SL(2,O)) 0 0 - 1 := by
  exact lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 0 0)
lemma levelThree_upper (M : levelThree) : (3 : O) ∣ (M : SL(2,O)) 0 1 := by
  simpa using levelThree_entry M 0 1
lemma levelThree_lower (M : levelThree) : (3 : O) ∣ (M : SL(2,O)) 1 0 := by
  simpa using levelThree_entry M 1 0
def value (M : levelThree) : O :=
  symbol ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 0 0)
theorem value_mul (M N : levelThree) : value (M*N) = value M * value N := by
  have hM : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  have hN : (N : SL(2,O)) 0 0 * (N : SL(2,O)) 1 1 -
      (N : SL(2,O)) 0 1 * (N : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (N : SL(2,O)).property
  have hh := kubota_mul ((M : SL(2,O)) 0 0) ((M : SL(2,O)) 0 1)
    ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 1 1)
    ((N : SL(2,O)) 0 0) ((N : SL(2,O)) 0 1)
    ((N : SL(2,O)) 1 0) ((N : SL(2,O)) 1 1) hM hN
    (levelThree_primary M) (levelThree_primary N)
    (levelThree_upper M) (levelThree_lower M) (levelThree_lower N)
  change symbol (((M : SL(2,O)) * (N : SL(2,O))) 1 0)
    (((M : SL(2,O)) * (N : SL(2,O))) 0 0) = _
  simpa only [value, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using hh
@[simp] theorem value_one : value 1 = 1 := by
  change symbol (0 : O) 1 = 1
  exact symbol_one 0
def character : levelThree →* O where
  toFun := value
  map_one' := value_one
  map_mul' := value_mul
def complexCharacter : levelThree →* ℂ :=
  ConcreteTraceCRT.eisEmbedding.toMonoidHom.comp character
end CubicKubota
end
end OAI


