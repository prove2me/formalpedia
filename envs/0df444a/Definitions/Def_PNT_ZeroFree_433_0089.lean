-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0089
-- name    : PNT_ZeroFree_433_0089
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:56:26.202568+00:00
-- url     : https://prove2.me/theorems/5afe1923-7fa3-4244-9060-df493e049c34
-- title:
--   Zero-free region foundations: Eisenstein.ConstantTermSupport [0089]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ConstantTermSupport.lean#L80-L622

import Definitions.Def_PNT_ZeroFree_433_0088

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ConstantTermSupport.lean#L80-L622
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
section
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

namespace CubicEisenstein
open MeasureTheory Set Filter
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid

lemma multiset_cube_remainder {α : Type*} [DecidableEq α] (s : Multiset α) (p : α)
    (hdiv : ∀ q, q ≠ p → 3 ∣ s.count q) :
    ∃ t : Multiset α, s=(s.count p % 3) • {p} + 3 • t := by
  let t := Finsupp.toMultiset (s.toFinsupp.mapRange (fun n : ℕ => n/3) (by decide))
  refine ⟨t,?_⟩
  apply Multiset.ext.mpr
  intro q
  simp only [Multiset.count_add,Multiset.count_nsmul,Multiset.count_singleton,
    t,Finsupp.count_toMultiset,Finsupp.mapRange_apply,Multiset.toFinsupp_apply]
  by_cases hq : q=p
  · subst q
    simp only [ite_true,mul_one]
    omega
  · simp only [hq,ite_false,mul_zero,zero_add]
    exact (Nat.mul_div_cancel' (hdiv q hq)).symm

lemma residue_lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

lemma constant_coefficient_unramified_count [NormalizationMonoid O]
    (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0)
    (q : O) (hq : q ≠ normalize lambda) : 3 ∣ (normalizedFactors c).count q := by
  by_cases hmem : q ∈ normalizedFactors c
  · have hprime := prime_of_normalized_factor q hmem
    let P : Ideal O := Ideal.span {q}
    let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
    have hg : lambda ∉ P := by
      intro hl
      have ha : Associated q lambda :=
        hprime.associated_of_dvd residue_lambda_prime (Ideal.mem_span_singleton.mp hl)
      apply hq
      exact (normalize_normalized_factor q hmem).symm.trans
        (normalize_eq_normalize_iff_associated.mpr ha)
    obtain ⟨p,hP,hprimary,-⟩ := cubicJacobi_exists_primary_generator P hg
    have hqp : Associated q p := Ideal.span_singleton_eq_span_singleton.mp hP
    have hp : Prime p := hqp.prime_iff.mp hprime
    obtain ⟨b,hfactor,hpb⟩ := (FiniteMultiplicity.of_prime_left hp hc).exists_eq_pow_mul_and_not_dvd
    have hd := constant_coefficient_primary_prime_exponent c p b (multiplicity p c)
      hc hlevel hp hprimary hpb hfactor hA
    have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hc
    rw [normalize_normalized_factor q hmem] at hcount
    rw [← hcount,← multiplicity_eq_of_associated_left hqp]
    exact hd
  · rw [Multiset.count_eq_zero.mpr hmem]
    exact dvd_zero _

theorem constant_coefficient_cube_reduction (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∃ (u : Oˣ) (r : ℕ) (a : O), r < 3 ∧ c=(u:O)*lambda^r*a^3 := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := normalizedFactors c
  obtain ⟨t,ht⟩ := multiset_cube_remainder s (normalize lambda)
    (constant_coefficient_unramified_count c hc hlevel hA)
  let r := s.count (normalize lambda) % 3
  have hprod : s.prod=(normalize lambda)^r*t.prod^3 := by
    rw [ht,Multiset.prod_add,Multiset.prod_nsmul,Multiset.prod_singleton,Multiset.prod_nsmul]
  have hassoc : Associated (lambda^r*t.prod^3) c := by
    have hnorm : Associated ((normalize lambda)^r*t.prod^3) (lambda^r*t.prod^3) :=
      (normalize_associated lambda).pow_pow.mul_right _
    apply hnorm.symm.trans
    rw [← hprod]
    exact prod_normalizedFactors hc
  obtain ⟨u,hu⟩ := hassoc
  refine ⟨u,r,t.prod,Nat.mod_lt _ (by decide),?_⟩
  rw [← hu]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified

lemma constant_coefficient_ramified_equation (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (hA : arithmeticResidueSum 0 c ≠ 0) (u : Oˣ) (r : ℕ) (a : O) (ha : a ≠ 0)
    (hfactor : c=(u:O)*lambda^r*a^3) (A B : ℤ) :
    symbol (u:O) (primaryCoord A B)*(cubicExp A)^r=1 := by
  let t0 := primaryCoord A B
  have ht0 : lambda^2 ∣ t0-1 := primaryCoord_primary A B
  obtain ⟨w,hw⟩ := exists_coprime_three_shift t0 3 a ht0 (primary_coprime_three t0 ht0) ha
  let t := t0+3*w*3
  have ht : lambda^2 ∣ t-1 := primary_add_multiple_three t0 3 w ht0
  have h9 : (9:O) ∣ t-t0 := ⟨w,by dsimp [t]; ring⟩
  have hat : IsCoprime a t := hw.symm
  have hlt : IsCoprime lambda t :=
    coprime_of_dvd_sub_one lambda t ((show lambda ∣ lambda^2 from ⟨lambda,by ring⟩).trans ht)
  have hct : IsCoprime c t := by
    rw [hfactor,show (u:O)*lambda^r*a^3=(u:O)*(lambda^r*a^3) by ring]
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    exact hlt.pow_left.mul_left hat.pow_left
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t
    ⟨hct,three_dvd_primary_sub_one t ht⟩
  have hacube : symbol (a^3) t=1 := by
    rw [symbol_pow_numerator a t ht 3]
    exact symbol_cube_of_isCoprime a t ht hat
  rw [hfactor,symbol_mul_numerator _ _ t ht,symbol_mul_numerator _ _ t ht,
    symbol_pow_numerator lambda t ht r,hacube,mul_one,
    symbol_unit_congr_mod_nine (u:O) t t0 u.isUnit ht ht0 h9,
    symbol_lambda_congr_mod_nine t t0 ht ht0 h9,
    symbol_lambda_eq_linearRay t0 ht0] at htriv
  simpa only [t0,linearRay_primaryCoord,one_mul,zero_mul,add_zero] using htriv

lemma unit_eq_sign_of_symbol_class (u : Oˣ)
    (hu : symbol (u:O) (primaryCoord 0 1)=1) : (u:O)=1 ∨ (u:O)=-1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega (primaryCoord 0 1)=omega^2 := by
    rw [symbol_omega_eq_linearRay _ (primaryCoord_primary 0 1),linearRay_primaryCoord]
    norm_num [cubicExp] <;> congr 1 <;> decide
  have hω2 : symbol (omega^2) (primaryCoord 0 1)=omega^4 := by
    rw [symbol_pow_numerator omega _ (primaryCoord_primary 0 1) 2,hω,← pow_mul]
  have hn2 : omega^2 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 2).not.mpr (by decide)
  have hn4 : omega^4 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 4).not.mpr (by decide)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · exact Or.inl (by rw [h,Units.val_one])
  · exact Or.inr (by rw [h,Units.val_neg,Units.val_one])
  · exact False.elim (hn2 (by simpa only [h,hη,hω] using hu))
  · exact False.elim (hn2 (by simpa only [h,Units.val_neg,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_pow_eq_pow_val,hη,hω2] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω2] using hu))

theorem arithmeticResidueSum_ne_zero_implies_cube (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) : ∃ a : O,c=a^3 := by
  obtain ⟨u,r,a,hr,hfactor⟩ := constant_coefficient_cube_reduction c hc hlevel hA
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : (3:ℕ) ≠ 0),mul_zero] at hfactor
    exact hc hfactor
  have h01 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 0 1
  have husign := unit_eq_sign_of_symbol_class u (by
    simpa only [cubicExp_zero,one_pow,mul_one] using h01)
  have h10 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 1 0
  have hωr : omega^r=1 := by
    rcases husign with hu | hu
    · simpa only [hu,symbol_one_numerator _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
    · simpa only [hu,symbol_neg_one _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
  have hdiv : 3 ∣ r := (omega_primitive.pow_eq_one_iff_dvd r).mp hωr
  have hr0 : r=0 := by omega
  rw [hr0,pow_zero,mul_one] at hfactor
  rcases husign with hu | hu
  · refine ⟨a,?_⟩
    simpa only [hu,one_mul] using hfactor
  · refine ⟨-a,?_⟩
    rw [hfactor,hu]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

theorem arithmeticResidueSum_ne_zero_iff_cube (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c ≠ 0 ↔ ∃ a : O,c=a^3 := by
  constructor
  · exact arithmeticResidueSum_ne_zero_implies_cube c hc hlevel
  · rintro ⟨a,rfl⟩
    have ha : a ≠ 0 := fun h => hc (by rw [h]; norm_num)
    exact arithmeticResidueSum_cube_ne_zero a ha

theorem arithmeticResidueSum_constant_formula (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c=
      if ∃ a : O,c=a^3 then (Nat.card (AdmissibleResidue c):ℂ) else 0 := by
  split_ifs with hcube
  · obtain ⟨a,rfl⟩ := hcube
    exact arithmeticResidueSum_cube a (fun h => hc (by rw [h]; norm_num))
  · exact not_ne_iff.mp (fun hA => hcube (arithmeticResidueSum_ne_zero_implies_cube c hc hlevel hA))

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

def idealZeroMask (D : Ideal O) (z : O) : ℂ :=
  if ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P then 0 else 1

theorem idealSupport_singleton_univ (D : Ideal O) :
    idealSupport {D} D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro P
  apply (mem_idealSupport_iff {D} D P).mpr
  obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
  have hID : I = D := Finset.mem_singleton.mp hI
  simpa only [hID] using hP

theorem singleton_rowCoprimeMask_eq_idealZeroMask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : primePool {D} => P.val) Finset.univ z = idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (primePool {D})), z ∈ P.val) ↔
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
      have hID : I = D := Finset.mem_singleton.mp hI
      exact ⟨P.val, hID ▸ hP, hz⟩
    · rintro ⟨P, hP, hz⟩
      have hp : P ∈ primePool {D} := mem_primePool_iff.mpr ⟨D, Finset.mem_singleton_self D, hP⟩
      exact ⟨⟨P, hp⟩, Finset.mem_univ _, hz⟩
  simp only [rowCoprimeMask, idealZeroMask, he]

theorem canonical_quadraticRow_star (D : Ideal O) (hD : Admissible D) (z : O) :
    star (quadraticRow D z) = quadraticRow D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticInitialBound.quadraticRow_star _ _ _ _

theorem canonical_quadraticRow_squared (D : Ideal O) (hD : Admissible D) (z : O) :
    quadraticRow D z * quadraticRow D z = idealZeroMask D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  rw [← QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ z z, ← pow_two,
    QuadraticSquarefreeKernel.quadraticRow_square, idealSupport_singleton_univ]
  exact singleton_rowCoprimeMask_eq_idealZeroMask D z

def gcdMaskPrimes (D : Ideal O) : Finset (Ideal O) :=
  {Ideal.span {lambda}, Ideal.span {(2 : O)}} ∪
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset

instance gcdMaskPrimes_maximal (D : Ideal O) (P : gcdMaskPrimes D) : P.val.IsMaximal := by
  rcases Finset.mem_union.mp P.property with hp | hp
  · rcases Finset.mem_insert.mp hp with hp | hp
    · rw [hp]
      exact lambdaIdeal_maximal
    · rw [Finset.mem_singleton.mp hp]
      exact twoIdeal_maximal
  · have h := UniqueFactorizationMonoid.prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp hp)
    exact (Ideal.isPrime_of_prime h).isMaximal h.ne_zero

theorem gcdMaskPrimes_mask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z =
      rowCoprimeMask badPrime Finset.univ z * idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val) ↔
      (lambda ∣ z ∨ (2 : O) ∣ z) ∨
        ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      rcases Finset.mem_union.mp P.property with hp | hp
      · rcases Finset.mem_insert.mp hp with hp | hp
        · exact Or.inl (Or.inl (Ideal.mem_span_singleton.mp (hp ▸ hz)))
        · exact Or.inl (Or.inr (Ideal.mem_span_singleton.mp ((Finset.mem_singleton.mp hp) ▸ hz)))
      · exact Or.inr ⟨P.val, Multiset.mem_toFinset.mp hp, hz⟩
    · rintro ((hz | hz) | ⟨P, hP, hz⟩)
      · exact ⟨⟨Ideal.span {lambda}, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨Ideal.span {(2 : O)}, Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨P, Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hP)⟩, Finset.mem_univ _, hz⟩
  change (if ∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val then (0 : ℂ) else 1) = _
  simp only [he]
  rw [badPrime_mask, supported_span_iff]
  unfold idealZeroMask
  by_cases hl : lambda ∣ z <;> by_cases ht : (2 : O) ∣ z <;>
    by_cases hd : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P <;> simp [hl, ht, hd]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance

theorem canonical_same_ray_pair_poisson
    {α : Type*} [DecidableEq α]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hd : Disjoint A B := idealSupport_disjoint_of_coprime F I J hcop
  have hpgI : primaryGenerator I = ∏ i ∈ A, p i := primaryGenerator_eq_poolProduct F hF I hIF
  have hpgJ : primaryGenerator J = ∏ i ∈ B, p i := primaryGenerator_eq_poolProduct F hF J hJF
  have hr : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i) := by
    rw [← hpgI, ← hpgJ]
    exact hray
  have hn : (∏ i ∈ A ∪ B, p i) = primaryGenerator I * primaryGenerator J := by
    rw [Finset.prod_union hd, ← hpgI, ← hpgJ]
  have hrowI (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) A z = quadraticRow I z :=
    (quadraticRow_eq_primaryPool F hF I hIF z).symm
  have hrowJ (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) B z = quadraticRow J z :=
    (quadraticRow_eq_primaryPool F hF J hJF z).symm
  have ht := same_ray_quadratic_pair_poisson R hinj S p (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    A B hd hr W M hM
  simpa only [hn, hrowI, hrowJ] using ht

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance PrimaryIdealUnitReindex

theorem canonical_pair_unit_invariant (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (u : Oˣ) (z : O) :
    quadraticRow I (u.val * z) * quadraticRow J (u.val * z) =
      quadraticRow I z * quadraticRow J z := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hcA : Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hcB : Pairwise (Function.onFun IsCoprime (fun i : B => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hr : residue (∏ i : A, p i.val) = residue (∏ i : B, p i.val) := by
    rw [Finset.prod_coe_sort, Finset.prod_coe_sort,
      ← primaryGenerator_eq_poolProduct F hF I hIF, ← primaryGenerator_eq_poolProduct F hF J hJF]
    exact hray
  have h := quadratic_pair_unit_invariant
    (fun i : A => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcA
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i : B => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcB
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val) hr u z
  have hrowI (w : O) : finiteSexticRow (fun i : A => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow I w :=
    (quadraticRow_eq_primarySubset F hF I hIF w).symm
  have hrowJ (w : O) : finiteSexticRow (fun i : B => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow J w :=
    (quadraticRow_eq_primarySubset F hF J hJF w).symm
  simpa only [hrowI, hrowJ] using h

theorem canonical_masked_pair_summable {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact quadraticRow_norm_le_one I z
      · exact quadraticRow_norm_le_one J z
    _ = _ := by ring

theorem canonical_pair_lattice_eq_primary_ideal_sum
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' lengthScale : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
      (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
      W ((Ideal.absNorm lengthScale.val : ℝ) / M) := by
  have hs := canonical_masked_pair_summable R S I J W M hM
  have hu (u : Oˣ) (lengthScale : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator lengthScale.val) *
        (quadraticRow I (u.val * primaryGenerator lengthScale.val) * quadraticRow J (u.val * primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (u.val * primaryGenerator lengthScale.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
        (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (primaryGenerator lengthScale.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, canonical_pair_unit_invariant I J hI hJ hray,
      norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  change (∑' z : O, if lambda ∣ z then (0 : ℂ) else _) = _ at ht
  have hn (lengthScale : GoodIdeal) := primaryGenerator_norm_sq lengthScale.val lengthScale.property
  simpa only [hn] using ht

theorem canonical_mask_lattice_eq_six_all_ideals
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (hmask : ∀ z : O, lambda ∣ z → rowCoprimeMask R S z = 0)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O,
      rowCoprimeMask R S (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) := by
  have ht := canonical_pair_lattice_eq_primary_ideal_sum R S I J hI hJ hray W M hM
  rw [card_units_eq_six] at ht
  have hl : (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M) := by
    apply tsum_congr
    intro z
    by_cases hz : lambda ∣ z
    · simp [hz, hmask z hz]
    · rw [if_neg hz]
  rw [hl] at ht
  rw [ht]
  congr 1
  let f : Ideal O → ℂ := fun lengthScale => rowCoprimeMask R S (primaryGenerator lengthScale) *
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
    W ((Ideal.absNorm lengthScale : ℝ) / M)
  change (∑' lengthScale : GoodIdeal, f lengthScale.val) = ∑' lengthScale : Ideal O, f lengthScale
  have hsub : (∑' lengthScale : GoodIdeal, f lengthScale.val) =
      ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | primaryGenerator lengthScale ≠ 0} : Set (Ideal O)).indicator f lengthScale :=
    tsum_subtype _ f
  rw [hsub]
  apply tsum_congr
  intro lengthScale
  by_cases hg : primaryGenerator lengthScale ≠ 0
  · exact Set.indicator_of_mem hg f
  · rw [Set.indicator_of_notMem hg]
    have hz : primaryGenerator lengthScale = 0 := not_not.mp hg
    dsimp only [f]
    rw [hz, hmask 0 (dvd_zero _)]
    simp only [zero_mul]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

theorem supported_primaryGenerator_ne_zero (lengthScale : Ideal O) (hL : Supported lengthScale) :
    primaryGenerator lengthScale ≠ 0 :=
  primaryGenerator_ne_zero_of_good_factors lengthScale hL.1 (fun P hP => (hL.2 P hP).1)

theorem supported_span_primaryGenerator_iff (lengthScale : Ideal O) :
    Supported (Ideal.span {primaryGenerator lengthScale}) ↔ Supported lengthScale := by
  constructor
  · intro h
    have hn : primaryGenerator lengthScale ≠ 0 := by
      intro hz
      apply h.1
      simp [hz]
    rwa [(primaryGenerator_spec lengthScale hn).1] at h
  · intro h
    rw [(primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale h)).1]
    exact h

theorem badPrime_mask_primaryGenerator (lengthScale : Ideal O) :
    rowCoprimeMask badPrime Finset.univ (primaryGenerator lengthScale) = if Supported lengthScale then 1 else 0 := by
  rw [badPrime_mask, supported_span_primaryGenerator_iff]

theorem canonical_supported_lattice_eq_six_ideals
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask badPrime Finset.univ z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O, if Supported lengthScale then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask badPrime Finset.univ z = 0 := by
    rw [badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => ((supported_span_iff z).mp h).1 hz
    exact if_neg hns
  rw [canonical_mask_lattice_eq_six_all_ideals badPrime Finset.univ hm I J hI hJ hray W M hM]
  congr 1
  apply tsum_congr
  intro lengthScale
  rw [badPrime_mask_primaryGenerator]
  by_cases hL : Supported lengthScale <;> simp [hL]

theorem canonical_supported_pair_poisson
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' lengthScale : Ideal O, if Supported lengthScale then χ (primaryGenerator lengthScale) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset Bool).powerset,
          let d := primeSubsetGenerator badPrime E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, badPrime i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hlat := canonical_same_ray_pair_poisson badPrime badPrime_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_supported_lattice_eq_six_ideals I J hI hJ hray W M hM
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

end CanonicalQuadraticSieve

end

end OAI

end


