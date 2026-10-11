-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0086
-- name    : PNT_ZeroFree_433_0086
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:47:24.904602+00:00
-- url     : https://prove2.me/theorems/0f38c04c-4107-4110-94f8-d3b15dab2f77
-- title:
--   Zero-free region foundations: QuadraticSieve.PrimePools [0086]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrimePools.lean#L81-L671

import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0084

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PrimePools.lean#L81-L671
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

instance canonicalPoolMaximal (F : Finset (Ideal O)) (i : primePool F) : i.val.IsMaximal := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem poolGood (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ i.val := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).1

theorem poolOdd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    ringChar (O ⧸ i.val) ≠ 2 := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).2

def poolPrimary (F : Finset (Ideal O)) (i : primePool F) : O := primaryPrime i.val

theorem poolPrimary_ne_zero (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : poolPrimary F i ≠ 0 := primaryPrime_ne_zero i.val (poolGood F hF i)

theorem poolPrimary_span (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : Ideal.span {poolPrimary F i} = i.val :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.1

theorem primaryPrime_eq_primaryGenerator (P : Ideal O) [P.IsMaximal] :
    primaryPrime P = primaryGenerator P := by
  have hp : Prime P := Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  rw [primaryGenerator, if_neg hp.ne_zero, UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
    normalize_eq]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

theorem primaryGenerator_eq_poolProduct (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) :
    primaryGenerator I = ∏ i ∈ idealSupport F I, poolPrimary F i := by
  calc
    _ = primaryGenerator (∏ i ∈ idealSupport F I, i.val) :=
      congrArg primaryGenerator (idealSupport_product_eq F hIF (hF I hIF).2.1).symm
    _ = ∏ i ∈ idealSupport F I, primaryGenerator i.val := by
      change primaryGeneratorHom (∏ i ∈ idealSupport F I, i.val) =
        ∏ i ∈ idealSupport F I, primaryGeneratorHom i.val
      rw [map_prod]
    _ = _ := Finset.prod_congr rfl (fun i hi => (primaryPrime_eq_primaryGenerator i.val).symm)

theorem quadraticRow_eq_pool (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    quadraticRow I z = QuadraticInitialBound.quadraticRow
      (fun i : primePool F => i.val) (poolGood F hF) (idealSupport F I) z := by
  rw [quadraticRow_eq F hF I hIF z]
  rfl

theorem poolPrimary_coprime (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) :
    Pairwise (Function.onFun IsCoprime (fun i : primePool F => Ideal.span {poolPrimary F i})) := by
  intro i j hij
  change IsCoprime (Ideal.span {poolPrimary F i}) (Ideal.span {poolPrimary F j})
  rw [poolPrimary_span F hF i, poolPrimary_span F hF j]
  exact Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))

theorem poolPrimary_good (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ Ideal.span {poolPrimary F i} := by rw [poolPrimary_span F hF i]; exact poolGood F hF i

theorem poolPrimary_odd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    ringChar (O ⧸ Ideal.span {poolPrimary F i}) ≠ 2 := by rw [poolPrimary_span F hF i]; exact poolOdd F hF i

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates

theorem quadraticRow_eq_primaryPool (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    quadraticRow I z = QuadraticInitialBound.quadraticRow
      (fun i : primePool F => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF) (idealSupport F I) z := by
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) = (fun i : primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  simpa only [he] using quadraticRow_eq_pool F hF I hIF z

theorem quadraticRow_eq_primeSubset (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    quadraticRow I z = finiteSexticRow
      (fun i : idealSupport F I => i.val.val) (fun i => poolGood F hF i.val) (fun _ => 3) z := by
  rw [quadraticRow_eq_pool F hF I hIF z, QuadraticInitialBound.quadraticRow_eq_canonical]

theorem idealSupport_disjoint_of_coprime (F : Finset (Ideal O)) (I J : Ideal O)
    (hIJ : IsCoprime I J) : Disjoint (idealSupport F I) (idealSupport F J) := by
  apply Finset.disjoint_left.mpr
  intro P hPI hPJ
  have hi := (mem_idealSupport_iff F I P).mp hPI
  have hj := (mem_idealSupport_iff F J P).mp hPJ
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hi
  exact hp.not_isUnit (hIJ.isRelPrime
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hi)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hj))

theorem primaryGenerator_unit_mod_four (I : Ideal O) (hI : Admissible I) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I)) := by
  let F : Finset (Ideal O) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have hJI : J = I := Finset.mem_singleton.mp hJ
    simpa only [hJI] using hI
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [primaryGenerator_eq_poolProduct F hF I (Finset.mem_singleton_self I)]
  exact RayFourExpansion.prime_product_unit_mod_four (poolPrimary F) (poolPrimary_odd F hF) _

theorem columnRay_idealQuotient_eq (D I J : Ideal O) (hI : Admissible I) (_hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : columnRay I = columnRay J) :
    columnRay (idealQuotient D I) = columnRay (idealQuotient D J) := by
  have hD : Admissible D := admissible_of_dvd hI hDI
  have hu := primaryGenerator_unit_mod_four D hD
  obtain ⟨u, hu⟩ := hu
  have hray : residue (primaryGenerator I) = residue (primaryGenerator J) := hIJ
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq hray
  have hquot : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator J) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨z, hz⟩
  have hprodI : primaryGenerator I = primaryGenerator D * primaryGenerator (idealQuotient D I) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDI]
  have hprodJ : primaryGenerator J = primaryGenerator D * primaryGenerator (idealQuotient D J) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDJ]
  rw [hprodI, hprodJ, map_mul, map_mul, ← hu] at hquot
  have heq := (Units.mul_right_inj u).mp hquot
  exact QuadraticGaussRay.residue_eq_of_quotient_four_eq _ _ heq

end
section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem quadraticRow_eq_primarySubset (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    quadraticRow I z = finiteSexticRow
      (fun i : idealSupport F I => Ideal.span {poolPrimary F i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) z := by
  have he : (fun i : idealSupport F I => Ideal.span {poolPrimary F i.val}) =
      (fun i : idealSupport F I => i.val.val) := funext (fun i => poolPrimary_span F hF i.val)
  simpa only [he] using quadraticRow_eq_primeSubset F hF I hIF z

end

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem quadraticRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    quadraticRow I 0 = 0 := by
  let F : Finset (Ideal O) := {I}
  have hIF : I ∈ F := Finset.mem_singleton_self I
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have hJI := Finset.mem_singleton.mp hJ
    simpa only [hJI] using hI
  have hS : (idealSupport F I).Nonempty := by
    by_contra hn
    have he : idealSupport F I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp := idealSupport_product_eq F hIF hI.2.1
    rw [he, Finset.prod_empty] at hp
    exact hI1 hp.symm
  let : Nonempty (idealSupport F I) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  rw [quadraticRow_eq_primeSubset F hF I hIF]
  exact finiteSexticRow_zero _ _ _

theorem quadratic_pair_zero_of_nontrivial (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (h : I ≠ 1 ∨ J ≠ 1) : quadraticRow I 0 * quadraticRow J 0 = 0 := by
  rcases h with h | h
  · rw [quadraticRow_zero_of_ne_one I hI h, zero_mul]
  · rw [quadraticRow_zero_of_ne_one J hJ h, mul_zero]

theorem quadratic_pair_tsum_remove_zero (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (h : I ≠ 1 ∨ J ≠ 1) (f : O → ℂ) :
    (∑' z : O, quadraticRow I z * quadraticRow J z * f z) =
      ∑' z : O, if z = 0 then 0 else quadraticRow I z * quadraticRow J z * f z := by
  apply tsum_congr
  intro z
  by_cases hz : z = 0
  · subst z
    rw [quadratic_pair_zero_of_nontrivial I J hI hJ h, zero_mul, if_pos rfl]
  · rw [if_neg hz]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def radialPairKernel (e k : O) (W : 𝓢(ℝ, ℂ))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (S T : Finset ι) : ℂ :=
  star (normalizedColumn p (fun U => V₁ (columnLog p X₁ U)) S) *
    normalizedColumn p (fun U => V₂ (columnLog p X₂ U)) T *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p S * primeProductNorm p T))

theorem actualSecondKernel_eq_coupled
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) :
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (radialPairKernel p e k W V₁ V₂ X₁ X₂ Y) := by
  simp only [actualSecondKernel, secondKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, radialPairKernel, normalizedColumn,
      FirstPassCubeLabels.primeProductNorm_union p S T hd, Finset.prod_union hd,
      map_mul, norm_mul, Complex.ofReal_mul,  Complex.star_def,
      Complex.conj_ofReal, div_eq_mul_inv, mul_inv_rev, map_inv₀]
    ring_nf
  · simp [hd]

theorem secondChildKernelPair_fixed_pool
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
        star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M * K (V∪N) (V∪M) := by
  have hzero (N : Finset ι) (hNF : N ∈ F.powerset)
      (hNV : N ∉ (F \ V).powerset) : ¬ Disjoint V N := by
    intro hd
    apply hNV
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hNF) hi,
      fun hiv => Finset.disjoint_left.mp hd hiv hi⟩
  unfold secondChildKernelPair
  calc
    _ = ∑ N ∈ (F \ V).powerset, ∑ M ∈ F.powerset,
        star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M * K (V∪N) (V∪M) := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro M hMF hMV
      rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₂ (m*r) c e
        (d*e*k₂) (fun _ => 1) V M (hzero M hMF hMV), mul_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro N hNF hNV
      rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₁ (m*r) c e
        (d*e*k₁) (fun _ => 1) V N (hzero N hNF hNV), star_zero]
      simp only [zero_mul, Finset.sum_const_zero]

theorem actualSecondKernel_eq_coupled_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) :
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) (radialPairKernel p e k W V₁ V₂ X₁ X₂ Y) := by
  rw [actualSecondKernel_eq_coupled,
    secondKernelPair_eq_children p hp hcop hg hinj hc hpr]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

def elementNorm (a : O) : ℝ := ‖eisEmbedding a‖ ^ 2

lemma elementNorm_pos (a : O) (ha : a ≠ 0) : 0 < elementNorm a := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))

lemma elementNorm_mul (a b : O) : elementNorm (a*b) = elementNorm a * elementNorm b := by
  simp only [elementNorm, map_mul, norm_mul, mul_pow]

theorem seven_radial_ratio (d e v n₁ n₂ k D E V X K Y : ℝ)
    (hd : 0 < d) (he : 0 < e) (hv : 0 < v) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hk : 0 < k) (hD : 0 < D) (hE : 0 < E) (hV : 0 < V) (hX : 0 < X) (hK : 0 < K) :
    Y * k / (e * v ^ 2 * n₁ * n₂) =
      (Y * K / (D * E ^ 2 * V ^ 2 * X ^ 2)) * Real.exp
        (Real.log (d*e*k/K) - Real.log (d/D) - 2*Real.log (e/E) -
          2*Real.log (v/V) - Real.log (n₁/X) - Real.log (n₂/X)) := by
  rw [show 2 * Real.log (e/E) = Real.log (e/E) + Real.log (e/E) by ring,
    show 2 * Real.log (v/V) = Real.log (v/V) + Real.log (v/V) by ring]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hd hD),
    Real.exp_log (div_pos he hE), Real.exp_log (div_pos hv hV),
    Real.exp_log (div_pos hn₁ hX), Real.exp_log (div_pos hn₂ hX),
    Real.exp_log (div_pos (mul_pos (mul_pos hd he) hk) hK)]
  field_simp

theorem second_radial_dyadic_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N M : Finset ι)
    (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX₀ : 0 < X₀) (hK : 0 < K) :
    Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (V∪N) * primeProductNorm p (V∪M)) =
      (Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
        (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
          2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
          columnLog p X₀ N - columnLog p X₀ M) := by
  rw [primeProductNorm_union p V N hVN, primeProductNorm_union p V M hVM]
  simp only [elementNorm_mul, columnLog]
  have h := seven_radial_ratio (elementNorm d) (elementNorm e) (primeProductNorm p V)
    (primeProductNorm p N) (primeProductNorm p M) (elementNorm k) D E V₀ X₀ K Y
    (elementNorm_pos d hd) (elementNorm_pos e he) (primeProductNorm_pos p hp V)
    (primeProductNorm_pos p hp N) (primeProductNorm_pos p hp M) (elementNorm_pos k hk)
    hD hE hV₀ hX₀ hK
  convert! h using 1 ; unfold elementNorm ; ring

def conjugateProfile (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap g

@[simp] lemma conjugateProfile_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    conjugateProfile g s = star (g s) := rfl

theorem normalizedColumn_pair_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N M : Finset ι)
    (hVN : Disjoint V N) (hVM : Disjoint V M)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun S => g₁ (columnLog p X S)) (V∪N)) *
      normalizedColumn p (fun S => g₂ (columnLog p X S)) (V∪M) =
    (X : ℂ)⁻¹ *
      conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) := by
  rw [normalizedColumn_union_test p hp V N hVN X X₀ hX hX₀ U hUc hUs g₁ hU₁,
    normalizedColumn_union_test p hp V M hVM X X₀ hX hX₀ U hUc hUs g₂ hU₂]
  simp only [conjugateProfile_apply, star_div₀, Complex.star_def, Complex.conj_ofReal]
  have hs : (Real.sqrt X : ℂ) * (Real.sqrt X : ℂ) = (X : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hX.le]
  simp only [div_eq_mul_inv]
  calc
    _ = ((Real.sqrt X : ℂ) * (Real.sqrt X : ℂ))⁻¹ *
        star (halfNormalizationCLM U g₁
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N)) *
        halfNormalizationCLM U g₂
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) := by
      rw [mul_inv_rev]
      simp only [Complex.star_def, div_eq_mul_inv]
      ring
    _ = _ := by rw [hs]; simp only [Complex.star_def, div_eq_mul_inv]

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

private theorem active_row_norm_le_one (S T : Finset ι) (a : O) :
    ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
    (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

def secondPairRadialMode (S T : Finset ι) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport T S, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
    activeGaussRowFactor p hp hinj hg T S e k

theorem secondPairRadialMode_summable (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => secondPairRadialMode p hp hg hinj S T e k W Y) := by
  let n := ∏ i : activeSupport T S, p i.val
  let G := FiniteGaussPhase.canonicalProductGauss (fun i : activeSupport T S => p i.val)
    (fun i => hp i.val) (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj T S)
    (fun i => hg i.val) (activeExponent T S)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hK : 0 < Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) :=
    div_pos hY (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hs := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W _ hK
  have hgk (k : O) : ‖activeGaussRowFactor p hp hinj hg T S e k‖ ≤ ‖G‖ := by
    simp only [activeGaussRowFactor, norm_mul, norm_star]
    change ‖G‖ * (_ * _) ≤ ‖G‖
    have hb : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) e‖ *
        ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) k‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (active_row_norm_le_one p hg T S e)
        (active_row_norm_le_one p hg T S k) (norm_nonneg _) zero_le_one
    exact mul_le_of_le_one_right (norm_nonneg _) hb
  have harg (k : O) : Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) =
      (Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) * ‖eisEmbedding k‖ ^ 2 := by ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((hs.mul_left ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖).mul_right ‖G‖)
  intro k
  simp only [secondPairRadialMode, norm_mul]
  rw [show (∏ i : activeSupport T S, p i.val) = n from rfl, harg]
  exact mul_le_mul_of_nonneg_left (hgk k) (by positivity)

theorem maskedSecondDual_eq_modes (G S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    maskedSecondDual p hg hp hinj G S T W Y =
      ∑ E ∈ G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, secondPairRadialMode p hp hg hinj S T
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y := by
  simp only [maskedSecondDual, secondPairRadialMode, mul_assoc, tsum_mul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  ring

def residualSecondMode (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
    if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y
    else 0

theorem residualSecondMode_summable (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) := by
  apply summable_sum
  intro S hS
  apply summable_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd]
    exact (secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).mul_left _
  · simp only [if_neg hd]
    exact summable_zero

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondFrequencyKernel (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T
  else 0

theorem residualSecondMode_tsum (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' k : O, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) =
      ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑' k : O, if Disjoint S T then
          star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
          (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
          secondPairRadialMode p hp hg hinj S T e k W Y
        else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : O => if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd]
      exact (secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).mul_left _
    · simp only [if_neg hd]
      exact summable_zero
  unfold residualSecondMode
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  exact Summable.tsum_finsetSum (fun T _ => hs S T)

def secondOverlapBlock (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset, if Disjoint S T then
    overlapPairWeight p hg Ψ m c d H G S T * maskedSecondDual p hg hp hinj G S T W Y
  else 0

theorem secondOverlapBlock_eq_modes (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y =
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E ∈ G.powerset,
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
            (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
          ∑' k : O, residualSecondMode p hp hg hinj F G Ψ Ψ m c d
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y := by
  let a := (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ)
  let w := fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)
  let f := fun (E S T : Finset ι) (k : O) => if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S *
      secondInputCoefficient p hg Ψ m c d (fun U => H (G ∪ U)) S) *
    (supportMobius (fun i => Ideal.span {p i}) T *
      secondInputCoefficient p hg Ψ m c d (fun U => H (G ∪ U)) T) *
    secondPairRadialMode p hp hg hinj S T (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y
    else 0
  have hterm (S T : Finset ι) :
      (if Disjoint S T then overlapPairWeight p hg Ψ m c d H G S T *
        maskedSecondDual p hg hp hinj G S T W Y else 0) =
      a * ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd, maskedSecondDual_eq_modes p hp hg hinj,
        overlapPairWeight, f, Finset.mul_sum, tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      dsimp only [a, w]
      ring
    · simp [hd, f]
  calc
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
      simp only [secondOverlapBlock, hterm, Finset.mul_sum]
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ E ∈ G.powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_comm]
    _ = a * ∑ E ∈ G.powerset, ∑ S ∈ (F \ G).powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro E hE
      rw [residualSecondMode_tsum p hp hg hinj F G Ψ Ψ m c d
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E)
        (primeSubsetGenerator_ne_zero _ E) W Y hY]
      simp only [Finset.mul_sum]
      rfl

theorem residualSecondMode_eq_frequencyKernel (F G E : Finset ι) (hEG : E ⊆ G)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
    (k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y =
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m (secondMaskQuotient p E G hEG) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k H₁ H₂ W Y := by
  unfold residualSecondMode
  rw [input_pair_fixed_pool p hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂]
  unfold secondFrequencyKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [if_pos hd, if_pos hd]
    have hn : (∏ i : activeSupport T S, p i.val) = ∏ i ∈ S ∪ T, p i := by
      rw [Finset.prod_coe_sort]
      simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
        Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.union_comm T S]
    simp only [secondPairRadialMode, secondGaussTerm, hn, primeProductNorm,
      ← secondMaskQuotient_spec p E G hEG]
    ring
  · simp [hd]

end SecondPassArithmetic

end

end OAI

end


