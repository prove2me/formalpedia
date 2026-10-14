-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0127_parallel2
-- name    : PNT_ZeroFree_433_0127_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:39:38.652988+00:00
-- url     : https://prove2.me/theorems/4b3366f5-6b34-4534-99be-85060c0f14fb
-- title:
--   Zero-free region foundations: QuadraticSieve.CommonMasks [0127_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L96-L445

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0095
import Definitions.Def_PNT_ZeroFree_433_0097
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0099
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0125_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel2
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum


theorem maskedPairIdealDualKernel_retained
    (G I J : Ideal O) (hG : G ≠ 0) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I=columnRay J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    maskedPairIdealDualKernel G I J W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
        retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K) +
      maskedPairDualTail G I J W M K := by
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hqpos (q : Ideal O) (hq : q ∈ idealDivisors G) : 0<(Ideal.absNorm q:ℝ) := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hpoint (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
        (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
          ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
            ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))) =
        (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
          retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K +
        ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
          (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
            dualSquarefreeTail I J W
              (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K) := by
    have hqN := hqpos q hq
    have ht : 0 < M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      positivity
    rw [dual_ideal_low_add_tail I J W _ K ht,dualSquarefreeLow_principal_finite I J hI hJ hray W _ K ht,
      mul_add,mul_add]
    congr 1
    simp only [retainedDualPair,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    have hB : 0<(Ideal.absNorm B.val:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr
        (fun hz => (mem_squarefreeIdealRange.mp B.property).1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    have harg : (1:ℝ)/((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ)) =
        (Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)) := by
      field_simp
    rw [harg]
    push_cast
    ring
  unfold maskedPairIdealDualKernel maskedPairDualTail
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson


def maskedDualFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0


end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum


theorem idealZeroMask_generator_eq_indicator (D B : Ideal O) (hD : D≠0) :
    idealZeroMask D (idealGenerator B) = if IsCoprime B D then 1 else 0 := by
  classical
  by_cases hc : IsCoprime B D
  · rw [if_pos hc,idealZeroMask_generator_eq_one D B hc.symm]
  · rw [if_neg hc]
    apply if_pos
    by_contra hn
    apply hc
    apply IsCoprime.symm
    apply ideals_coprime_of_relprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hD).mpr
    intro P hPD hPB hp
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors D :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hD).mpr ⟨hp,hPD⟩
    have hgen : idealGenerator B∈P := by
      apply (Ideal.span_singleton_le_iff_mem P).mp
      rw [span_idealGenerator]
      exact Ideal.dvd_iff_le.mp hPB
    exact hn ⟨P,hfac,hgen⟩

theorem idealZeroMask_primary_eq_indicator (D B : Ideal O) (hD : D≠0) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {primaryGenerator B}=Ideal.span {idealGenerator B} := by
    rw [(primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)).1,span_idealGenerator]
  rw [idealZeroMask_span_eq D _ _ he,idealZeroMask_generator_eq_indicator D B hD]

theorem commonMask_primary_indicator (D B : Ideal O) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B (commonMaskIdeal D) then 1 else 0 := by
  have he := idealZeroMask_commonMaskIdeal D (primaryGenerator B)
  rw [gcdMaskPrimes_mask,badPrime_mask_primaryGenerator,if_pos hB,one_mul] at he
  rw [←he,idealZeroMask_primary_eq_indicator _ B (commonMaskIdeal_squarefree D).ne_zero hB]


def pairMaskedSquareSource (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (B : Ideal O) : ℂ :=
  (quadraticRow I (primaryGenerator B)*quadraticRow J (primaryGenerator B))*
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(I*J)} => P.val) Finset.univ z *
      (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B))

theorem originalPairLow_residual_finite (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      (6:ℂ)⁻¹*∑ B : coprimeSquarefreeRange (commonMaskIdeal D) K,
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val := by
  classical
  rw [originalPairLow_principal_finite I J hI hJ W M K hM]
  have ht (B : idealRange K) :
      (quadraticRow I (primaryGenerator B.val)*quadraticRow J (primaryGenerator B.val))*
        ((6:ℂ)⁻¹*lowPrincipalLattice I J W (Real.sqrt (M/(Ideal.absNorm B.val:ℝ)))) =
      (6:ℂ)⁻¹*(if IsCoprime B.val (commonMaskIdeal D) then
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val else 0) := by
    have hB := admissible_supported (mem_idealRange.mp B.property).1
    have hp := canonical_pair_divisor_mask D I J hI hJ hDI hDJ (primaryGenerator B.val)
    rw [canonical_quadraticRow_star I hI,commonMask_primary_indicator D B.val hB] at hp
    rw [hp,lowPrincipalLattice_residual D I J hI hJ hDI hDJ]
    by_cases hc : IsCoprime B.val (commonMaskIdeal D)
    · simp only [hc,ite_true,one_mul,pairMaskedSquareSource,sourcePrincipalScale]
      ring
    · simp only [hc,ite_false,zero_mul,mul_zero]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_idealRange_coprime (commonMaskIdeal D) K
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)]

theorem originalLow_gcd_aggregate
    {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  classical
  let S := coprimeSquarefreeRange (commonMaskIdeal D) K
  let q := fun j => idealQuotient D (cols j)
  have hq (j : n) : Admissible (q j) := admissible_idealQuotient (hcols j) (hdiv j)
  have ht (j k : n) :
      (if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * ∑ B : S,
        originalTerm (fun B : S => B.val) q q a a 1 1 B j k *
          ∑' z : O, rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(q j*q k)} => P.val) Finset.univ z *
            (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B.val)) := by
    have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
    by_cases hc : IsCoprime (q j) (q k)
    · rw [if_pos (heq.mpr hc),originalPairLow_residual_finite D _ _ (hcols j) (hcols k) (hdiv j) (hdiv k) W M K hM]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      simp only [originalTerm,hc,ite_true,one_dvd,pairMaskedSquareSource,star_mul,
        canonical_quadraticRow_star _ (hq j)]
      dsimp only [q]
      ring
    · have hg : ¬gcd (cols j) (cols k)=D := fun h => hc (heq.mp h)
      simp only [hg,ite_false,originalTerm,hc,Finset.sum_const_zero,zero_mul,mul_zero]
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset n)) (t := (Finset.univ:Finset S))]
  simp only [maskedPrincipalSourceSum,Finset.mul_sum,S,q,sourcePrincipalScale]

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem originalDual_gcd_aggregate {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) =
      maskedDualFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M := by
  unfold maskedDualFamily
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
  by_cases hg : gcd (cols j) (cols k)=D
  · have hneq : cols j≠cols k := by
      intro h
      rw [← h] at hg
      exact hproper j (by simpa using hg)
    rw [if_pos hg,if_pos (heq.mp hg),
      originalPairDualKernel_eq_divisors D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) hneq (hray j k) W M hM]
  · rw [if_neg hg,if_neg (fun hc => hg (heq.mpr hc))]


end


end CanonicalQuadraticSieve

end

end OAI

end


