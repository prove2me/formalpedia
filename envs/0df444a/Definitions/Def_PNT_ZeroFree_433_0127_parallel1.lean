-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0127_parallel1
-- name    : PNT_ZeroFree_433_0127_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:34:19.396502+00:00
-- url     : https://prove2.me/theorems/ba16f6c7-2190-4b41-a1a6-d1adf7800ba5
-- title:
--   Zero-free region foundations: QuadraticSieve.CommonMasks [0127_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L83-L645

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0065_1
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0095
import Definitions.Def_PNT_ZeroFree_433_0097
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0099
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

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

def maskedPairDualTail (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K

def retainedDualPair (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M F K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val*
    (((M/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))*F):ℝ):ℂ)*
      dualPrincipalIdeal I J W
        (Real.sqrt (F*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)))))


end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson


def maskedDualTailFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0


end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

theorem normalizedFactors_commonMaskIdeal (D : Ideal O) :
    UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
  have hp (P : Ideal O) (hP : P∈(gcdMaskPrimes D).val) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  simpa only [commonMaskIdeal,Finset.prod_val,id_eq] using h

theorem idealZeroMask_commonMaskIdeal (D : Ideal O) (z : O) :
    idealZeroMask (commonMaskIdeal D) z =
      rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z := by
  classical
  simp only [idealZeroMask,normalizedFactors_commonMaskIdeal,rowCoprimeMask,
    Finset.mem_univ,true_and,Subtype.exists,exists_prop,Finset.mem_val]

lemma idealZeroMask_idempotent (D : Ideal O) (z : O) :
    idealZeroMask D z*idealZeroMask D z=idealZeroMask D z := by
  classical
  unfold idealZeroMask
  split_ifs <;> norm_num


theorem residual_joint_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I*J) => P.val) Finset.univ z =
      rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val)
        Finset.univ z := by
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hi : idealZeroMask I z=idealZeroMask D z*idealZeroMask (idealQuotient D I) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D I) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDI).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hIq.1 z
  have hj : idealZeroMask J z=idealZeroMask D z*idealZeroMask (idealQuotient D J) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D J) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDJ).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hJq.1 z
  rw [gcdMaskPrimes_mask,singleton_rowCoprimeMask_eq_idealZeroMask,
    idealZeroMask_mul I J hI.1 hJ.1,
    idealZeroMask_mul (commonMaskIdeal D) _ (commonMaskIdeal_squarefree D).ne_zero (mul_ne_zero hIq.1 hJq.1),
    idealZeroMask_mul _ _ hIq.1 hJq.1,idealZeroMask_commonMaskIdeal,gcdMaskPrimes_mask,hi,hj]
  calc
    _ = (rowCoprimeMask badPrime Finset.univ z)*(idealZeroMask D z*idealZeroMask D z)*
      (idealZeroMask (idealQuotient D I) z*idealZeroMask (idealQuotient D J) z) := by ring
    _ = _ := by rw [idealZeroMask_idempotent]

theorem lowPrincipalLattice_residual (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (X : ℝ) :
    lowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask
        (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val) Finset.univ z *
        (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/X)) := by
  unfold lowPrincipalLattice
  apply tsum_congr
  intro z
  by_cases hz : z=0
  · subst z
    simp only [jointMask_zero,ite_true,mul_zero,zero_mul]
  · rw [if_neg hz,quadraticSquareProfile_apply,residual_joint_mask D I J hI hJ hDI hDJ]

theorem idealRange_filter_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (idealRange K).filter (fun B => IsCoprime B G)=coprimeSquarefreeRange G K := by
  classical
  ext B
  constructor
  · intro h
    obtain ⟨hb,hc⟩ := Finset.mem_filter.mp h
    have hB := mem_idealRange.mp hb
    exact Finset.mem_filter.mpr ⟨mem_squarefreeIdealRange.mpr ⟨hB.1.2.1,hB.2⟩,hc⟩
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp h).2⟩
    exact coprimeSquarefreeRange_subset_idealRange G hbad K h

theorem sum_idealRange_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) (f : Ideal O → ℂ) :
    (∑ B : idealRange K, if IsCoprime B.val G then f B.val else 0) =
      ∑ B : coprimeSquarefreeRange G K, f B.val := by
  classical
  rw [Finset.sum_coe_sort (idealRange K) (fun B => if IsCoprime B G then f B else 0),
    ←Finset.sum_filter,idealRange_filter_coprime G K hbad,
    Finset.sum_coe_sort (coprimeSquarefreeRange G K) f]


end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson


end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem residual_commonMask_coprime (D I : Ideal O) (hI : Admissible I) (hDI : D∣I) :
    IsCoprime (commonMaskIdeal D) (idealQuotient D I) := by
  have hD := admissible_of_dvd hI hDI
  have hQ := admissible_idealQuotient hI hDI
  have hs : Squarefree (D*idealQuotient D I) := by rw [idealQuotient_mul hDI]; exact hI.2.1
  have hrel := (squarefree_mul_iff.mp hs).1
  have hG := (commonMaskIdeal_squarefree D).ne_zero
  apply ideals_coprime_of_relprime
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hG).mpr
  intro P hPG hPQ hp
  have hf : P∈UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hG).mpr ⟨hp,hPG⟩
  rw [normalizedFactors_commonMaskIdeal] at hf
  have hmem : P∈fixedBadPrimes ∨ P∈primeSupport D := Finset.mem_union.mp hf
  rcases hmem with hbad | hPD
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors (idealQuotient D I) :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.1).mpr ⟨hp,hPQ⟩
    exact (prime_good_iff_not_bad P).mp (hQ.2.2 P hfac) hbad
  · have hd : P∣D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPD)
    exact hp.not_isUnit (hrel hd hPQ)

theorem idealQuotient_norm_eq (D I : Ideal O) (hD : D≠0) (hDI : D∣I) :
    (Ideal.absNorm (idealQuotient D I):ℝ)=(Ideal.absNorm I:ℝ)/(Ideal.absNorm D:ℝ) := by
  have hn : (Ideal.absNorm D:ℝ)≠0 := by
    exact_mod_cast (show Ideal.absNorm D≠0 from fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (eq_div_iff hn).mpr
  rw [mul_comm,←Nat.cast_mul,←map_mul,idealQuotient_mul hDI]

theorem idealQuotient_shell (D I : Ideal O) (hD : D≠0) (hDI : D∣I) (N : ℝ)
    (hI : N/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤N) :
    (N/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (idealQuotient D I):ℝ) ∧
      (Ideal.absNorm (idealQuotient D I):ℝ)≤N/(Ideal.absNorm D:ℝ) := by
  have hn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  rw [idealQuotient_norm_eq D I hD hDI]
  constructor
  · calc
      _ = (N/2)/(Ideal.absNorm D:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hI.1 hn.le
  · exact div_le_div_of_nonneg_right hI.2 hn.le

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : Finset n :=
  Finset.univ.filter (fun j => D ∣ cols j ∧ columnRay (cols j)=c ∧ a j≠0)

theorem mem_gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (j : n) :
    j∈gcdRaySupport cols a D c ↔ D∣cols j ∧ columnRay (cols j)=c ∧ a j≠0 := by
  simp only [gcdRaySupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem gcd_ray_pair_sum_restrict {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O)
    (c : EisensteinEPrimaryPhase.Coord) (H : n → n → ℂ) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
      then star (a j)*a k*H j k else 0) =
    ∑ j : gcdRaySupport cols a D c, ∑ k : gcdRaySupport cols a D c,
      if gcd (cols j.val) (cols k.val)=D then star (a j.val)*a k.val*H j.val k.val else 0 := by
  classical
  let S := gcdRaySupport cols a D c
  let f := fun j k => if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
    then star (a j)*a k*H j k else 0
  have hjzero (j : n) (hj : j∉S) (k : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a j=0 := by
        by_contra hn
        apply hj
        exact (mem_gcdRaySupport cols a D c j).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_left (cols j) (cols k),h.2.1,hn⟩
      simp only [hz,star_zero,zero_mul]
    · rfl
  have hkzero (k : n) (hk : k∉S) (j : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a k=0 := by
        by_contra hn
        apply hk
        exact (mem_gcdRaySupport cols a D c k).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_right (cols j) (cols k),h.2.2,hn⟩
      simp only [hz,mul_zero,zero_mul]
    · rfl
  have hleft : (∑ j∈S, ∑ k, f j k) = ∑ j, ∑ k, f j k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    exact Finset.sum_eq_zero (fun k _ => hjzero j hj k)
  change (∑ j, ∑ k, f j k)=_
  rw [←hleft,←Finset.sum_coe_sort S (fun j => ∑ k, f j k)]
  apply Finset.sum_congr rfl
  intro j _
  have hright : (∑ k∈S, f j.val k) = ∑ k, f j.val k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    exact hkzero k hk j.val
  rw [←hright,←Finset.sum_coe_sort S (fun k => f j.val k)]
  apply Finset.sum_congr rfl
  intro k _
  have hj := (mem_gcdRaySupport cols a D c j.val).mp j.property
  have hk := (mem_gcdRaySupport cols a D c k.val).mp k.property
  simp only [f,hj.2.1,hk.2.1,and_true]

theorem gcdRaySupport_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑ j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤ ∑ j, ‖a j‖^2 := by
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

theorem gcdRaySupport_quotient_properties (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (hD : D≠0)
    (c : EisensteinEPrimaryPhase.Coord) :
    let cols := fun j : gcdRaySupport (fun I : idealRange N => I.val) a D c =>
      idealQuotient D j.val.val
    Function.Injective cols ∧
    (∀ j, Admissible (cols j) ∧
      (X/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (cols j):ℝ) ∧
      (Ideal.absNorm (cols j):ℝ)≤X/(Ideal.absNorm D:ℝ) ∧
      IsCoprime (commonMaskIdeal D) (cols j)) ∧
    (∀ j k, columnRay (cols j)=columnRay (cols k)) := by
  dsimp only
  have hp (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) :=
    (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  refine ⟨?_,?_,?_⟩
  · intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_injective_on D (hp j).1 (hp k).1 hjk
  · intro j
    have hadm := (mem_idealRange.mp j.val.property).1
    have hshell := idealQuotient_shell D j.val.val hD (hp j).1 X
      ⟨(ha j.val (hp j).2.2).1.le,(ha j.val (hp j).2.2).2⟩
    exact ⟨admissible_idealQuotient hadm (hp j).1,hshell.1,hshell.2,
      residual_commonMask_coprime D j.val.val hadm (hp j).1⟩
  · intro j k
    exact columnRay_idealQuotient_eq D j.val.val k.val.val
      (mem_idealRange.mp j.val.property).1 (mem_idealRange.mp k.val.property).1
      (hp j).1 (hp k).1 ((hp j).2.1.trans (hp k).2.1.symm)

theorem gcdRaySupport_proper (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) : j.val.val≠D := by
  intro h
  have hp := (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  have hs := (ha j.val hp.2.2).1
  rw [h] at hs
  exact (not_lt_of_ge hsmall) hs

end CanonicalQuadraticSieve

end

end OAI

end


