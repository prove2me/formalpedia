-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0258_parallel1
-- name    : PNT_ZeroFree_433_0258_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:47:32.750041+00:00
-- url     : https://prove2.me/theorems/e86904a3-af99-4019-8a5c-3a673c06c33e
-- title:
--   Zero-free region foundations: Eisenstein.PrimeGaussFactors [0258_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.PrimeGaussFactors
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimeGaussFactors.lean#L85-L647

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0046_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel2
import Definitions.Def_PNT_ZeroFree_433_0221_parallel2
import Definitions.Def_PNT_ZeroFree_433_0227_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/PrimeGaussFactors.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
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
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0258_parallel1_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units


end


section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_inverse (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (primeCubicMulChar p hp hprimary)⁻¹=primeCubicMulChar p hp hprimary^2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [←pow_succ'] using primeCubicMulChar_cube p hp hprimary

lemma primeCubicGauss_two_eq_star (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis) :
    primeCubicGauss p hp hprimary 2 h=star (primeCubicGauss p hp hprimary 1 h) := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  rw [primeCubicGauss_eq_gaussSum,primeCubicGauss_eq_gaussSum,pow_one,star_gaussSum_eq,
    primeCubicMulChar_inverse]
  have he:=mul_gaussSum_inv_eq_gaussSum
    (primeCubicMulChar p hp hprimary^2) ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h))
  have hm:(primeCubicMulChar p hp hprimary^2) (-1 : Eis⧸Ideal.span {p})=1:=by
    rw [MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),←map_pow]
    norm_num
  rw [hm,one_mul] at he
  exact he.symm

lemma primeCubicGauss_one_normalized (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    [(Ideal.span {p}:Ideal Eis).IsMaximal] (hg:lambda∉(Ideal.span {p}:Ideal Eis)) :
    primeCubicGauss p hp hprimary 1 1/(‖eisEmbedding p‖:ℂ)=
      breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero := by
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  unfold breveGamma2
  rw [primeCubicGauss_eq_gaussSum,pow_one,canonicalSextic_pow_two]
  simp only [map_one,AddChar.mulShift_one]
  congr 2
  apply DFunLike.ext
  intro x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [primeCubicMulChar_mk,MulChar.ringHomComp_apply,
    symbol_prime p hp hprimary,primeValue_eq _ hg]


lemma prime_normalizer_powers (p:Eis) (hp:p≠0) :
    (‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))=
      (‖eisEmbedding p‖:ℂ)⁻¹ := by
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  rw [←Complex.ofReal_natCast,←eisEmbedding_norm_sq_eq_absNorm_span,pow_two,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ←mul_assoc,←Complex.cpow_add _ _ hr,←Complex.cpow_add _ _ hr]
  convert! Complex.cpow_neg_one (‖eisEmbedding p‖:ℂ) using 1 ; congr 1 ; norm_num


end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def normalizedCubicUnitGauss (n:Eis) : ℂ :=
  cubicUnitGaussSum 1 n/(‖eisEmbedding n‖:ℂ)


lemma cubicSymbol_star_mul (a b:Eis) (hb:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b)=1 := by
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hb hab,map_one]
  have hn:‖eisEmbedding (symbol a b)‖=1:=by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
    simpa only [norm_pow,norm_one,one_pow] using congrArg norm hc
  rw [mul_comm]
  simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
    Complex.mul_conj (eisEmbedding (symbol a b))

lemma normalizedCubicUnitGauss_coprime_product (a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (normalizedCubicUnitGauss (a*b))=
      eisEmbedding (symbol a b)*star (normalizedCubicUnitGauss a)*star (normalizedCubicUnitGauss b) := by
  have hG:=cubicUnitGaussSum_coprime_product 1 a b ha hb hap hbp hab
  simp only [one_mul] at hG
  have ht:=cubicUnitGaussSum_frequency_twist 1 b a hb hbp hab.symm
  simp only [one_mul] at ht
  have hN:eisEmbedding (symbol a b)*normalizedCubicUnitGauss (a*b)=
      normalizedCubicUnitGauss a*normalizedCubicUnitGauss b:=by
    unfold normalizedCubicUnitGauss
    rw [hG,map_mul,norm_mul,Complex.ofReal_mul]
    calc
      _=cubicUnitGaussSum 1 a*(eisEmbedding (symbol a b)*cubicUnitGaussSum a b)/
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)):=by ring
      _=_:=by rw [ht];ring
  have hs:=congrArg star hN
  simp only [star_mul] at hs
  have hc:=cubicSymbol_star_mul a b hbp hab
  calc
    _=(star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b))*
        star (normalizedCubicUnitGauss (a*b)):=by rw [hc,one_mul]
    _=eisEmbedding (symbol a b)*(star (normalizedCubicUnitGauss (a*b))*
        star (eisEmbedding (symbol a b))):=by ring
    _=_:=by rw [hs];ring


lemma primary_finset_product {ι:Type*} (s:Finset ι) (p:ι→Eis)
    (hp:∀i∈s,lambda^2∣p i-1) : lambda^2∣(∏i∈s,p i)-1 := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi]
    exact primary_mul _ _ (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_prime_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (x:Eis) (hpx:p∣x) : symbol x p=0 := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpx),MulChar.map_zero]

lemma cubicSymbol_zero_of_not_coprime (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1)
    (x:Eis) (hnot:¬IsCoprime n x) : symbol x n=0 := by
  obtain ⟨s,hs,hp⟩:=exists_primary_prime_factorization n hn hprimary
  rw [←hs] at hnot ⊢
  clear hs hn hprimary n
  induction s using Multiset.induction_on with
  | empty=>exact False.elim (hnot (by simpa using (isCoprime_one_left : IsCoprime (1:Eis) x)))
  | @cons p s ih=>
    have hprime:=hp p (Multiset.mem_cons_self _ _)
    have hrest:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hp q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,symbol_mul_denominator]
    by_cases hc:IsCoprime p x
    · have hnc:¬IsCoprime s.prod x:=fun h=>hnot (by simpa using hc.mul_left h)
      rw [ih hnc hrest,mul_zero]
    · rw [cubicSymbol_prime_zero p hprime.1 hprime.2 x
        (hprime.1.irreducible.dvd_iff_not_isCoprime.mpr hc),zero_mul]

lemma cubicRow_eq_idealSymbol (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) (a:Eis) :
    cubicRow I hI (Ideal.Quotient.mk I a)=eisEmbedding (idealSymbol I a) := by
  rw [cubicRow_mk]
  simp_rw [canonicalSextic_pow_two,MulChar.ringHomComp_apply,←primeValue_eq]
  change (∏P:primeSupport I,eisEmbedding (primeValue P.val a))=eisEmbedding (idealSymbol I a)
  rw [←Finset.prod_subtype (primeSupport I) (fun _=>Iff.rfl)
    (fun P=>eisEmbedding (primeValue P a)),←map_prod]
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hnodup: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  congr 1
  rw [idealSymbol,if_neg hI0]
  change (((primeSupport I).val.map (fun P=>primeValue P a)).prod)=_
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hnodup.dedup
  rw [hv]

lemma cubicUnitGaussSum_full (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1) (h:Eis) :
    cubicUnitGaussSum h n=
      ∑'x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
        quotientTrace n hn (Ideal.Quotient.mk _ h*x) := by
  let f:(Eis⧸Ideal.span {n})→ℂ:=fun x=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
      quotientTrace n hn (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hnot
    change ¬IsUnit x at hnot
    have hcop:¬IsCoprime n (GaussianShiftedPartition.representative n x):=by
      intro hc
      apply hnot
      have hh:=(isUnit_quotient_span_iff n (GaussianShiftedPartition.representative n x)).mpr hc
      simpa only [GaussianShiftedPartition.representative_spec] using hh
    exact hx (by simp only [f,cubicSymbol_zero_of_not_coprime n hn hprimary _ hcop,map_zero,zero_mul])
  change cubicUnitGaussSum h n=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  dsimp only [f]
  rw [←GaussianShiftedPartition.representative_spec n x.val,quotientTrace_mk_product]
  simp only [GaussianShiftedPartition.representative_spec]

theorem normalizedCubicUnitGauss_eq_gaussTwo (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hsq:Squarefree I) :
    normalizedCubicUnitGauss (primaryGenerator I)=gaussTwo I hI := by
  let n:=primaryGenerator I
  let:Finite (Eis⧸Ideal.span {n}):=finite_quotient_span hI
  let:Fintype (Eis⧸Ideal.span {n}):=Fintype.ofFinite _
  let e:=Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  rw [normalizedCubicUnitGauss,cubicUnitGaussSum_full _ hI (primaryGenerator_spec I hI).2 1,
    tsum_fintype]
  change (∑x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
    quotientTrace n hI (Ideal.Quotient.mk _ 1*x))/(‖eisEmbedding n‖:ℂ)=
    (∑x:Eis⧸Ideal.span {n},cubicRow I hI (e x)*quotientTrace n hI x)/(‖eisEmbedding n‖:ℂ)
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk,cubicRow_eq_idealSymbol I hI hsq]
  have hc:n∣GaussianShiftedPartition.representative n (Ideal.Quotient.mk (Ideal.span {n}) a)-a:=
    gaussRep_mk_congr n a
  have hs:symbol a n=idealSymbol I a:=by
    unfold symbol
    rw [(primaryGenerator_spec I hI).1]
  rw [symbol_congr hc,hs,map_one,one_mul]

end CubicEisenstein

end

end OAI

end


