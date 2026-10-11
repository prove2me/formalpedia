-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0220_parallel1
-- name    : PNT_ZeroFree_433_0220_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:36:41.486627+00:00
-- url     : https://prove2.me/theorems/1d515216-a49a-4417-9c40-6eebeba49483
-- title:
--   Zero-free region foundations: Eisenstein.RamifiedGaussSeries [0220_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.RamifiedGaussSeries
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedGaussSeries.lean#L86-L589

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0015
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0145_parallel1
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel2
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedGaussSeries.lean
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

lemma ramified_symbol_congr_mod_nine (u : Eisˣ) (n : ℕ) (d e : Eis)
    (hd : (3:Eis)∣d-1) (he : (3:Eis)∣e-1) (hde : (9:Eis)∣d-e) :
    symbol (u.val*lambda^n) d=symbol (u.val*lambda^n) e := by
  have hdp:=lambda_sq_dvd_three.trans hd
  have hep:=lambda_sq_dvd_three.trans he
  rw [symbol_mul_numerator _ _ d hdp,symbol_mul_numerator _ _ e hep,
    symbol_pow_numerator _ d hdp,symbol_pow_numerator _ e hep,
    symbol_unit_congr_mod_nine u.val d e u.isUnit hdp hep hde,
    CubicRamified.symbol_lambda_congr_mod_nine d e hdp hep hde]

lemma primary_add_nine (d w : Eis) (hd : (3:Eis)∣d-1) :
    (3:Eis)∣d+9*w-1 := by
  convert! dvd_add hd (show (3:Eis)∣9*w from ⟨3*w,by ring⟩) using 1 ; ring

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

lemma residueAdditive_add (h c d e : Eis) :
    residueAdditive h c (d+e)=residueAdditive h c d*residueAdditive h c e := by
  unfold residueAdditive
  rw [map_add,mul_add,add_div,AddChar.map_add_eq_mul]

theorem ramified_arithmetic_additive_eigen (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (w : Eis) :
    residueAdditive h (u.val*lambda^n) (9*w)*arithmeticResidueSum h (u.val*lambda^n)=
      arithmeticResidueSum h (u.val*lambda^n) := by
  let c:=u.val*lambda^n
  have hc:c≠0:=ramifiedElement_ne_zero u n
  have hlevel:(3:Eis)∣c:=ramifiedElement_level u n hn
  have heq:=(ramifiedResidueAddEquiv u n w).tsum_eq
    (fun r : AdmissibleResidue c=>eisEmbedding (symbol c (denominatorRep c r.1))*
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c,residueAdditive h c (9*w)*
      (eisEmbedding (symbol c (denominatorRep c r.1))*residueAdditive h c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c (ramifiedResidueAddEquiv u n w r).1))*
        residueAdditive h c (denominatorRep c (ramifiedResidueAddEquiv u n w r).1) := by
      apply tsum_congr
      intro r
      let d:=denominatorRep c r.1
      have hrep : 3*c∣denominatorRep c (ramifiedResidueAdd u n w r).1-(d+9*w):=
        denominatorRep_mk_congr c (d+9*w)
      have hdp:(3:Eis)∣d+9*w-1:=primary_add_nine d w r.2.2
      have hchar : symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1)=symbol c d := by
        rw [row_symbol_congr_modulus c _ (d+9*w) hlevel hdp hrep]
        exact ramified_symbol_congr_mod_nine u n (d+9*w) d hdp r.2.2 ⟨w,by ring⟩
      change _=eisEmbedding (symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1))*
        residueAdditive h c (denominatorRep c (ramifiedResidueAdd u n w r).1)
      rw [hchar,residueAdditive_congr h c _ (d+9*w) hc hrep,residueAdditive_add]
      dsimp only [d]
      ring
    _ = _ := heq

theorem ramified_arithmetic_support (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    u.val*lambda^n∣3*h := by
  let c:=u.val*lambda^n
  have hc:c≠0:=ramifiedElement_ne_zero u n
  have hp : ∀w:Eis,residueAdditive h c (9*w)=1:=by
    intro w
    apply mul_right_cancel₀ hA
    rw [ramified_arithmetic_additive_eigen h u n hn w,one_mul]
  let psi:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc
  have hprimitive:psi.IsPrimitive:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  by_contra hdiv
  have hne:Ideal.Quotient.mk (Ideal.span {c}) (3*h)≠0:=by
    intro hh
    exact hdiv (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  apply hprimitive hne
  ext x
  obtain ⟨w,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [AddChar.mulShift_apply,←map_mul,psi,eisTraceModChar,
    IdealGaussCRT.traceModChar_mk,AddChar.one_apply]
  convert! hp w using 1
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp
  ; ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_primary_coprime (u : Eisˣ) (n : ℕ) (b : Eis)
    (hb : lambda^2∣b-1) : IsCoprime (3*(u.val*lambda^n)) b := by
  have h3:IsCoprime (3:Eis) b:=(primary_coprime_three b hb).symm
  have hl:IsCoprime lambda b:=coprime_of_dvd_sub_one lambda b
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hb)
  have hu:IsCoprime u.val b:=⟨u.inv,0,by simp⟩
  exact h3.mul_left (hu.mul_left hl.pow_left)


lemma ramifiedElement_absNorm (u : Eisˣ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {u.val*lambda^n})=3^n := by
  have hu:Ideal.span {u.val}=(1:Ideal Eis):=by
    rw [Ideal.one_eq_top]
    exact Ideal.span_singleton_eq_top.mpr u.isUnit
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,hu,map_one,one_mul,
    ←Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

lemma three_absNorm : Ideal.absNorm (Ideal.span {(3:Eis)})=9 := by
  rw [←qNat_eq_absNorm_span]
  have he:(3:Eis)=ActualEisensteinCoordinates.eval 3 0:=by
    simp [ActualEisensteinCoordinates.eval]
  rw [he,ShortDraftLatticeCount.qNat,ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> decide

theorem ramified_arithmetic_norm_bound (h : Eis) (hh : h≠0) (u : Eisˣ)
    (n : ℕ) (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    3^n≤9*Ideal.absNorm (Ideal.span {h}) := by
  have hI:(Ideal.span {h}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hh
  have hN:0<Ideal.absNorm (Ideal.span {h}):=
    Nat.pos_of_ne_zero (fun hz=>hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply Nat.le_of_dvd (by positivity)
  obtain ⟨v,hv⟩:=ramified_arithmetic_support h u n hn hA
  refine ⟨Ideal.absNorm (Ideal.span {v}),?_⟩
  calc
    9*Ideal.absNorm (Ideal.span {h})=Ideal.absNorm (Ideal.span {(3:Eis)*h}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm]
    _=Ideal.absNorm (Ideal.span {(u.val*lambda^n)*v}):=by rw [hv]
    _=3^n*Ideal.absNorm (Ideal.span {v}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,ramifiedElement_absNorm]

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

lemma arithmeticDirichlet_support_nonzero (s : ℂ) (h : Eis) :
    Function.support (arithmeticDirichletTerm s h)⊆{c : LevelLower | c.1≠0} := by
  intro c hc
  change arithmeticDirichletTerm s h c≠0 at hc
  intro hz
  exact hc (by simp only [arithmeticDirichletTerm,hz,ite_true])

theorem arithmeticDirichletSeries_ramified_reindex (s : ℂ) (hs : 2<s.re) (h : Eis) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑'n:ℕ,∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  have hsum:Summable (arithmeticDirichletTerm s h):=(arithmeticDirichletTerm_summable_norm s hs h).of_norm
  have hsub:Summable (fun c:NonzeroLevelLower=>arithmeticDirichletTerm s h c.1):=hsum.subtype _
  have hp:=ramifiedLowerEquiv.summable_iff.mpr hsub
  change Summable (fun p:Eisˣ×ℕ×GoodIdeal=>arithmeticDirichletTerm s h (ramifiedLowerMap p).1) at hp
  calc
    _=∑'c:NonzeroLevelLower,arithmeticDirichletTerm s h c.1:=
      (tsum_subtype_eq_of_support_subset (arithmeticDirichlet_support_nonzero s h)).symm
    _=∑'p:Eisˣ×ℕ×GoodIdeal,arithmeticDirichletTerm s h (ramifiedLowerMap p).1:=
      (ramifiedLowerEquiv.tsum_eq _).symm
    _=_:=by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro u
      exact (hp.prod_factor u).tsum_prod


end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicUnitGaussSum_phase_shift (h a b : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (hab : IsCoprime (3*a) b) :
    eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*cubicUnitGaussSum h b=
      cubicUnitGaussSum (h*(9*a)) b := by
  have hbt : IsCoprime b (9*a):=by
    rw [show (9:Eis)*a=3*(3*a) by ring]
    exact (primary_coprime_three b hbprimary).mul_right hab.symm
  have heig:=cubicUnitGaussSum_frequency_twist h b (9*a) hb hbprimary hbt
  have hs : symbol a b*symbol (3*a) b*symbol (9*a) b=1 := by
    calc
      _=symbol (a*(3*a)*(9*a)) b:=by
        symm
        calc
          _=symbol (a*(3*a)) b*symbol (9*a) b:=
            symbol_mul_numerator _ _ b hbprimary
          _=_:=by rw [symbol_mul_numerator a (3*a) b hbprimary]
      _=symbol ((3*a)^3) b:=by congr 1; ring
      _=(symbol (3*a) b)^3:=symbol_pow_numerator _ _ hbprimary 3
      _=1:=symbol_cube_of_isCoprime _ _ hbprimary hab
  have he : eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
      eisEmbedding (symbol (9*a) b)=1:=by
    simpa only [map_mul,map_one] using congrArg eisEmbedding hs
  calc
    _=(eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b))*
        (eisEmbedding (symbol (9*a) b)*cubicUnitGaussSum (h*(9*a)) b):=by rw [heig]
    _=(eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        eisEmbedding (symbol (9*a) b))*cubicUnitGaussSum (h*(9*a)) b:=by ring
    _=_:=by rw [he,one_mul]

def unramifiedCubicGaussSeries (s : ℂ) (h : Eis) : ℂ:=
  ∑'I:GoodIdeal,(Ideal.absNorm I.1:ℂ)^(-s)*cubicUnitGaussSum h (primaryGenerator I.1)


end

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicUnitGaussSum_cube_shift (h b t : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (hbt : IsCoprime b t) :
    cubicUnitGaussSum (h*t^3) b=cubicUnitGaussSum h b := by
  have heig:=cubicUnitGaussSum_frequency_twist h b (t^3) hb hbprimary hbt.pow_right
  have hs : symbol (t^3) b=1:=by
    rw [symbol_pow_numerator t b hbprimary 3]
    exact symbol_cube_of_isCoprime t b hbprimary hbt.symm
  simpa only [hs,map_one,one_mul] using heig

theorem unramifiedCubicGaussSeries_neg (s : ℂ) (h : Eis) :
    unramifiedCubicGaussSeries s (-h)=unramifiedCubicGaussSeries s h := by
  apply tsum_congr
  intro I
  congr 1
  have hc : IsCoprime (primaryGenerator I.1) (-1:Eis):=⟨0,-1,by ring⟩
  simpa only [show (-1:Eis)^3=-1 by ring,mul_neg_one] using cubicUnitGaussSum_cube_shift h (primaryGenerator I.1) (-1) I.2
    (primaryGenerator_spec I.1 I.2).2 hc

theorem unramifiedCubicGaussSeries_lambda_pow (s : ℂ) (h : Eis) (n : ℕ) :
    unramifiedCubicGaussSeries s (h*lambda^n)=
      unramifiedCubicGaussSeries s (h*lambda^(n%3)) := by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  have hl:IsCoprime lambda (primaryGenerator I.1):=
    coprime_of_dvd_sub_one lambda _ ((show lambda∣lambda^2 from ⟨lambda,by ring⟩).trans hp)
  have he:lambda^n=lambda^(n%3)*(lambda^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.2 hp hl.symm.pow_right

theorem unramifiedCubicGaussSeries_lambda_cube (s : ℂ) (h : Eis) :
    unramifiedCubicGaussSeries s (h*lambda^3)=unramifiedCubicGaussSeries s h := by
  simpa using unramifiedCubicGaussSeries_lambda_pow s h 3

theorem unit_eq_sign_omega (u : Eisˣ) :
    ∃j:Fin 3,(u:Eis)=omega^j.val ∨ (u:Eis)=-(omega^j.val) := by
  let ζ:=IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η:Eisˣ:=(ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη:(η:Eis)=omega:=rfl
  have hlist:u∈([1,-1,η,-η,η^2,-η^2]:List Eisˣ):=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h|h|h|h|h|h
  · exact ⟨0,Or.inl (by simp [h])⟩
  · exact ⟨0,Or.inr (by simp [h])⟩
  · exact ⟨1,Or.inl (by simp [h,hη])⟩
  · exact ⟨1,Or.inr (by simp [h,hη])⟩
  · exact ⟨2,Or.inl (by simp only [h,Units.val_pow_eq_pow_val,hη];rfl)⟩
  · exact ⟨2,Or.inr (by simp only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη];rfl)⟩

theorem unramifiedCubicGaussSeries_nine_family (h : Eis) (u : Eisˣ) (n : ℕ) :
    ∃j k:Fin 3,∀s:ℂ,
      unramifiedCubicGaussSeries s (h*(9*((u:Eis)*lambda^n)))=
        unramifiedCubicGaussSeries s (h*omega^j.val*lambda^k.val) := by
  have hl:lambda^2=-3*omega:=by
    have hw:omega^2=-omega-1:=by
      have h3:omega^3=1:=omega_primitive.pow_eq_one
      have h1:omega≠1:=omega_primitive.ne_one (by decide)
      have hp:(omega-1)*(omega^2+omega+1)=0:=by linear_combination h3
      have hz:omega^2+omega+1=0:=(mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h1)
      linear_combination hz
    change (omega-1)^2=-3*omega
    linear_combination hw
  have h9:(9:Eis)=omega*lambda^4:=by
    calc
      _=9*omega^3:=by rw [omega_primitive.pow_eq_one];ring
      _=omega*((-3*omega)^2):=by ring
      _=omega*((lambda^2)^2):=by rw [hl]
      _=omega*lambda^4:=by ring
  let ζ:=IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η:Eisˣ:=(ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη:(η:Eis)=omega:=rfl
  obtain ⟨j,hj⟩:=unit_eq_sign_omega (η*u)
  refine ⟨j,⟨(n+4)%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro s
  have he:h*(9*((u:Eis)*lambda^n))=(h*((η*u:Eisˣ):Eis))*lambda^(n+4):=by
    rw [h9,Units.val_mul,hη,pow_add]
    ring
  rw [he,unramifiedCubicGaussSeries_lambda_pow]
  rcases hj with hj|hj
  · rw [hj]
  · rw [hj]
    simpa only [mul_neg,neg_mul] using
      unramifiedCubicGaussSeries_neg s (h*omega^j.val*lambda^((n+4)%3))

end CubicEisenstein

end

end OAI

end


