-- Prove2me | Definitions.Def_OAIHecke78B013
-- name    : OAIHecke78B013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T00:23:14.444272+00:00
-- url     : https://prove2.me/theorems/0fbe5597-357a-495b-88d1-4b270b18db56
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 14 of 29
-- statement:
--   Definitions bundle 14 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B011` of this split, and through them their definitions.
--
--   Modules: `Eisenstein.RamifiedGaussSeries`, `Eisenstein.ResidualFourierBounds`, `Eisenstein.ResidualFourierSeries`, `Eisenstein.SourceProjection`, `Eisenstein.ScatteringResidues`, `Eisenstein.SourceQuotient`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B011

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedGaussSeries
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
  convert (preTransparency := .instances) dvd_add hd (show (3:Eis)∣9*w from ⟨3*w,by ring⟩) using 1 ; ring

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
  convert (preTransparency := .instances) hp w using 1
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

theorem arithmeticResidueSum_ramified_split (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1) :
    arithmeticResidueSum h ((u.val*lambda^n)*b)=
      eisEmbedding (symbol (u.val*lambda^n) b)*
      eisEmbedding (symbol (3*(u.val*lambda^n)) b)*
      arithmeticResidueSum h (u.val*lambda^n)*cubicUnitGaussSum h b :=
  arithmeticResidueSum_coprime_product h _ b (ramifiedElement_ne_zero u n)
    (primary_ne_zero b hb) (ramifiedElement_level u n hn) hb (ramified_primary_coprime u n b hb)

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
  norm_num [ShortDraftLatticeCount.q]

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

theorem arithmeticResidueSum_ramified_index_bound (h : Eis) (hh : h≠0)
    (u : Eisˣ) (n : ℕ) (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1)
    (hA : arithmeticResidueSum h ((u.val*lambda^n)*b)≠0) :
    n≤ ramifiedFrequencyBound h := by
  have ha:arithmeticResidueSum h (u.val*lambda^n)≠0:=by
    intro hz
    apply hA
    rw [arithmeticResidueSum_ramified_split h u n hn b hb,hz,mul_zero,zero_mul]
  exact Nat.le_log_of_pow_le (by decide) (ramified_arithmetic_norm_bound h hh u n hn ha)

theorem arithmeticDirichletTerm_ramified_vanish (s : ℂ) (h : Eis) (hh : h≠0)
    (u : Eisˣ) (n : ℕ) (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1)
    (hout : ramifiedFrequencyBound h<n) :
    arithmeticDirichletTerm s h
      ⟨(u.val*lambda^n)*b,dvd_mul_of_dvd_left (ramifiedElement_level u n hn) b⟩=0 := by
  have hA:arithmeticResidueSum h ((u.val*lambda^n)*b)=0:=by
    by_contra hA
    exact (not_le_of_gt hout) (arithmeticResidueSum_ramified_index_bound h hh u n hn b hb hA)
  simp only [arithmeticDirichletTerm,hA,mul_zero,ite_self]

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
    change (Ideal.span {lambda}:Ideal Eis)^2 ∣ _
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

theorem arithmeticDirichletSeries_finite_ramified (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs h]
  apply tsum_congr
  intro u
  apply tsum_eq_sum
  intro n hn
  have hout:ramifiedFrequencyBound h<n+2:=by
    have hh':¬n< ramifiedFrequencyBound h+1:=by simpa only [Finset.mem_range] using hn
    omega
  have hzero (I:GoodIdeal) : arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1=0 :=
    arithmeticDirichletTerm_ramified_vanish s h hh u (n+2) (by omega)
      (primaryGenerator I.1) (primaryGenerator_spec I.1 I.2).2 hout
  simp only [hzero,tsum_zero]

theorem arithmeticDirichletSeries_gauss_expansion (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),∑'I:GoodIdeal,
        ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
          (eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
           eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
           arithmeticResidueSum h (u.val*lambda^(n+2))*cubicUnitGaussSum h (primaryGenerator I.1)) := by
  rw [arithmeticDirichletSeries_finite_ramified s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  apply tsum_congr
  intro I
  rw [arithmeticDirichletTerm, if_neg (ramifiedLowerMap (u,n,I)).2]
  dsimp only [ramifiedLowerMap]
  congr 1
  exact arithmeticResidueSum_ramified_split h u (n+2) (by omega)
    (primaryGenerator I.1) (primaryGenerator_spec I.1 I.2).2

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

theorem arithmeticDirichletSeries_unramified_gauss (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*arithmeticResidueSum h (u.val*lambda^(n+2))*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))) := by
  rw [arithmeticDirichletSeries_gauss_expansion s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,Complex.ofReal_natCast,ramifiedLower_span,
    map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [←cubicUnitGaussSum_phase_shift h (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)]
  ring

theorem scatteringCoefficient_unramified_gauss (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    scatteringCoefficient s h=
      (∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*arithmeticResidueSum h (u.val*lambda^(n+2))*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient,arithmeticDirichletSeries_unramified_gauss s hs h hh]

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

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierBounds
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspHeightFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  let := cuspPeriodStripFiniteVolume a b ha
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

def cuspHeightFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : CuspHeightStripL2 a b :=
  (cuspHeightFourierTest_memLp a b ha ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))

def kernelCuspHeightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspHeightFourierTestL2 a b ha ρ h)).comp (kernelCuspHeightPullback a b ha)

lemma kernelCuspHeightFourier_integral (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h F=∫w in cuspPeriodStrip a b,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h),
    kernelCuspHeightPullback_ae a b ha F] with w hw hp
  rw [RCLike.inner_apply,cuspHeightFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspHeightFourier_restrict (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h (kernelMassRestrictionCLM (cuspHeightQuotientCompact a b)
      (cuspHeightQuotientCompact_isCompact a b ha).measurableSet F)=kernelCuspHeightFourier a b ha ρ h F := by
  rw [kernelCuspHeightFourier_integral,kernelCuspHeightFourier_integral]
  have he := (kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp
    (kernelMassRestriction_coe (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩) _))

def kernelCuspHeightFourierFamily (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspHeightFourier a b ha ρ h
    (kernelLocalCorrectedSeed (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha)
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspHeightFourierFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspHeightFourierFamily a b ha ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspHeightFourier a b ha ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal (cuspHeightQuotientCompact a b)
        (cuspHeightQuotientCompact_isCompact a b ha) 2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma kernelCuspHeightFourierFamily_residue_limit (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspHeightFourierFamily a b ha ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspHeightFourier a b ha ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspHeightFourier_restrict,
    kernelCuspHeightFourierFamily] using hh

lemma kernelCuspHeightFourierFamily_initial (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ h s=∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspHeightFourierFamily,kernelCuspHeightFourier_integral]
  have he := (kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (cuspHeightQuotientCompact a b)
      (cuspHeightQuotientCompact_isCompact a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]

def cuspIntervalWhittakerHeightFactor (a b : ℝ)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc a b,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))

lemma hyperbolicEisenstein_cusp_height_fourier_nonzero (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  have hexp : ∀v∈Set.Icc a b,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := ha.trans_le hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,if_neg hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc a b,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _

lemma kernelCuspHeightFourierFamily_initial_factor (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  rw [kernelCuspHeightFourierFamily_initial a b ha ρ h s hs hi,
    hyperbolicEisenstein_cusp_height_fourier_nonzero a b ha ρ s (by linarith) h hh]

lemma cuspIntervalWhittakerHeightFactor_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspIntervalWhittakerHeightFactor a b ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  have heq : (fun s => cuspIntervalWhittakerHeightFactor a b ρ s h)=
      (fun s => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (mul_assoc _ _ _).symm)
  rw [heq]
  exact cuspWeightedWhittakerInterval_differentiableAt ρ a b ha (cuspFrequency h) w hw

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma kernelCuspHeightFourierFamily_cross_identity (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (kernelCuspHeightFourierFamily_analyticAt_nonreal a b ha ρ h s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) domain := by
    intro s hs
    exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
          cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [kernelCuspHeightFourierFamily_initial_factor a b ha ρ h hh s hs.1 hs.2,
      kernelCuspFourierFamily_eq_upper h hh ⟨by linarith [hs.1],hs.2⟩]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma kernelCuspHeightFourier_residue_factor (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*nonzeroScatteringResidue h*
        cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hbase : Tendsto (fun s : ℂ => cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) h)) :=
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => cuspIntervalWhittakerHeightFactor a b ρ s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h)) :=
    (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((kernelCuspHeightFourierFamily_residue_limit a b ha ρ h).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspHeightFourierFamily a b ha ρ h ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
        ((4/3:ℂ)+(t:ℂ)*Complex.I))*cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := kernelCuspHeightFourierFamily_cross_identity a b ha ρ h hh hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      kernelCuspFourier h cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hH := cuspWhittakerHeightFactor_center_ne_zero h
  calc
    _ = (kernelCuspFourier h cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h)/
        cuspWhittakerHeightFactor (4/3:ℂ) h := (eq_div_iff hH).mpr heq
    _ = _ := by
      unfold nonzeroScatteringResidue
      field_simp [cusp_volume_ne_zero,hH]

lemma cuspIntervalWhittakerHeightFactor_center_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h=
      cubicBesselNormalizer h*(∫v in Set.Icc a b,
        ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  dsimp only
  rw [sourceFourierKernel_cubic_height h hh v hpos]
  ring

lemma kernelCuspHeightFourier_residue_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFourierCoefficient h*
        (∫v in Set.Icc a b,ρ v*
          (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [kernelCuspHeightFourier_residue_factor a b ha ρ h hh,
    cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,cubicResidualFourierCoefficient]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma kernelCuspHeightFourier_uniform_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(ρ : BoundedContinuousFunction ℝ ℂ)(h : ActualEisensteinCubic.O)(F : KernelQuotientL2),
      ‖kernelCuspHeightFourier a b ha ρ h F‖≤C*‖ρ‖*‖F‖ := by
  let := cuspPeriodStripFiniteVolume a b ha
  let mass : ℝ := (measureUnivNNReal (hyperbolicVolume.restrict (cuspPeriodStrip a b)):ℝ)^((2:ℝ≥0∞).toReal)⁻¹
  have hmass : 0≤ mass := Real.rpow_nonneg (by positivity) _
  refine ⟨mass*‖kernelCuspHeightPullback a b ha‖,mul_nonneg hmass (norm_nonneg _),?_⟩
  intro ρ h F
  have htest : ‖cuspHeightFourierTestL2 a b ha ρ h‖≤ mass*‖ρ‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg ρ)
    filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h)] with w hw
    change ‖cuspHeightFourierTestL2 a b ha ρ h w‖≤‖ρ‖
    rw [cuspHeightFourierTestL2,hw,norm_star]
    exact cuspWeightedFourierPhase_bound ρ h w
  change ‖inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)‖≤_
  calc
    _ ≤ ‖cuspHeightFourierTestL2 a b ha ρ h‖*‖kernelCuspHeightPullback a b ha F‖ := norm_inner_le_norm _ _
    _ ≤ (mass*‖ρ‖)*(‖kernelCuspHeightPullback a b ha‖*‖F‖) :=
      mul_le_mul htest ((kernelCuspHeightPullback a b ha).le_opNorm F) (norm_nonneg _)
        (mul_nonneg hmass (norm_nonneg _))
    _ = _ := by ring

lemma cubicResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖cubicResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖cubicEisensteinResidue‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelCuspHeightFourier_residue_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h cubicEisensteinResidue
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

def cubicBesselDensity (x t : ℝ) : ℝ :=
  t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t))

lemma cubicBesselDensity_integrable (x : ℝ) :
    IntegrableOn (cubicBesselDensity x) (Set.Ioi 0) := by
  have hi := (schlafliIntegral_integrable (1/3:ℂ) x (by norm_num)).re
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
    schlafliIntegrand_real (1/3) x t ht]
  change t^((1/3:ℝ)-1)*Real.exp (-t-x^2/(4*t))=cubicBesselDensity x t
  norm_num [cubicBesselDensity]

lemma cubicBesselDensity_nonneg (x t : ℝ) (ht : 0≤t) : 0≤ cubicBesselDensity x t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

lemma schlafliIntegral_cubic_real (x : ℝ) :
    schlafliIntegral (1/3:ℂ) x=((∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t):ℝ) := by
  unfold schlafliIntegral
  calc
    _ = ∫t in Set.Ioi (0:ℝ),((cubicBesselDensity x t:ℝ):ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
        schlafliIntegrand_real (1/3) x t ht]
      norm_num [cubicBesselDensity]
    _ = _ := integral_ofReal

lemma schlafliBesselK_cubic_real (x : ℝ) (hx : 0<x) :
    schlafliBesselK (1/3:ℂ) x=
      (((1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)):ℝ) := by
  rw [schlafliBesselK,schlafliIntegral_cubic_real]
  have hp := Complex.ofReal_cpow (show 0≤x/2 by positivity) (-(1:ℝ)/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat,neg_div] at hp
  rw [←hp]
  push_cast
  ring_nf

lemma schlafliBesselK_cubic_norm_re (x : ℝ) (hx : 0<x) :
    ‖schlafliBesselK (1/3:ℂ) x‖=(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  apply Complex.norm_of_nonneg
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicBesselDensity_nonneg x t ht.le

lemma cubicBesselDensity_upper (x t : ℝ) (ht : 0<t) :
    cubicBesselDensity x t≤Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hq : -t-x^2/(4*t)≤-x/2-t/2 := by
    have hf : x/2-t/2≤x^2/(4*t) :=
      (le_div_iff₀ (show 0<4*t by positivity)).mpr (by
        nlinarith [sq_nonneg (t-x),sq_nonneg t])
    linarith
  have he := Real.exp_le_exp.mpr hq
  unfold cubicBesselDensity
  calc
    _ ≤ t^(-(2:ℝ)/3)*Real.exp (-x/2-t/2) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring_nf

lemma cubicBesselIntegral_upper (x : ℝ) :
    (∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2:ℝ)/3) (p := (1:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,show ∀t : ℝ,-(1/2)*t=-t/2 by intro t;ring] using h
  have hb := setIntegral_mono_on (cubicBesselDensity_integrable x)
    (hi.const_mul (Real.exp (-x/2))) measurableSet_Ioi (fun t ht => cubicBesselDensity_upper x t ht)
  rw [integral_const_mul] at hb
  have he : (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    convert (preTransparency := .instances) hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf
  rw [he] at hb
  exact hb

lemma cubicBesselDensity_lower (x t : ℝ) (hx : 0<x) (ht : t∈Set.Icc x (2*x)) :
    (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)≤ cubicBesselDensity x t := by
  have htp : 0<t := hx.trans_le ht.1
  have hp : (2*x)^(-(2:ℝ)/3)≤t^(-(2:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos htp ht.2 (by norm_num)
  have hfrac : x^2/(4*t)≤x/4 :=
    (div_le_iff₀ (show 0<4*t by positivity)).mpr (by nlinarith [ht.1])
  have he : Real.exp (-9*x/4)≤Real.exp (-t-x^2/(4*t)) :=
    Real.exp_le_exp.mpr (by linarith [ht.2])
  exact mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg htp.le _)

lemma cubicBesselIntegral_lower (x : ℝ) (hx : 0<x) :
    x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
  have hsub : Set.Icc x (2*x)⊆Set.Ioi (0:ℝ) := fun t ht => hx.trans_le ht.1
  have hi := cubicBesselDensity_integrable x
  have hr := hi.mono_set hsub
  have hconstant : IntegrableOn (fun _ : ℝ => (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))
      (Set.Icc x (2*x)) := integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hmono := setIntegral_mono_on hconstant hr measurableSet_Icc
    (fun t ht => cubicBesselDensity_lower x t hx ht)
  have hextend : (∫t in Set.Icc x (2*x),cubicBesselDensity x t)≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensity_nonneg x t ht.le
    · exact Eventually.of_forall hsub
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith),smul_eq_mul,
    show 2*x-x=x by ring] at hmono
  exact hmono.trans hextend

def cubicBesselLowerConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*(2:ℝ)^(-(2:ℝ)/3)

lemma cubicBesselLowerConstant_pos : 0<cubicBesselLowerConstant := by
  unfold cubicBesselLowerConstant
  positivity

theorem schlafliBesselK_cubic_lower (x : ℝ) (hx : 0<x) :
    cubicBesselLowerConstant*Real.exp (-9*x/4)≤(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  have hp := mul_le_mul_of_nonneg_left (cubicBesselIntegral_lower x hx)
    (show 0≤(1/2:ℝ)*(x/2)^(-(1:ℝ)/3) by positivity)
  have hnorm : (x/2)^(-(1:ℝ)/3)=(1/2:ℝ)^(-(1:ℝ)/3)*x^(-(1:ℝ)/3) := by
    rw [show x/2=(1/2:ℝ)*x by ring,Real.mul_rpow (by norm_num) hx.le]
  have htwo : (2*x)^(-(2:ℝ)/3)=(2:ℝ)^(-(2:ℝ)/3)*x^(-(2:ℝ)/3) :=
    Real.mul_rpow (by norm_num) hx.le
  have hxp : x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3)=1 := by
    calc
      _ = x^(-(1:ℝ)/3)*x^(1:ℝ)*x^(-(2:ℝ)/3) := by rw [Real.rpow_one]
      _ = x^((-(1:ℝ)/3+1)+(-(2:ℝ)/3)) := by rw [←Real.rpow_add hx,←Real.rpow_add hx]
      _ = 1 := by norm_num
  have he : (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)))=
      cubicBesselLowerConstant*Real.exp (-9*x/4) := by
    rw [hnorm,htwo]
    calc
      _ = cubicBesselLowerConstant*(x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3))*Real.exp (-9*x/4) := by
        unfold cubicBesselLowerConstant
        ring
      _ = _ := by rw [hxp,mul_one]
  rwa [he] at hp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma exp_neg_mul_le_inverse_cube (ε r : ℝ) (hε : 0<ε) (hr : 0< r) :
    Real.exp (-ε*r)≤(6/ε^3)*r^(-3:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp (ε*r) (le_of_lt (mul_pos hε hr)) 3
  norm_num only [Nat.factorial] at hp
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(ε*r)^3/6) hp
  rw [one_div,←Real.exp_neg] at hi
  rw [Real.rpow_neg hr.le]
  norm_num only [Real.rpow_ofNat]
  have halg : (6/ε^3)*(r^3)⁻¹=((ε*r)^3/6)⁻¹ := by
    field_simp
  rw [halg]
  simpa only [neg_mul,one_div] using hi

lemma summable_exp_neg_embedding_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖ConcreteTraceCRT.eisEmbedding h‖)) := by
  have hs := (summable_embedding_rpow (-3) (by norm_num)).mul_left (6/ε^3)
  have hz : Summable (fun h : ActualEisensteinCubic.O => if h=0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq 0 (1:ℝ)).summable
  apply Summable.of_nonneg_of_le (fun h => (Real.exp_pos _).le) _ (hz.add hs)
  intro h
  by_cases hh : h=0
  · subst h
    norm_num [Pi.add_apply]
  · have hp : 0<‖ConcreteTraceCRT.eisEmbedding h‖ :=
      norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh)
    simpa only [Pi.add_apply,if_neg hh,zero_add] using exp_neg_mul_le_inverse_cube ε _ hε hp

lemma summable_exp_neg_cuspFrequency_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖cuspFrequency h‖)) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := by
    apply norm_pos_iff.mpr
    exact mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero
  have hs := summable_exp_neg_embedding_norm (ε/‖(3:ℂ)*ConcreteTraceCRT.eisLam‖) (div_pos hε hd)
  apply hs.congr
  intro h
  congr 1
  rw [cuspFrequency,norm_div]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselNormalizer_ne_zero (h : ActualEisensteinCubic.O) (hh : h≠0) : cubicBesselNormalizer h≠0 := by
  unfold cubicBesselNormalizer
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  · apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh)))

lemma cubicBesselHeight_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    IntegrableOn (fun v : ℝ => schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)
      (Set.Icc a b) volume := by
  have hsource : IntegrableOn (fun v : ℝ => (v:ℂ)^(-(4/3:ℂ)-1)*
      sourceFourierKernel (4/3) (cuspFrequency h*v)) (Set.Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    intro v hv
    have hpos := ha.trans_le hv.1
    exact ((Complex.continuousAt_ofReal_cpow_const v (-(4/3:ℂ)-1) (Or.inr hpos.ne')).mul
      ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
        ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt
  apply (hsource.div_const (cubicBesselNormalizer h)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  apply (div_eq_iff (cubicBesselNormalizer_ne_zero h hh)).mpr
  simpa only [mul_comm] using sourceFourierKernel_cubic_height h hh v (ha.trans_le hv.1)

lemma cubicBesselHeight_average_lower (a b : ℝ) (ha : 0<a) (hab : a<b) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ((b-a)*cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
      ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖ := by
  have hb : 0<b := ha.trans hab
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  let lower : ℝ := (cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)
  have hi := cubicBesselHeight_integrable a b ha h hh
  have hpoint (v : ℝ) (hv : v∈Set.Icc a b) : lower≤
      RCLike.re (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
    have hvp := ha.trans_le hv.1
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v := by positivity
    have hK := schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx
    have he : Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        Real.exp (-9*(4*Real.pi*‖cuspFrequency h‖*v)/4) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hv.2
        (show 0≤9*Real.pi*‖cuspFrequency h‖ by positivity)
      nlinarith [hmul]
    have hnum : cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)).re :=
      (mul_le_mul_of_nonneg_left he cubicBesselLowerConstant_pos.le).trans hK
    have hden : v^2≤b^2 := sq_le_sq₀ hvp.le hb.le |>.mpr hv.2
    change lower≤Complex.re (_/(v:ℂ)^2)
    rw [←Complex.ofReal_pow,Complex.div_ofReal_re]
    calc
      lower = (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/b^2 := by dsimp [lower]; ring
      _ ≤ (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/v^2 :=
        div_le_div_of_nonneg_left (mul_nonneg cubicBesselLowerConstant_pos.le (Real.exp_pos _).le)
          (sq_pos_of_pos hvp) hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg v)
  have hmono := setIntegral_mono_on
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top) : IntegrableOn (fun _ : ℝ => lower) (Set.Icc a b))
    hi.re measurableSet_Icc hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le hab.le,smul_eq_mul] at hmono
  have hreal : (∫v in Set.Icc a b,RCLike.re
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2))=
      Complex.re (∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) :=
    integral_re hi
  rw [hreal] at hmono
  have hfinal := hmono.trans (Complex.re_le_norm _)
  convert (preTransparency := .instances) hfinal using 1 ; dsimp [lower] ; ring

lemma cubicResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖cubicResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := cubicResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (cubicResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierSeries
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspFrequency_norm_lower (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹≤‖cuspFrequency h‖ := by
  have hn : 1≤‖ConcreteTraceCRT.eisEmbedding h‖^2 := by
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hh))
  have hnorm : 1≤‖ConcreteTraceCRT.eisEmbedding h‖ := by nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding h)]
  rw [cuspFrequency,norm_div,inv_eq_one_div]
  exact div_le_div_of_nonneg_right hnorm (norm_nonneg _)

def cubicBesselUpperAway (deltaLoss : ℝ) : ℝ :=
  (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperAway_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) : 0<cubicBesselUpperAway deltaLoss := by
  unfold cubicBesselUpperAway
  positivity

lemma schlafliBesselK_cubic_upper_away (deltaLoss x : ℝ) (hδ : 0<deltaLoss) (hx : deltaLoss≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤ cubicBesselUpperAway deltaLoss*Real.exp (-x/2) := by
  have hxp := hδ.trans_le hx
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  have hp : (x/2)^(-(1:ℝ)/3)≤(deltaLoss/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperAway;ring

def cubicResidualNonzeroTerm (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else nonzeroScatteringResidue h*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

lemma cubicResidualNonzeroTerm_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicResidualNonzeroTerm h (v,z)=cubicResidualFourierCoefficient h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicResidualNonzeroTerm,if_neg hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^3*(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ) := by
    rw [←Complex.cpow_ofNat (v:ℂ) 3,←Complex.cpow_add _ _ hv0]
    congr 1
    ring
  have hker := sourceFourierKernel_cubic_height h hh v hv
  calc
    _ = nonzeroScatteringResidue h*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [hker,cubicResidualFourierCoefficient]
      field_simp

lemma cubicResidualNonzeroTerm_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (cubicResidualNonzeroTerm h) {p : ℝ × ℂ | 0<p.1} := by
  unfold cubicResidualNonzeroTerm
  by_cases hh : h=0
  · simp only [if_pos hh]
    exact continuousOn_const
  simp only [if_neg hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

lemma cubicResidualNonzeroTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖cubicResidualNonzeroTerm h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let deltaLoss : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hδ : 0<deltaLoss := by dsimp [deltaLoss];positivity
  have hCu : 0<cubicBesselUpperAway deltaLoss := cubicBesselUpperAway_pos deltaLoss hδ
  obtain ⟨C,hC,hcoeff⟩ := cubicResidualFourierCoefficient_subexponential (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway deltaLoss,mul_nonneg (mul_nonneg hC hb.le) (cubicBesselUpperAway_pos deltaLoss hδ).le,?_⟩
  intro h p hp
  have hv : 0<p.1 := ha.trans_le hp.1
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,if_pos hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : deltaLoss≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1
      ha.le (norm_nonneg (cuspFrequency h))
    dsimp [deltaLoss]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [show p=(p.1,p.2) from rfl,cubicResidualNonzeroTerm_bessel h hh _ hv,
    norm_mul,norm_mul,norm_mul,breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  have hkb := schlafliBesselK_cubic_upper_away deltaLoss (4*Real.pi*‖cuspFrequency h‖*p.1) hδ hx
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway deltaLoss*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (mul_nonneg hC (Real.exp_pos _).le))
        hkb (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway deltaLoss)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2 =
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le
      nlinarith

def cubicResidualNonzeroSeries (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,cubicResidualNonzeroTerm h p

lemma cubicResidualNonzeroSeries_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound a b ha hab
  apply continuousOn_tsum (u := fun h : ActualEisensteinCubic.O => C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))
  · intro h
    exact (cubicResidualNonzeroTerm_continuousOn h).mono (fun p hp => ha.trans_le hp.1)
  · exact (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma cubicResidualNonzeroSeries_continuousOn :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | 0<p.1} := by
  intro p hp
  change 0<p.1 at hp
  have hclosed := cubicResidualNonzeroSeries_continuousOn_slab (p.1/2) (2*p.1) (by linarith) (by linarith)
  have hnb : {q : ℝ × ℂ | q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

def cubicResidualNonzeroFunction (w : HyperbolicSpace) : ℂ :=
  cubicResidualNonzeroSeries (hyperbolicHeight w,hyperbolicHorizontal w)

lemma cubicResidualNonzeroFunction_continuous : Continuous cubicResidualNonzeroFunction := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  have hp : (hyperbolicHeight w,hyperbolicHorizontal w)∈{p : ℝ × ℂ | 0<p.1} := hyperbolicHeight_pos w
  exact (cubicResidualNonzeroSeries_continuousOn.continuousAt (hopen.mem_nhds hp)).comp
    (f := fun u : HyperbolicSpace => (hyperbolicHeight u,hyperbolicHorizontal u))
    (hyperbolicHeight_continuous.prodMk hyperbolicHorizontal_continuous).continuousAt

lemma cubicResidualNonzeroSeries_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    cubicResidualNonzeroSeries (v,z+3*ConcreteTraceCRT.eisEmbedding n)=cubicResidualNonzeroSeries (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,if_pos hh]
  simp only [cubicResidualNonzeroTerm,if_neg hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicResidualModeAmplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else cubicResidualFourierCoefficient h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma cubicResidualNonzeroTerm_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    cubicResidualNonzeroTerm h (v,z)=cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,cubicResidualModeAmplitude,if_pos hh,zero_mul]
  · rw [cubicResidualNonzeroTerm_bessel h hh v hv z,cubicResidualModeAmplitude,if_neg hh]

lemma integral_cusp_character_product (h k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  have hphase (z : ℂ) : ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z)=ShortDraftTrace.breveE (-cuspFrequency (k-h)*z) := by
    rw [←AddChar.map_add_eq_mul]
    congr 1
    unfold cuspFrequency
    rw [map_sub]
    ring
  simp_rw [hphase]
  simpa only [sub_eq_zero,eq_comm] using integral_cusp_character (k-h)

lemma cubicResidualNonzeroSeries_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v k := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
    ShortDraftTrace.breveE (-cuspFrequency k*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => cubicResidualModeAmplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*z)+starRingEnd ℂ (cuspFrequency h*z)))*
      Complex.exp (2*Real.pi*Complex.I*((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
    change ‖(cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)‖≤_
    rw [←cubicResidualNonzeroTerm_eq_amplitude v hv h z,norm_mul,breveE_norm,mul_one]
    exact hbound h (v,z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=
      if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v h else 0 := by
    change (∫z in periodDomain,cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=_
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑'h : ActualEisensteinCubic.O,cubicResidualNonzeroTerm h (v,z))*ShortDraftTrace.breveE (-cuspFrequency k*z)=_
        rw [←tsum_mul_right]
        apply tsum_congr
        intro h
        rw [cubicResidualNonzeroTerm_eq_amplitude v hv h z])
    _ = ∑'h : ActualEisensteinCubic.O,∫z in periodDomain,f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑'h : ActualEisensteinCubic.O,if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v h else 0 := tsum_congr hterm
    _ = _ := by simp

end

section
open Filter MeasureTheory
open scoped Classical Topology

lemma ae_eq_of_boundedContinuous_height_tests («μ» : Measure ℝ) (f g : ℝ→ℂ)
    (hf : Integrable f «μ») (hg : Integrable g «μ»)
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x,ρ x*f x∂«μ»)=(∫x,ρ x*g x∂«μ»)) : f=ᵐ[«μ»]g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro test htest hsupp
  obtain ⟨C,hC⟩ := hsupp.exists_bound_of_continuous htest.continuous
  let ρ : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (test x:ℂ))
      (Complex.continuous_ofReal.comp htest.continuous) C (fun x => by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using hC x)
  have hh := heq ρ
  change (∫x,(test x:ℂ)*f x∂«μ»)=(∫x,(test x:ℂ)*g x∂«μ») at hh
  simpa only [Complex.real_smul] using hh

lemma interval_ae_eq_of_boundedContinuous_height_tests (a b : ℝ) (f g : ℝ→ℂ)
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b))
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x in Set.Icc a b,ρ x*f x)=(∫x in Set.Icc a b,ρ x*g x)) :
    f=ᵐ[volume.restrict (Set.Icc a b)]g :=
  ae_eq_of_boundedContinuous_height_tests (volume.restrict (Set.Icc a b)) f g hf hg heq

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def compactHeightMellin (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^s

lemma compactHeightMellin_integrable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    IntegrableOn (fun v : ℝ => ρ v*(v:ℂ)^s) (Set.Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  apply ρ.continuous.continuousOn.mul
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s
    (Or.inr (ha.trans_le hv.1).ne')).continuousWithinAt

theorem compactHeightMellin_differentiable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) : Differentiable ℂ (compactHeightMellin a b ρ) := by
  let heightLog : ℝ→ℂ := fun v => (Real.log (max a v):ℂ)
  have hl : Continuous heightLog := Complex.continuous_ofReal.comp
    ((continuous_const.max continuous_id).log (fun v => (ha.trans_le (le_max_left a v)).ne'))
  let F : ℂ→ℝ→ℂ := fun s v => ρ v*Complex.exp (heightLog v*s)
  let F' : ℂ→ℝ→ℂ := fun s v => ρ v*(Complex.exp (heightLog v*s)*heightLog v)
  have hF : ∀s,Continuous (F s) := fun s => ρ.continuous.mul ((hl.mul_const s).cexp)
  have hF' : Continuous (fun p : ℂ×ℝ => F' p.1 p.2) := by
    exact (ρ.continuous.comp continuous_snd).mul
      ((((hl.comp continuous_snd).mul continuous_fst).cexp).mul (hl.comp continuous_snd))
  have hder : ∀s v,HasDerivAt (fun w => F w v) (F' s v) s := by
    intro s v
    simpa only [F,F',id_eq,mul_one] using
      (((hasDerivAt_id s).const_mul (heightLog v)).cexp).const_mul (ρ v)
  have heq : compactHeightMellin a b ρ=(fun s => ∫v in Set.Icc a b,F s v) := by
    funext s
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only [compactHeightMellin,F,heightLog]
    rw [max_eq_right hv.1,Complex.ofReal_log (ha.trans_le hv.1).le,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne')]
  rw [heq]
  intro s
  obtain ⟨C,hC⟩ := ((isCompact_closedBall s (1:ℝ)).prod (isCompact_Icc : IsCompact (Set.Icc a b))).exists_bound_of_continuousOn hF'.continuousOn
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ»:=volume.restrict (Set.Icc a b)) (F:=F) (F':=F')
    (bound:=fun _ => C) (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun w => (hF w).aestronglyMeasurable))
    ((hF s).continuousOn.integrableOn_Icc)
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv w hw
      exact hC (w,v) ⟨Metric.ball_subset_closedBall hw,hv⟩)
    (integrable_const C)
    (Eventually.of_forall (fun v w _ => hder w v))
  exact hd.2.differentiableAt

lemma compactHeightMellin_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    AnalyticAt ℂ (compactHeightMellin a b ρ) s :=
  (compactHeightMellin_differentiable a b ha ρ).analyticAt s

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

def cuspHeightConstantAverage (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(compactHeightMellin a b ρ (s-3)+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*compactHeightMellin a b ρ (-s-1))

lemma hyperbolicEisenstein_cusp_height_fourier_zero (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ 0 w∂hyperbolicVolume)=
      cuspHeightConstantAverage a b ρ s := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ 0 w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ 0)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  have hexp : ∀v∈Set.Icc a b,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*
          (ρ v*(v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
            (ρ v*(v:ℂ)^(-s-1))) := by
    intro v hv
    have hpos : 0<v := ha.trans_le hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency 0*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency 0*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinConstantCoefficient_formula v hpos s hs]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have hm : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp,hm]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hexp,integral_const_mul,
    integral_add (compactHeightMellin_integrable a b ha ρ _)
      ((compactHeightMellin_integrable a b ha ρ _).const_mul _),integral_const_mul]
  rfl

lemma kernelCuspHeightFourierFamily_zero_initial (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ 0 s=cuspHeightConstantAverage a b ρ s := by
  rw [kernelCuspHeightFourierFamily_initial a b ha ρ 0 s hs hi,
    hyperbolicEisenstein_cusp_height_fourier_zero a b ha ρ s (by linarith)]

def weightedOutgoingConstant (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  kernelCuspHeightFourierFamily a b ha ρ 0 s-
    ((9*Real.sqrt 3/2:ℝ):ℂ)*compactHeightMellin a b ρ (s-3)

def baseOutgoingConstant (s : ℂ) : ℂ :=
  kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s-
    ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspMainHeightFactor s

lemma weightedOutgoingConstant_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 1<s.re) (hi : 0<s.im) :
    AnalyticAt ℂ (weightedOutgoingConstant a b ha ρ) s := by
  exact (kernelCuspHeightFourierFamily_analyticAt_nonreal a b ha ρ 0 s hs.ne' hi.ne').sub
    (analyticAt_const.mul ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl))

lemma baseOutgoingConstant_analyticAt (s : ℂ) (hs : 1<s.re) (hi : 0<s.im) :
    AnalyticAt ℂ baseOutgoingConstant s := by
  have hne : s≠2 := by intro he; subst s; norm_num at hi
  have hmain : AnalyticAt ℂ cuspMainHeightFactor s := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [eventually_ne_nhds hne] with z hz
    exact cuspMainHeightFactor_differentiableAt z hz
  exact (kernelCuspAverageFamily_analyticAt_nonreal 2 3 (by norm_num) (by norm_num)
    s hs.ne' hi.ne').sub (analyticAt_const.mul hmain)

lemma cuspScatterHeightFactor_analyticAt (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ cuspScatterHeightFactor s := by
  have hne : s≠0 := by intro he; subst s; norm_num at hs
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds hne] with z hz
  exact cuspScatterHeightFactor_differentiableAt z hz

lemma weightedOutgoingConstant_cross_identity (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Set.EqOn (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1))
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s) domain := by
    intro s hs
    exact (weightedOutgoingConstant_analyticAt a b ha ρ s hs.1 hs.2).mul
      (cuspScatterHeightFactor_analyticAt s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) domain := by
    intro s hs
    exact (baseOutgoingConstant_analyticAt s hs.1 hs.2).mul
      ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
        (analyticAt_id.neg.sub analyticAt_const) rfl)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
      apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
        s (by linarith [hs.1])
        (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)).trans
      exact hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1])
    rw [weightedOutgoingConstant,baseOutgoingConstant,
      kernelCuspHeightFourierFamily_zero_initial a b ha ρ s hs.1 hs.2,hb,
      cuspHeightConstantAverage,cuspConstantAverage]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection
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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_tsum_comp_addHom {R S : Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ) :
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y := by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

lemma ramified_affine_isUnit (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) : IsUnit (1+3*x) := by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hh:denominatorCondition (u.val*lambda^n) (1+3*d):=
    ramified_denominator_condition u n _ ⟨d,by ring⟩
  simpa only [map_add,map_one,map_mul,map_ofNat] using
    (isUnit_quotient_span_iff _ _).mpr hh.1

def ramifiedAffineEquiv (u:Eisˣ) (n:ℕ) :
    (Eis⧸Ideal.span {u.val*lambda^n})≃AdmissibleResidue (u.val*lambda^n):=
  (Equiv.subtypeUnivEquiv (ramified_affine_isUnit u n)).symm.trans (affineResidueEquiv _)

theorem ramified_arithmetic_affine (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ∑'x:Eis⧸Ideal.span {u.val*lambda^n},
        eisEmbedding (symbol (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x))*
        residueAdditive h (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x) := by
  rw [arithmeticResidueSum,←(ramifiedAffineEquiv u n).tsum_eq]
  apply tsum_congr
  intro x
  let a:=u.val*lambda^n
  let d:=1+3*GaussianShiftedPartition.representative a x
  have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
  have hrep:3*a∣denominatorRep a ((ramifiedAffineEquiv u n) x).val-d:=
    denominatorRep_mk_congr a d
  change eisEmbedding (symbol a (denominatorRep a ((ramifiedAffineEquiv u n) x).val))*
    residueAdditive h a (denominatorRep a ((ramifiedAffineEquiv u n) x).val)=_
  rw [row_symbol_congr_modulus a _ d (ramifiedElement_level u n hn) hd hrep,
    residueAdditive_congr h a _ d (ramifiedElement_ne_zero u n) hrep]

def ramifiedReduction (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    (Eis⧸Ideal.span {u.val*lambda^n})→+*(Eis⧸Ideal.span {(3:Eis)}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
    (ramifiedElement_level u n hn))

lemma ramifiedReduction_surjective (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Function.Surjective (ramifiedReduction u n hn):=
  Ideal.Quotient.factor_surjective _

lemma ramifiedReduction_rep (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) :
    (3:Eis)∣GaussianShiftedPartition.representative (u.val*lambda^n) x-
      GaussianShiftedPartition.representative 3 (ramifiedReduction u n hn x) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec]
  have hh:=congrArg (ramifiedReduction u n hn)
    (GaussianShiftedPartition.representative_spec (u.val*lambda^n) x)
  exact hh

lemma residueAdditive_ramified_scale (h k a d:Eis) (ha:a≠0) (hk:3*h=a*k) :
    residueAdditive h a d=residueAdditive k 3 d := by
  unfold residueAdditive cuspFrequency
  congr 1
  have he:=congrArg eisEmbedding hk
  simp only [map_mul,map_ofNat] at he
  have ha':eisEmbedding a≠0:=eisEmbedding_ne_zero ha
  simp only [map_ofNat]
  field_simp
  linear_combination eisLam⁻¹*eisEmbedding d*he

def ramifiedNineSum (k:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  ∑'x:Eis⧸Ideal.span {(3:Eis)},
    eisEmbedding (symbol (u.val*lambda^n)
      (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)

lemma ramifiedReduction_kernel_card (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker=3^(n-2) := by
  have hc:=card_ring_eq_card_mul_kernel (ramifiedReduction u n hn)
    (ramifiedReduction_surjective u n hn)
  change Ideal.absNorm (Ideal.span {u.val*lambda^n})=
    Ideal.absNorm (Ideal.span {(3:Eis)})*Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker at hc
  rw [ramifiedElement_absNorm,three_absNorm] at hc
  have hn':n=2+(n-2):=by omega
  have hp:(3:ℕ)^n=9*3^(n-2):=by
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  omega

theorem ramified_arithmetic_nine_sum (h k:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ((3^(n-2):ℕ):ℂ)*ramifiedNineSum k u n := by
  let a:=u.val*lambda^n
  let f:=ramifiedReduction u n hn
  let F:Eis⧸Ideal.span {(3:Eis)}→ℂ:=fun x=>
    eisEmbedding (symbol a (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)
  have hpoint (x:Eis⧸Ideal.span {a}):
      eisEmbedding (symbol a (1+3*GaussianShiftedPartition.representative a x))*
        residueAdditive h a (1+3*GaussianShiftedPartition.representative a x)=F (f x):=by
    let d:=1+3*GaussianShiftedPartition.representative a x
    let e:=1+3*GaussianShiftedPartition.representative 3 (f x)
    have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
    have he:(3:Eis)∣e-1:=⟨_,by dsimp [e];ring⟩
    have h9:(9:Eis)∣d-e:=by
      obtain ⟨w,hw⟩:=ramifiedReduction_rep u n hn x
      exact ⟨w,by dsimp [d,e,f,a] at *;linear_combination 3*hw⟩
    change eisEmbedding (symbol a d)*residueAdditive h a d=F (f x)
    rw [ramified_symbol_congr_mod_nine u n d e hd he h9,
      residueAdditive_ramified_scale h k a d (ramifiedElement_ne_zero u n) hk,
      residueAdditive_congr k 3 d e (by norm_num) (by convert (preTransparency := .instances) h9 using 1 ;norm_num)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span (ramifiedElement_ne_zero u n)
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  rw [ramified_arithmetic_affine h u n hn]
  calc
    _=∑'x:Eis⧸Ideal.span {a},F (f x):=tsum_congr hpoint
    _=(Nat.card f.toAddMonoidHom.ker:ℂ)*∑'x,F x:=
      finite_tsum_comp_addHom f.toAddMonoidHom (ramifiedReduction_surjective u n hn) F
    _=_:=by rw [ramifiedReduction_kernel_card u n hn];rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedLinearChar (u:Eisˣ) (n:ℕ):AddChar Eis ℂ where
  toFun x:=eisEmbedding (symbol (u.val*lambda^n) (1+3*x))
  map_zero_eq_one':=by simp
  map_add_eq_mul':=by
    intro x y
    have hp (z:Eis):(3:Eis)∣1+3*z-1:=⟨z,by ring⟩
    have hprod:(3:Eis)∣(1+3*x)*(1+3*y)-1:=⟨x+y+3*x*y,by ring⟩
    rw [ramified_symbol_congr_mod_nine u n (1+3*(x+y))
      ((1+3*x)*(1+3*y)) (hp _) hprod ⟨-x*y,by ring⟩,
      symbol_mul_denominator,map_mul]

lemma ramifiedLinearChar_period (u:Eisˣ) (n:ℕ) (x:Eis)
    (hx:x∈Ideal.span {(3:Eis)}) : ramifiedLinearChar u n x=1 := by
  obtain ⟨w,rfl⟩:=Ideal.mem_span_singleton.mp hx
  change eisEmbedding (symbol (u.val*lambda^n) (1+3*(3*w)))=1
  rw [ramified_symbol_congr_mod_nine u n _ 1 ⟨3*w,by ring⟩ (by simp) ⟨w,by ring⟩]
  simp

def ramifiedQuotientChar (u:Eisˣ) (n:ℕ):AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  IdealGaussCRT.quotientAddChar _ (ramifiedLinearChar u n) (ramifiedLinearChar_period u n)

lemma ramifiedQuotientChar_rep (u:Eisˣ) (n:ℕ) (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedQuotientChar u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x)) := by
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  rfl

def ramifiedFrequencyChar (k:Eis) (u:Eisˣ) (n:ℕ):
    AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  ramifiedQuotientChar u n *
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num)).mulShift (Ideal.Quotient.mk _ k)

lemma ramifiedFrequencyChar_rep (k:Eis) (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedFrequencyChar k u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (3*GaussianShiftedPartition.representative 3 x) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar_rep]
  congr 1
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  simp only [AddChar.mulShift_apply,←map_mul,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp

theorem ramifiedNineSum_eq_character_test (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedNineSum k u n=
      if ramifiedFrequencyChar k u n=1 then 9*residueAdditive k 3 1 else 0 := by
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  let:Fintype (Eis⧸Ideal.span {(3:Eis)}):=Fintype.ofFinite _
  have hcard:(Fintype.card (Eis⧸Ideal.span {(3:Eis)}):ℂ)=9:=by
    have hh:=three_absNorm
    change Nat.card (Eis⧸Ideal.span {(3:Eis)})=9 at hh
    exact_mod_cast (show Fintype.card (Eis⧸Ideal.span {(3:Eis)})=9 by
      simpa only [Nat.card_eq_fintype_card] using hh)
  have he:ramifiedNineSum k u n=residueAdditive k 3 1*
      ∑'x:Eis⧸Ideal.span {(3:Eis)},ramifiedFrequencyChar k u n x:=by
    rw [ramifiedNineSum,←tsum_mul_left]
    apply tsum_congr
    intro x
    rw [ramifiedFrequencyChar_rep,residueAdditive_add]
    ring
  rw [he,tsum_fintype]
  split_ifs with hchar
  · rw [AddChar.sum_eq_card_of_eq_one hchar,hcard]
    ring
  · rw [AddChar.sum_eq_zero_of_ne_one hchar,mul_zero]

theorem ramified_arithmetic_character_test (h k:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      if ramifiedFrequencyChar k u n=1 then ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0 := by
  rw [ramified_arithmetic_nine_sum h k u n hn hk,ramifiedNineSum_eq_character_test]
  have hp:(3:ℕ)^n=3^(n-2)*9:=by
    have hn':n=(n-2)+2:=by omega
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  split_ifs
  · rw [hp,Nat.cast_mul]
    norm_num
    ring
  · ring

end CubicEisenstein

namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic
open CubicEisenstein

def levelThreeInTwo : Subgroup levelTwo := levelThree.comap levelTwo.subtype

instance levelThreeInTwo_normal : levelThreeInTwo.Normal := by
  constructor
  intro n hn g
  exact (levelThreeConjugate (g:SL(2,ActualEisensteinCubic.O)) ⟨(n:SL(2,ActualEisensteinCubic.O)),hn⟩).property

instance levelThreeInTwo_finiteIndex : levelThreeInTwo.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  change (levelThree.comap levelTwo.subtype).FiniteIndex
  infer_instance

def rationalLift : SL(2,ℤ)→*levelTwo where
  toFun r := ⟨rationalEmbedding r,rational_mem_levelTwo r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def rationalQuotient : SL(2,ℤ)→*(levelTwo ⧸ levelThreeInTwo) :=
  (QuotientGroup.mk' levelThreeInTwo).comp rationalLift

theorem rationalQuotient_surjective : Function.Surjective rationalQuotient := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective levelThreeInTwo q
  obtain ⟨n,r,hr⟩ := g.property
  refine ⟨r,?_⟩
  let n2 : levelTwo := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  have he : g=n2*rationalLift r := Subtype.ext hr.symm
  have hn : QuotientGroup.mk' levelThreeInTwo n2=1 :=
    (QuotientGroup.eq_one_iff n2).mpr n.property
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=_
  rw [he,map_mul,hn,one_mul]

def rationalCongruenceThree : Subgroup (SL(2,ℤ)) := rationalQuotient.ker

instance rationalCongruenceThree_normal : rationalCongruenceThree.Normal := by
  unfold rationalCongruenceThree
  infer_instance

theorem mem_rationalCongruenceThree (r : SL(2,ℤ)) :
    r∈rationalCongruenceThree ↔ rationalEmbedding r∈levelThree := by
  change QuotientGroup.mk' levelThreeInTwo (rationalLift r)=1 ↔ _
  exact QuotientGroup.eq_one_iff _

instance rationalCongruenceThree_finiteIndex : rationalCongruenceThree.FiniteIndex := by
  have he : rationalCongruenceThree=levelThree.comap rationalEmbedding := by
    ext r
    exact mem_rationalCongruenceThree r
  rw [he]
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  infer_instance

end

open ActualEisensteinCubic

lemma three_dvd_intCast_iff (a : ℤ) : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) ↔ (3:ℤ)∣a := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨u,v,huv⟩ := ActualEisensteinCoordinates.exists_coordinates x
    have he : ActualEisensteinCoordinates.eval a 0=
        ActualEisensteinCoordinates.eval (3*u) (3*v) := by
      dsimp [ActualEisensteinCoordinates.eval]
      rw [hx,huv]
      push_cast
      ring
    exact ⟨u,(ActualEisensteinCoordinates.unique_coordinates he).1⟩
  · rintro ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb

lemma mem_levelThree_iff_entries (g : SL(2,ActualEisensteinCubic.O)) : g∈levelThree ↔
    ∀i j,(3:ActualEisensteinCubic.O)∣g i j-(if i=j then 1 else 0) := by
  constructor
  · intro hg i j
    exact levelThree_entry ⟨g,hg⟩ i j
  · intro h
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) g=1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)}) (g i j)=
      (1:Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O ⧸ Ideal.span {(3:ActualEisensteinCubic.O)})) i j
    rw [Matrix.one_apply]
    have he := (Ideal.Quotient.mk_eq_mk_iff_sub_mem (g i j) (if i=j then 1 else 0)).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
    simpa only [apply_ite,map_one,map_zero] using he

def rationalReductionThree : SL(2,ℤ)→*SL(2,ZMod 3) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

lemma rationalReductionThree_eq_one_iff (g : SL(2,ℤ)) :
    rationalReductionThree g=1 ↔ g∈rationalCongruenceThree := by
  rw [mem_rationalCongruenceThree,mem_levelThree_iff_entries]
  constructor
  · intro hg i j
    have he := congrArg (fun h : SL(2,ZMod 3) => h i j) hg
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j at he
    rw [Matrix.one_apply] at he
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using sub_eq_zero.mpr he
    have hO := (three_dvd_intCast_iff (g i j-(if i=j then 1 else 0))).mpr hd
    simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
      Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hO
  · intro hg
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (g i j:ZMod 3)=(1:Matrix (Fin 2) (Fin 2) (ZMod 3)) i j
    rw [Matrix.one_apply]
    apply sub_eq_zero.mp
    have hd : (3:ℤ)∣g i j-(if i=j then 1 else 0) := by
      apply (three_dvd_intCast_iff _).mp
      simpa only [rationalEmbedding,Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,
        Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hg i j
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
    simpa only [Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero] using hz

abbrev RationalBruhatIndex := Fin 2 × (Fin 3 ⊕ (Fin 3 × Fin 3))

def rationalBruhatRep (i : RationalBruhatIndex) : SL(2,ℤ) :=
  ModularGroup.S^(2*i.1.val) * match i.2 with
    | Sum.inl a => ModularGroup.T^a.val
    | Sum.inr ab => ModularGroup.T^ab.1.val*ModularGroup.S*ModularGroup.T^ab.2.val

lemma rationalBruhat_complete : ∀g : SL(2,ZMod 3),
    ∃i : RationalBruhatIndex,rationalReductionThree (rationalBruhatRep i)=g := by
  decide +kernel

lemma rationalReductionThree_surjective : Function.Surjective rationalReductionThree := by
  intro g
  obtain ⟨i,hi⟩ := rationalBruhat_complete g
  exact ⟨rationalBruhatRep i,hi⟩

lemma rationalBruhat_injective : Function.Injective
    (fun i : RationalBruhatIndex => rationalReductionThree (rationalBruhatRep i)) := by
  decide +kernel

end CubicKubota

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicEisenstein

lemma rationalQuotient_eq_iff_reduction (r s : SL(2,ℤ)) :
    rationalQuotient r=rationalQuotient s ↔
      rationalReductionThree r=rationalReductionThree s := by
  have hleft : rationalQuotient r=rationalQuotient s ↔ r*s⁻¹∈rationalCongruenceThree := by
    change _ ↔ rationalQuotient (r*s⁻¹)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
  rw [hleft,←rationalReductionThree_eq_one_iff,map_mul,map_inv,mul_inv_eq_one]

lemma levelTwoComplexCharacter_rationalLift (r : SL(2,ℤ)) :
    levelTwoComplexCharacter (rationalLift r)=1 := levelTwoComplexCharacter_rational r

def rationalCosetEquiv : RationalBruhatIndex ≃ (levelTwo ⧸ levelThreeInTwo) :=
  Equiv.ofBijective (fun i => rationalQuotient (rationalBruhatRep i)) ⟨by
    intro i j h
    exact rationalBruhat_injective ((rationalQuotient_eq_iff_reduction _ _).mp h),by
    intro q
    obtain ⟨r,hr⟩ := rationalQuotient_surjective q
    obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
    exact ⟨i,((rationalQuotient_eq_iff_reduction _ _).mpr hi).trans hr⟩⟩

instance sourceQuotientFintype : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _

def sourceRationalSection (q : levelTwo ⧸ levelThreeInTwo) : SL(2,ℤ) :=
  rationalBruhatRep (rationalCosetEquiv.symm q)

lemma sourceRationalSection_spec (q : levelTwo ⧸ levelThreeInTwo) :
    rationalQuotient (sourceRationalSection q)=q := rationalCosetEquiv.apply_symm_apply q

def sourceProjection (f : HyperbolicSpace→ℂ) (w : HyperbolicSpace) : ℂ :=
  (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
    f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)

lemma sourceProjection_eq_twentyFour (f : HyperbolicSpace→ℂ) (w : HyperbolicSpace) :
    sourceProjection f w=(24:ℂ)⁻¹ * ∑i : RationalBruhatIndex,
      f (integralComplexMatrix (rationalEmbedding (rationalBruhatRep i)) • w) := by
  unfold sourceProjection
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

lemma sourceSection_translate (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (q : levelTwo ⧸ levelThreeInTwo) (g : levelTwo) (w : HyperbolicSpace) :
    f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) •
      (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)) =
    levelTwoComplexCharacter g *
      f (integralComplexMatrix (rationalEmbedding (sourceRationalSection
        (q*QuotientGroup.mk' levelThreeInTwo g))) • w) := by
  let r := sourceRationalSection q
  let s := sourceRationalSection (q*QuotientGroup.mk' levelThreeInTwo g)
  let n2 : levelTwo := rationalLift r*g*(rationalLift s)⁻¹
  have hn2 : n2∈levelThreeInTwo := by
    apply (QuotientGroup.eq_one_iff (N:=levelThreeInTwo) n2).mp
    change QuotientGroup.mk' levelThreeInTwo (rationalLift r*g*(rationalLift s)⁻¹)=1
    rw [map_mul,map_mul,map_inv]
    change rationalQuotient r * QuotientGroup.mk' levelThreeInTwo g *
      (rationalQuotient s)⁻¹=1
    rw [sourceRationalSection_spec,sourceRationalSection_spec,mul_inv_cancel]
  let n : levelThree := ⟨(n2:SL(2,ActualEisensteinCubic.O)),hn2⟩
  have hc : complexCharacter n=levelTwoComplexCharacter g := by
    rw [←levelTwoComplexCharacter_restrict n]
    change levelTwoComplexCharacter (rationalLift r*g*(rationalLift s)⁻¹)=_
    rw [map_mul,map_mul,←map_inv rationalLift]
    change levelTwoComplexCharacter (rationalLift r)*levelTwoComplexCharacter g*
      levelTwoComplexCharacter (rationalLift s⁻¹)=_
    rw [levelTwoComplexCharacter_rationalLift,levelTwoComplexCharacter_rationalLift,one_mul,mul_one]
  have he : rationalEmbedding r*(g:SL(2,ActualEisensteinCubic.O))=(n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding s := by
    change _=(rationalEmbedding r*(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding s)⁻¹)*rationalEmbedding s
    group
  change f (integralComplexMatrix (rationalEmbedding r) •
    (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w))=
    levelTwoComplexCharacter g*f (integralComplexMatrix (rationalEmbedding s) • w)
  rw [←mul_smul,←map_mul,he,map_mul,integralComplexMatrix_levelThree,mul_smul,hf,hc]

theorem sourceProjection_automorphy (f : HyperbolicSpace→ℂ)
    (hf : ∀n : levelThree,∀w,f (complexMatrix n • w)=complexCharacter n*f w)
    (g : levelTwo) (w : HyperbolicSpace) :
    sourceProjection f (integralComplexMatrix (g:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter g * sourceProjection f w := by
  unfold sourceProjection
  simp_rw [sourceSection_translate f hf]
  rw [←Finset.mul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInTwo g))
    (fun q => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))]
  ring

def sourceEisenstein (s : ℂ) : HyperbolicSpace→ℂ := sourceProjection (hyperbolicEisenstein s)

end CubicKubota

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ScatteringResidues
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical Topology

section

lemma scalar_residue_sub_continuous (f g : ℂ→ℂ) (z r : ℂ)
    (hf : Tendsto (fun s => (s-z)*f s) (𝓝[≠] z) (𝓝 r)) (hg : ContinuousAt g z) :
    Tendsto (fun s => (s-z)*(f s-g s)) (𝓝[≠] z) (𝓝 r) := by
  have hlin : Tendsto (fun s : ℂ => s-z) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [id_eq,sub_self] using (tendsto_id.sub_const z).mono_left
      (show 𝓝[≠] z≤𝓝 z from nhdsWithin_le_nhds)
  have hz : Tendsto (fun s => (s-z)*g s) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using hlin.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [mul_sub,sub_zero] using hf.sub hz

lemma weightedOutgoingConstant_residue_limit (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*weightedOutgoingConstant a b ha ρ s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue)) := by
  apply scalar_residue_sub_continuous _ _ _ _ (kernelCuspHeightFourierFamily_residue_limit a b ha ρ 0)
  exact continuousAt_const.mul
    ((compactHeightMellin_differentiable a b ha ρ).continuous.continuousAt.comp
      (continuousAt_id.sub_const 3))

lemma baseOutgoingConstant_residue_limit :
    Tendsto (fun s : ℂ => (s-4/3)*baseOutgoingConstant s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cuspConstantAverageResidue) := by
  have hf := kernelCuspAverageFamily_residue_limit 2 3 (by norm_num) (by norm_num)
  change Tendsto _ _ (𝓝 (kernelCuspStripAverage cubicEisensteinResidue)) at hf
  rw [cubicEisensteinResidue_cusp_average] at hf
  apply scalar_residue_sub_continuous _ _ _ _ hf
  exact continuousAt_const.mul
    (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt

theorem kernelCuspHeightFourier_zero_residue (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
        (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(4/3:ℂ)-1)) := by
  have hbase : Tendsto cuspScatterHeightFactor (𝓝[≠] (4/3:ℂ))
      (𝓝 (cuspScatterHeightFactor (4/3:ℂ))) :=
    (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => compactHeightMellin a b ρ (-s-1)) (𝓝[≠] (4/3:ℂ))
      (𝓝 (compactHeightMellin a b ρ (-(4/3:ℂ)-1))) :=
    ((compactHeightMellin_differentiable a b ha ρ).continuous.continuousAt.comp
      (continuousAt_id.neg.sub_const 1)).tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((weightedOutgoingConstant_residue_limit a b ha ρ).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := (baseOutgoingConstant_residue_limit.mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*weightedOutgoingConstant a b ha ρ ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspScatterHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        compactHeightMellin a b ρ (-((4/3:ℂ)+(t:ℂ)*Complex.I)-1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := weightedOutgoingConstant_cross_identity a b ha ρ hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue*cuspScatterHeightFactor (4/3:ℂ)=
      cuspConstantAverageResidue*compactHeightMellin a b ρ (-(4/3:ℂ)-1) :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hne : cuspScatterHeightFactor (4/3:ℂ)≠0 := by
    intro he
    have hpos := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  apply mul_right_cancel₀ hne
  rw [heq,cuspConstantAverageResidue]
  change _=(((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    compactHeightMellin a b ρ (-(4/3:ℂ)-1))*cuspScatterHeightFactor (4/3:ℂ)
  ring

lemma kernelCuspHeightFourier_zero_residue_seven_thirds (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
        (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ))) := by
  convert (preTransparency := .instances) kernelCuspHeightFourier_zero_residue a b ha ρ using 2
  congr 1
  norm_num

local notation "O" => ActualEisensteinCubic.O

def cubicResidualFullModeAmplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else cubicResidualFourierCoefficient h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma cubicResidualFullModeAmplitude_zero (v : ℝ) :
    cubicResidualFullModeAmplitude v 0=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) := by
  simp only [cubicResidualFullModeAmplitude,ite_true]

lemma cubicResidualFullModeAmplitude_nonzero (v : ℝ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cubicResidualFullModeAmplitude v h=cubicResidualFourierCoefficient h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [cubicResidualFullModeAmplitude,if_neg hh]

lemma cubicResidualFullModeAmplitude_zero_density (v : ℝ) (hv : 0<v) :
    cubicResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^(-(7/3:ℂ))=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3 := by
    rw [show -(7/3:ℂ)=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [cubicResidualFullModeAmplitude_zero,hp]
  ring

lemma cubicResidualFullModeAmplitude_nonzero_density (v : ℝ) (hv : 0<v)
    (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cubicResidualFullModeAmplitude v h/(v:ℂ)^3=cubicResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [cubicResidualFullModeAmplitude_nonzero v h hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem kernelCuspHeightFourier_residue_full (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  by_cases hh : h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*
          (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ))) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelCuspHeightFourier_residue_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3))=
        cubicResidualFourierCoefficient h*(∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicResidualFunction (w : HyperbolicSpace) : ℂ :=
  (3*Real.pi:ℂ)*constantArithmeticResidue*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+
    cubicResidualNonzeroFunction w

lemma cubicResidualFunction_continuous : Continuous cubicResidualFunction := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add cubicResidualNonzeroFunction_continuous

lemma cubicResidualNonzeroSeries_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicResidualNonzeroSeries (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (cubicResidualNonzeroSeries_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

lemma periodDomain_integrable_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    IntegrableOn f periodDomain volume := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma cubicResidualFunction_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then
        (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) else cubicResidualModeAmplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => ((3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)) (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((cubicResidualNonzeroSeries_height_continuous v hv).mul hphase)
  simp_rw [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,cubicResidualNonzeroSeries_fourier v hv k]
  by_cases hk : k=0
  · simp only [if_pos hk,cubicResidualModeAmplitude,mul_zero]
    ring
  · simp only [if_neg hk,mul_zero,zero_add]

lemma cubicResidualFunction_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    cubicResidualFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      cubicResidualFunction (upperPoint z v hv) := by
  simp only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,cubicResidualNonzeroSeries_period]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelCuspHeightPullback_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    MemLp (fun w => F (integralOrbitProjection globalKubotaKernel w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  MemLp.ae_eq (kernelCuspHeightPullback_ae a b ha F)
    (MeasureTheory.Lp.memLp (kernelCuspHeightPullback a b ha F))

lemma kernelCuspCoordinates_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    MemLp (fun q : ℝ × ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)) := by
  have hm := euclideanToHyperbolic_measurePreserving_on (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
  rw [positiveEuclideanStrip_preimage] at hm
  have hF := (kernelCuspHeightPullback_memLp a b ha F).comp_measurePreserving hm
  have hvol := euclideanVolume_le_heightCube_hyperbolic (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
    (max 1 b) (by positivity) (fun p hp => hp.1.2.trans (le_max_right 1 b))
  have hFE := (hF.smul_measure (c := ENNReal.ofReal ((max 1 b)^3)) ENNReal.ofReal_ne_top).mono_measure hvol
  have hsplit := spatialComplexSplit_preserves_volume.restrict_preimage (s := Set.Icc a b ×ˢ periodDomain)
    (measurableSet_Icc.prod periodDomain_measurable)
  have hback := hsplit.symm
  have hpull := hFE.comp_measurePreserving hback
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod, Function.comp_def,
    positiveEuclideanStrip, cuspCoordinateLift] using hpull

section ProductSections
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {«μ» : Measure α} {ν : Measure β} [SFinite «μ»] [SFinite ν]

lemma complex_memLp_two_sections {f : α × β → ℂ} (hf : MemLp f 2 («μ».prod ν)) :
    ∀ᵐx ∂«μ», MemLp (fun y => f (x,y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    hf.norm.integrable_sq.prod_right_ae] with x hx hi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi

end ProductSections

lemma kernelCuspSections_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      MemLp (fun z : ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))) 2
        (volume.restrict periodDomain) :=
  complex_memLp_two_sections (kernelCuspCoordinates_memLp a b ha F)

lemma cuspCoordinateLift_measurable : Measurable cuspCoordinateLift :=
  euclideanToHyperbolic_measurable.comp spatialComplexSplit.symm.measurable

lemma kernelCuspFourierCoordinate_integrable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    IntegrableOn (fun q : ℝ × ℂ =>
      (F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))*
        cuspWeightedFourierPhase ρ h (cuspCoordinateLift q))/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume := by
  let := periodDomain_finiteMeasure
  have hF := (kernelCuspCoordinates_memLp a b ha F).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hm : Measurable (fun q : ℝ × ℂ =>
      cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)/(q.1:ℂ)^3) :=
    ((cuspWeightedFourierPhase_continuous ρ h).measurable.comp cuspCoordinateLift_measurable).div
      (by fun_prop)
  have hb : ∀ᵐq ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)),
      ‖cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)/(q.1:ℂ)^3‖≤‖ρ‖/a^3 := by
    rw [Measure.prod_restrict, ←Measure.volume_eq_prod]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod periodDomain_measurable)] with q hq
    have hpos : 0<q.1 := ha.trans_le hq.1.1
    rw [norm_div,norm_pow,Complex.norm_of_nonneg hpos.le]
    calc
      _ ≤ ‖ρ‖/q.1^3 := div_le_div_of_nonneg_right
        (cuspWeightedFourierPhase_bound ρ h (cuspCoordinateLift q)) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ ha.le hq.1.1 3)
  have hi := hF.mul_bdd hm.aestronglyMeasurable hb
  simpa only [IntegrableOn, Measure.prod_restrict, ←Measure.volume_eq_prod, mul_div_assoc] using hi

def kernelCuspSliceCoefficient (F : KernelQuotientL2) (h : ActualEisensteinCubic.O) (v : ℝ) : ℂ :=
  (∫z in periodDomain, F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
    ShortDraftTrace.breveE (-cuspFrequency h*z))/(v:ℂ)^3

lemma kernelCuspHeightFourier_eq_slice_integral (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h F =
      ∫v in Set.Icc a b, ρ v*kernelCuspSliceCoefficient F h v := by
  rw [kernelCuspHeightFourier_integral]
  have hg : StronglyMeasurable (fun w =>
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w) :=
    ((MeasureTheory.Lp.stronglyMeasurable F).comp_measurable (measurable_integralOrbitProjection _)).mul
      (cuspWeightedFourierPhase_continuous ρ h).stronglyMeasurable
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (kernelCuspFourierCoordinate_integrable a b ha ρ h F)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  simp only [kernelCuspSliceCoefficient]
  rw [←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [cuspWeightedFourierPhase,cuspFourierPhase,cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)

lemma kernelCuspSliceCoefficient_integrable (a b : ℝ) (ha : 0<a)
    (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    IntegrableOn (kernelCuspSliceCoefficient F h) (Set.Icc a b) volume := by
  have hi := kernelCuspFourierCoordinate_integrable a b ha 1 h F
  rw [IntegrableOn, Measure.volume_eq_prod, ←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hpos : 0<v := ha.trans_le hv.1
  rw [integral_div, kernelCuspSliceCoefficient]
  apply congrArg (fun c : ℂ => c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [kernelCuspSliceCoefficient]
    rw [cuspWeightedFourierPhase,cuspFourierPhase,cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)

end

section

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma third_character_eq_one_iff_basis (ψ:AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ) :
    ψ=1 ↔ ψ (Ideal.Quotient.mk _ (1:Eis))=1 ∧
      ψ (Ideal.Quotient.mk _ omega)=1 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1,hw⟩
    ext x
    obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [←ActualEisensteinCoordinates.eval_coords z]
    change ψ (Ideal.Quotient.mk _
      (((ActualEisensteinCoordinates.coords z).1:Eis)+
       ((ActualEisensteinCoordinates.coords z).2:Eis)*omega))=1
    rw [map_add,AddChar.map_add_eq_mul]
    have hA:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        ((ActualEisensteinCoordinates.coords z).1:Eis)=
        (ActualEisensteinCoordinates.coords z).1 • Ideal.Quotient.mk _ (1:Eis):=by
      rw [←map_zsmul]
      simp
    have hB:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        (((ActualEisensteinCoordinates.coords z).2:Eis)*omega)=
        (ActualEisensteinCoordinates.coords z).2 • Ideal.Quotient.mk _ omega:=by
      rw [←map_zsmul]
      simp only [zsmul_eq_mul]
    rw [hA,hB,AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,h1,hw]
    simp

lemma omega3_pow_exp_eq_one_iff (t:ℕ) (b:ℤ) :
    omega3^t*Complex.exp (2*Real.pi*Complex.I*(b:ℂ)/3)=1 ↔
      (3:ℤ)∣(t:ℤ)+b := by
  have hω:omega3=Complex.exp (2*Real.pi*Complex.I/3):=by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1,?_⟩
    push_cast
    ring
  rw [hω,←Complex.exp_nat_mul,←Complex.exp_add]
  have he:(t:ℂ)*(2*Real.pi*Complex.I/3)+2*Real.pi*Complex.I*(b:ℂ)/3=
      2*Real.pi*Complex.I*(((t:ℤ)+b:ℤ):ℂ)/3:=by push_cast;ring
  rw [he]
  constructor
  · intro hh
    have hh':Complex.exp (2*Real.pi*Complex.I*((((t:ℤ)+b:ℤ):ℂ)/3))=1:=by
      convert (preTransparency := .instances) hh using 1 ;ring_nf
    obtain ⟨v,hv⟩:=GeneralPrimitiveTrace.complex_exp_trace_integer hh'
    have hc:(((t:ℤ)+b:ℤ):ℂ)=3*(v:ℂ):=by linear_combination 3*hv
    have hi:(t:ℤ)+b=3*v:=by exact_mod_cast hc
    exact ⟨v,hi⟩
  · rintro ⟨v,hv⟩
    rw [hv]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨v,?_⟩
    push_cast
    ring

lemma eisEmbedding_omega_actual : eisEmbedding omega=omega3 := by
  have hω:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hω,eisEmbedding_eval]
  norm_num

lemma trace_third_coordinate (k:Eis) :
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num) (Ideal.Quotient.mk _ k)=
      Complex.exp (2*Real.pi*Complex.I*((ActualEisensteinCoordinates.coords k).2:ℂ)/3) := by
  rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  have hh:=breveE_real_trace_of_O 3 k
  norm_num at hh
  convert (preTransparency := .instances) hh using 1 ;simp only [map_ofNat] ;congr 1 ;ring

end

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_symbol_primaryCoord (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) (A B:ℤ) :
    symbol (u.val*lambda^n) (primaryCoord A B)=
      (cubicExp (2*A-B))^j*(cubicExp A)^n := by
  have hp:=primaryCoord_primary A B
  rw [symbol_mul_numerator _ _ _ hp,symbol_pow_numerator _ _ hp,
    symbol_lambda_eq_linearRay _ hp,linearRay_primaryCoord]
  norm_num only [one_mul,zero_mul,add_zero]
  congr 1
  rcases hu with hu|hu
  · rw [hu,symbol_pow_numerator _ _ hp,symbol_omega_eq_linearRay _ hp,
      linearRay_primaryCoord]
    ring_nf
  · rw [hu,symbol_neg_numerator _ _ hp,symbol_pow_numerator _ _ hp,
      symbol_omega_eq_linearRay _ hp,linearRay_primaryCoord]
    ring_nf

lemma ramified_symbol_at_one (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*(1:Eis))=omega^(2*j+n) := by
  have he:(1+3*(1:Eis))=primaryCoord 1 0:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  rw [←pow_mul,←pow_add]

lemma ramified_symbol_at_omega (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*omega)=omega^(2*j) := by
  have he:(1+3*omega)=primaryCoord 0 1:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  rw [←pow_mul]

lemma ramifiedFrequencyChar_mk (k:Eis) (u:Eisˣ) (n:ℕ) (x:Eis) :
    ramifiedFrequencyChar k u n (Ideal.Quotient.mk _ x)=
      eisEmbedding (symbol (u.val*lambda^n) (1+3*x))*
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ (k*x)) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar,
    IdealGaussCRT.quotientAddChar_mk,AddChar.mulShift_apply,←map_mul]
  rfl

lemma coords_mul_omega_second (k:Eis) :
    (ActualEisensteinCoordinates.coords (k*omega)).2=
      (ActualEisensteinCoordinates.coords k).1-(ActualEisensteinCoordinates.coords k).2 := by
  conv_lhs => rw [←ActualEisensteinCoordinates.eval_coords k]
  have hw:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

def ramifiedCongruence (k:Eis) (j n:ℕ):Prop:=
  (3:ℤ)∣(2*(j:ℤ)+(n:ℤ)+(ActualEisensteinCoordinates.coords k).2) ∧
  (3:ℤ)∣(2*(j:ℤ)+(ActualEisensteinCoordinates.coords k).1-
    (ActualEisensteinCoordinates.coords k).2)

lemma ramifiedFrequencyChar_eq_one_iff (k:Eis) (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    ramifiedFrequencyChar k u n=1 ↔ ramifiedCongruence k j n := by
  rw [third_character_eq_one_iff_basis,ramifiedFrequencyChar_mk,
    ramifiedFrequencyChar_mk,ramified_symbol_at_one u n j hu,
    ramified_symbol_at_omega u n j hu,map_pow,map_pow,eisEmbedding_omega_actual,
    mul_one,trace_third_coordinate,trace_third_coordinate,coords_mul_omega_second,
    omega3_pow_exp_eq_one_iff,omega3_pow_exp_eq_one_iff]
  unfold ramifiedCongruence
  push_cast
  simp only [add_sub_assoc]

theorem ramified_arithmetic_explicit_table (h k:Eis) (u:Eisˣ) (n j:ℕ)
    (hn:2≤n) (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j))
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      if ramifiedCongruence k j n then ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0 := by
  rw [ramified_arithmetic_character_test h k u n hn hk]
  simp only [ramifiedFrequencyChar_eq_one_iff k u n j hu]

def ramifiedUnitIndex (u:Eisˣ):Fin 3:=Classical.choose (unit_eq_sign_omega u)

lemma ramifiedUnitIndex_spec (u:Eisˣ) :
    (u:Eis)=omega^(ramifiedUnitIndex u).val ∨
      (u:Eis)=-(omega^(ramifiedUnitIndex u).val):=
  Classical.choose_spec (unit_eq_sign_omega u)

def explicitRamifiedCoefficient (h:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  if hd:u.val*lambda^n∣3*h then
    let k:=Classical.choose hd
    if ramifiedCongruence k (ramifiedUnitIndex u).val n then
      ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0
  else 0

theorem arithmeticResidueSum_eq_explicitRamifiedCoefficient (h:Eis) (u:Eisˣ)
    (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=explicitRamifiedCoefficient h u n := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · exact ramified_arithmetic_explicit_table h (Classical.choose hd) u n
      (ramifiedUnitIndex u).val hn (ramifiedUnitIndex_spec u) (Classical.choose_spec hd)
  · by_contra hne
    exact hd (ramified_arithmetic_support h u n hn hne)

theorem scatteringCoefficient_explicit_ramified (s:ℂ) (hs:2<s.re)
    (h:Eis) (hh:h≠0) :
    scatteringCoefficient s h=
      (∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h u (n+2)*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient_unramified_gauss s hs h hh]
  congr 1
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (n+2) (by omega)]

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceQuotient
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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

abbrev SourceKernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def sourceComplexMatrix : levelTwo→*SL(2,ℂ) :=
  integralComplexMatrix.comp levelTwo.subtype

lemma globalKubotaKernel_source_conjugate_mem (M : levelTwo) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel :=
  CubicKubota.globalKubotaKernel_conjugate M N N.property

def kernelSourceConjugate (M : levelTwo) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_source_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹,globalKubotaKernel_source_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma source_action_respects_kernel (M : levelTwo) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (sourceComplexMatrix M • u) (sourceComplexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelSourceConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (sourceComplexMatrix M • u)=sourceComplexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change sourceComplexMatrix M • (integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) •
    ((sourceComplexMatrix M)⁻¹ • (sourceComplexMatrix M • u)))=_
  rw [inv_smul_smul,hN]

def kernelSourceAction (M : levelTwo) : SourceKernelQuotient→SourceKernelQuotient :=
  Quotient.map' (fun w => sourceComplexMatrix M • w) (source_action_respects_kernel M)

lemma kernelSourceAction_mk (M : levelTwo) (w : HyperbolicSpace) :
    kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • w) := rfl

lemma kernelSourceAction_one (q : SourceKernelQuotient) : kernelSourceAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelSourceAction_mul (M N : levelTwo) (q : SourceKernelQuotient) :
    kernelSourceAction (M*N) q=kernelSourceAction M (kernelSourceAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • (sourceComplexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelSourceAction_continuous (M : levelTwo) : Continuous (kernelSourceAction M) :=
  (continuous_hyperbolic_action (sourceComplexMatrix M)).quotient_map' (source_action_respects_kernel M)

def kernelSourceHomeomorph (M : levelTwo) : SourceKernelQuotient ≃ₜ SourceKernelQuotient where
  toFun := kernelSourceAction M
  invFun := kernelSourceAction M⁻¹
  left_inv q := by rw [←kernelSourceAction_mul,inv_mul_cancel,kernelSourceAction_one]
  right_inv q := by rw [←kernelSourceAction_mul,mul_inv_cancel,kernelSourceAction_one]
  continuous_toFun := kernelSourceAction_continuous M
  continuous_invFun := kernelSourceAction_continuous M⁻¹

lemma kernelSourceAction_fundamentalDomain (M : levelTwo) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => sourceComplexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (sourceComplexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (sourceComplexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (sourceComplexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelSourceConjugate M⁻¹).toEquiv
  intro N w
  change sourceComplexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (sourceComplexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change sourceComplexMatrix M • (((sourceComplexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((sourceComplexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelSourceAction_measurePreserving (M : levelTwo) :
    MeasurePreserving (kernelSourceAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelSourceAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => sourceComplexMatrix M • w
  have hmap := (measurePreserving_smul (sourceComplexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (sourceComplexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelSourceAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelSourceAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelSourceAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelSourceAction_fundamentalDomain M)

end CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota

def kernelSourcePullback (M : levelTwo) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelSourceAction M) (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_ae_eq (M : levelTwo) (F : KernelQuotientL2) :
    kernelSourcePullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelSourceAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_one (F : KernelQuotientL2) : kernelSourcePullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq 1 F] with q hq
  simpa only [kernelSourceAction_one] using hq

lemma kernelSourcePullback_comp (M N : levelTwo) (F : KernelQuotientL2) :
    kernelSourcePullback M (kernelSourcePullback N F)=kernelSourcePullback (N*M) F := by
  have hcomp := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSourcePullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq M (kernelSourcePullback N F),hcomp,
    kernelSourcePullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelSourceAction_mul N M q).symm)

local notation "O" => ActualEisensteinCubic.O

def kernelSourceProjection : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  (24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
    (kernelSourcePullback (rationalLift (sourceRationalSection q))).toContinuousLinearMap

lemma kernelSourceProjection_apply (F : KernelQuotientL2) :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F := by
  simp only [kernelSourceProjection,_root_.smul_apply,_root_.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap]

lemma kernelSourceProjection_eq_twentyFour (F : KernelQuotientL2) :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑i : RationalBruhatIndex,
      kernelSourcePullback (rationalLift (rationalBruhatRep i)) F := by
  rw [kernelSourceProjection_apply]
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

end CubicEisenstein

namespace CubicKubota
open ActualEisensteinCubic

def sourceLevelInclusion : levelThree→*levelTwo where
  toFun n := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

lemma sourceLevelInclusion_character (n : levelThree) :
    levelTwoComplexCharacter (sourceLevelInclusion n)=complexCharacter n :=
  levelTwoComplexCharacter_restrict n

end CubicKubota

namespace CubicEisenstein
open CubicKubota

lemma kernelSourceProjection_ae_eq (F : KernelQuotientL2) :
    kernelSourceProjection F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
        F (kernelSourceAction (rationalLift (sourceRationalSection q)) x) := by
  rw [kernelSourceProjection_apply]
  have hsum := (Lp.coeFn_finsetSum Finset.univ
    (fun q : levelTwo ⧸ levelThreeInTwo =>
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F)).trans
    (eventuallyEq_sum (fun q _ =>
      kernelSourcePullback_ae_eq (rationalLift (sourceRationalSection q)) F))
  filter_upwards [(Lp.coeFn_smul (24:ℂ)⁻¹ _).trans (hsum.const_smul (24:ℂ)⁻¹)] with x hx
  simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using hx

end CubicEisenstein
end

open scoped Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
open EisensteinSchwartzPoisson ActualEisensteinCubic ConcreteTraceCRT Module

def periodVector : (Fin 2 → ℝ) ≃L[ℝ] ℂ := periodBasis.equivFunL.symm

lemma periodVector_apply (x : Fin 2 → ℝ) :
    periodVector x = 3 * ((x 0 : ℂ) + (x 1 : ℂ) * omega3) := by
  change periodBasis.equivFun.symm x = _
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_two, periodBasis_zero, periodBasis_one]
  simp only [Complex.real_smul]
  ring

def periodTorus (z : ℂ) : UnitAddTorus (Fin 2) :=
  fun i => (periodBasis.equivFunL z i : UnitAddCircle)

lemma periodTorus_periodVector (x : Fin 2 → ℝ) :
    periodTorus (periodVector x) = fun i => (x i : UnitAddCircle) := by
  change (fun i => ((periodBasis.equivFunL (periodBasis.equivFunL.symm x)) i : UnitAddCircle)) = _
  rw [periodBasis.equivFunL.apply_symm_apply]

def periodFrequencyEquiv : (Fin 2 → ℤ) ≃ ActualEisensteinCubic.O :=
  (finTwoArrowEquiv ℤ).trans dualFrequencyEquiv

lemma periodFrequencyEquiv_apply (n : Fin 2 → ℤ) :
    periodFrequencyEquiv n = dualFrequencyEquiv (n 0, n 1) := rfl

lemma periodVector_character (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * periodVector x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) := by
  have hlam : eisLam ≠ 0 := by
    exact eisLam_ne_zero
  have harg : cuspFrequency (periodFrequencyEquiv n) * periodVector x =
      (eisEmbedding (dualFrequencyEquiv (n 0,n 1)) *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega3)) / eisLam := by
    rw [cuspFrequency, periodVector_apply, periodFrequencyEquiv_apply]
    field_simp
  rw [harg, ←paperE, paperE_eq_exp, dualFrequencyEquiv_coordinates]
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hw : omega3.re = -(1/2:ℝ) := by norm_num [omega3]
  congr 1
  simp only [complexPoint, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, hw, omega3_im]
  push_cast
  field_simp
  ring

lemma periodTorus_mFourier (n : Fin 2 → ℤ) (z : ℂ) :
    UnitAddTorus.mFourier n (periodTorus z) =
      ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * z) := by
  obtain ⟨x, rfl⟩ := periodVector.surjective z
  rw [periodTorus_periodVector, periodVector_character]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [←Complex.exp_add]
  congr 1
  ring

lemma periodFrequencyEquiv_neg (n : Fin 2 → ℤ) :
    periodFrequencyEquiv (-n) = -periodFrequencyEquiv n := by
  apply eisEmbedding_injective
  change eisEmbedding (ActualEisensteinCoordinates.eval (-n 0 + -n 1) (-n 0)) =
    eisEmbedding (-ActualEisensteinCoordinates.eval (n 0 + n 1) (n 0))
  rw [map_neg, eisEmbedding_eval, eisEmbedding_eval]
  push_cast
  ring

lemma cuspFrequency_neg (h : ActualEisensteinCubic.O) : cuspFrequency (-h) = -cuspFrequency h := by
  simp only [cuspFrequency, map_neg, neg_div]

lemma periodVector_eq_lattice (x : Fin 2 → ℝ) :
    periodVector x = eisensteinLatticeMap 3 (by norm_num) (Complex.measurableEquivPi.symm x) := by
  rw [periodVector_apply]
  simp [eisensteinLatticeMap, Complex.measurableEquivPi_symm_apply, mul_comm]

lemma periodVector_map_volume :
    Measure.map periodVector volume = ENNReal.ofReal (2/(9*Real.sqrt 3)) • volume := by
  have heq : (periodVector : (Fin 2 → ℝ) → ℂ) =
      eisensteinLatticeMap 3 (by norm_num) ∘ Complex.measurableEquivPi.symm :=
    funext periodVector_eq_lattice
  rw [heq, ←Measure.map_map (eisensteinLatticeMap 3 (by norm_num)).continuous.measurable
    Complex.measurableEquivPi.symm.measurable, Complex.volume_preserving_equiv_pi.symm.map_eq]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map (eisensteinLatticeMap 3 (by norm_num)) volume =
    ENNReal.ofReal (inverseJacobian (eisensteinLatticeMap 3 (by norm_num))) • volume at hmap
  rw [hmap, eisenstein_inverseJacobian]
  norm_num [mul_comm]

def periodCube : Set (Fin 2 → ℝ) := {x | ∀i, x i ∈ Set.Ico 0 1}

lemma periodVector_preimage_domain : periodVector ⁻¹' periodDomain = periodCube := by
  ext x
  change (∀i, periodBasis.repr (periodBasis.equivFun.symm x) i ∈ Set.Ico 0 1) ↔ _
  simp only [←Basis.equivFun_apply, periodBasis.equivFun.apply_symm_apply]
  rfl

lemma periodDomain_integral_coordinates (f : ℂ → ℂ) :
    (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f z) =
      ∫x in periodCube, f (periodVector x) := by
  have h := periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.setIntegral_map
    f periodDomain («μ» := (volume : Measure (Fin 2 → ℝ)))
  change (∫z in periodDomain, f z ∂Measure.map periodVector volume) =
    ∫x in periodVector ⁻¹' periodDomain, f (periodVector x) at h
  rw [periodVector_map_volume, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), periodVector_preimage_domain] at h
  exact h

local instance instMeasureSpaceUnitAddCircle_solutions : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions_rf37349_1 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_rf37349_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma periodCube_ae_Ioc : periodCube =ᵐ[volume]
    {x : Fin 2 → ℝ | ∀i, x i ∈ Set.Ioc 0 1} := by
  rw [volume_pi]
  have h := Measure.ae_eq_set_pi («μ» := fun _ : Fin 2 => (volume : Measure ℝ))
    (I := Set.univ) (s := fun _ => Set.Ico (0:ℝ) 1) (t := fun _ => Set.Ioc (0:ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  simpa only [Set.pi, Set.mem_univ, forall_true_left, periodCube] using h

lemma periodTorus_integral (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫t, f t) = (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f (periodTorus z)) := by
  rw [periodDomain_integral_coordinates, UnitAddTorus.integral_preimage f (fun _ => 0)]
  simp only [zero_add, periodTorus_periodVector]
  exact setIntegral_congr_set periodCube_ae_Ioc.symm

lemma periodTorus_fourierCoeff (f : UnitAddTorus (Fin 2) → ℂ) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f n = (2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain, f (periodTorus z) *
        ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [UnitAddTorus.mFourierCoeff, periodTorus_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [periodTorus_mFourier, periodFrequencyEquiv_neg, cuspFrequency_neg]
    exact mul_comm _ _)

lemma periodTorus_L2_ext (F G : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain, F (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) =
      ∫z in periodDomain, G (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) : F=G := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext n
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    periodTorus_fourierCoeff, periodTorus_fourierCoeff, h]

end CubicEisenstein

end

end OAI
end


