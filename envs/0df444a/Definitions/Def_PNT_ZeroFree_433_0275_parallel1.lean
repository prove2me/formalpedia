-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0275_parallel1
-- name    : PNT_ZeroFree_433_0275_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:24:16.553995+00:00
-- url     : https://prove2.me/theorems/d0f2e0c3-3941-4995-8c13-6c79579a320d
-- title:
--   Zero-free region foundations: ChineseRemainder.FrequencyLifts [0275_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/FrequencyLifts.lean#L83-L540

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0046_1
import Definitions.Def_PNT_ZeroFree_433_0046_2
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/FrequencyLifts.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

omit [Fintype ι] in
theorem exists_strong_unit_frequency_lifts (M:Eis) (p:ι→Eis)
    (hM:∀i,IsCoprime M (p i)) (x:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ∃h:ι→Eis,(∀i,M^2∣h i) ∧
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i})) ∧
      ∀i,IsCoprime (h i) (p i) := by
  have hx (i:ι) := exists_frequency_lift (M^2) (p i)
    (Quotient.out (x i:Eis⧸Ideal.span {p i})) (hM i).pow_left
  choose h hh hd using hx
  have he (i:ι):Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i}) := by
    calc
      _=Ideal.Quotient.mk (Ideal.span {p i}) (Quotient.out (x i:Eis⧸Ideal.span {p i})) :=
        Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hd i))
      _=x i:=Ideal.Quotient.mk_out _
  refine ⟨h,hh,he,?_⟩
  intro i
  apply IsCoprime.symm
  apply (isUnit_quotient_span_iff (p i) (h i)).mp
  rw [he]
  exact (x i).isUnit


end ShortDraftCRT

open scoped BigOperators Classical


namespace FixedRayActiveSet

lemma sum_nonzero_ite {F : Type*} [Field F] [Fintype F] (f:F→ℂ) :
    (∑x:F,if x≠0 then f x else 0)=∑u:Fˣ,f (u:F) := by
  calc
    _ = ∑x∈(Finset.univ:Finset F).filter (fun x=>x≠0),f x := by rw [Finset.sum_filter]
    _ = ∑x:{x:F//x≠0},f x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = _ := (Equiv.sum_comp unitsEquivNeZero (fun x:{x:F//x≠0}=>f x)).symm

def activeStratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (A:Finset ι) :
    Finset (∀i,F i) := Finset.univ.filter (fun h=>∀i,h i≠0↔i∈A)

theorem sum_active_stratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (A:Finset ι) (f:∀i,F i→ℂ) :
    (∑h∈activeStratum F A,∏i,f i (h i))=
      (∏i∈A,∑u:(F i)ˣ,f i (u:F i))*
        (∏i∈(Finset.univ:Finset ι)\A,f i 0) := by
  classical
  let g:=fun i (x:F i)=>if (x≠0↔i∈A) then f i x else 0
  have hs : (∑h∈activeStratum F A,∏i,f i (h i))=
      ∏i,∑x:F i,g i x := by
    rw [activeStratum,Finset.sum_filter]
    calc
      _ = ∑h:∀i,F i,∏i,g i (h i) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact (Fintype.prod_ite_zero (p:=fun i=>h i≠0↔i∈A) (f:=fun i=>f i (h i))).symm
      _ = _ := (Fintype.prod_sum g).symm
  have hg (i:ι) : (∑x:F i,g i x)=if i∈A then ∑u:(F i)ˣ,f i (u:F i) else f i 0 := by
    by_cases hi:i∈A
    · simpa only [g,hi,iff_true,ite_true] using sum_nonzero_ite (f i)
    · simp [g,hi]
  rw [hs]
  simp only [hg,Finset.prod_ite]
  have ha : (Finset.univ:Finset ι).filter (fun i=>i∈A)=A := by ext i;simp
  have hn : (Finset.univ:Finset ι).filter (fun i=>i∉A)=(Finset.univ:Finset ι)\A := by ext i;simp
  rw [ha,hn]

theorem sum_by_active_strata {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (weight:(∀i,F i)→ℂ) :
    (∑h:∀i,F i,weight h)=
      ∑A∈(Finset.univ:Finset ι).powerset,∑h∈activeStratum F A,weight h := by
  classical
  symm
  simp only [activeStratum,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  let A:Finset ι:=Finset.univ.filter (fun i=>h i≠0)
  have he : ∀i,h i≠0↔i∈A := by intro i;simp [A]
  rw [Finset.sum_eq_single A]
  · simp only [he,implies_true,ite_true]
  · intro B hB hBA
    have hbad : ¬(∀i,h i≠0↔i∈B) := by
      intro hgood
      apply hBA
      ext i
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using (hgood i).symm
    simp only [hbad,ite_false]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim

end FixedRayActiveSet

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


end LocalReflectionBrackets

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    ramifiedTraceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(paperLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=paperLambda*((paperLambdaUnit⁻¹:Eisˣ)*q)
  rw [paperLambda_eq,hq]
  have hu : (paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel paperLambdaUnit)
  calc
    _=(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

def paperLambdaQuotient (h:Eis) : Eis :=
  if hh:ramifiedTraceLambda∣h then hh.choose else 0

lemma paperLambdaQuotient_mul (h:Eis) (hh:ramifiedTraceLambda∣h) :
    ramifiedTraceLambda*paperLambdaQuotient h=h := by
  simp only [paperLambdaQuotient,dif_pos hh]
  exact hh.choose_spec.symm


def sourceCuspPhaseNumerator (j:Fin 3) (u h:Eis) : Eis :=
  if j=0 then ramifiedTraceLambda*u^2*h else -u^2*paperLambdaQuotient h


end CubicEisenstein

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve QuadraticAllOddCRT
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def cubicTwoSupplement : Eis→*ℂ where
  toFun n:=(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]

def quadraticTwoSupplement : Eis→*ℂ :=
  InitialMeanSquare.normCharacter (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

def twoSupplement : Eis→*ℂ := cubicTwoSupplement^2*quadraticTwoSupplement

lemma cubicTwoSupplement_norm (n:Eis) : ‖cubicTwoSupplement n‖≤1 := by
  change ‖(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal n)‖≤1
  exact FiniteRayExpansion.norm_char_le_one _ _


lemma cubicTwoSupplement_periodic (x y:Eis) (hxy:x-y∈Ideal.span {(8:Eis)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2:x-y∈cubicTwoIdeal:=by
    obtain ⟨k,hk⟩:=Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4*k,?_⟩
    change x-y=(-2:Eis)*(-4*k)
    rw [hk]
    ring
  change (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal x)=
    (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]


end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def supportedIdealRow (a:Eis) : Eis→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs:Supported (1:Ideal Eis):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:Eis)}=(1:Ideal Eis) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],
      if_pos hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

lemma supportedIdealRow_norm (a n:Eis) : ‖supportedIdealRow a n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

lemma exists_supported_primary_unit (x:Eis) (hx:Supported (Ideal.span {x})) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:=supported_primaryGenerator_ne_zero (Ideal.span {x}) hx
  have hp:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hp.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  have he:u.val*x=primaryGenerator (Ideal.span {x}):=by simpa only [mul_comm] using hu
  rw [he]
  exact hp.2


lemma supportedIdealRow_lambda_primary (n:Eis) (hs:Supported (Ideal.span {n})) :
    supportedIdealRow lambda n=idealRowHom lambda (Ideal.span {n}) := by
  change (if Supported (Ideal.span {n}) then _ else _)=_
  rw [if_pos hs]

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma negative_two_prime : Prime (-2:Eis) :=
  (Ideal.span_singleton_prime (by norm_num : (-2:Eis)≠0)).mp
    (show (Ideal.span {(-2:Eis)}).IsPrime from cubicTwoIdeal_isMaximal.isPrime)


end


end CanonicalRowCompletion

end

end OAI

end


