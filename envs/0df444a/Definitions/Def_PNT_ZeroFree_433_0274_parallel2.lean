-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0274_parallel2
-- name    : PNT_ZeroFree_433_0274_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:06:16.559558+00:00
-- url     : https://prove2.me/theorems/b9f3a0e6-3131-4721-a54f-cd844009be18
-- title:
--   Zero-free region foundations: Cusp.ResiduePhases [0274_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduePhases.lean#L223-L551

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0011
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0122
import Definitions.Def_PNT_ZeroFree_433_0128
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0152_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel2
import Definitions.Def_PNT_ZeroFree_433_0210
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduePhases.lean
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


open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

lemma finiteAdditiveFourierCoeff_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (k h : R) :
    finiteAdditiveFourierCoeff (ψ.mulShift k) φ h=
      finiteAdditiveFourierCoeff ψ φ (k*h) := by
  unfold finiteAdditiveFourierCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [AddChar.mulShift_apply]
  congr 2
  ring

theorem finite_fourier_weighted_shift_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (ψi : ∀i,AddChar (R i) ℂ) (k : ∀i,(R i)ˣ)
    (hψ : ∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i ((k i:R i)*e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h := by
  rw [finite_fourier_weighted_crt R e ψ φ (fun i h=>κ i ((k i:R i)*h))]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hψ,finiteAdditiveFourierCoeff_mulShift]
  exact Equiv.sum_comp (k i).mulLeft
    (fun h:R i=>finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h)

theorem finiteAdditiveFourierCoeff_pair {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T≃+*R×S) (ψ : AddChar T ℂ) (φ : R→ℂ) (f : S→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun t=>φ (e t).1*f (e t).2) h=
      finiteAdditiveFourierCoeff (leftAddChar e ψ) φ (e h).1 *
      finiteAdditiveFourierCoeff (rightAddChar e ψ) f (e h).2 := by
  have hs : (∑x:T,(φ (e x).1*f (e x).2)*ψ (-h*x))=
      (∑x:R,φ x*leftAddChar e ψ (-(e h).1*x))*
        (∑y:S,f y*rightAddChar e ψ (-(e h).2*y)) := by
    calc
      _ = ∑x:T,(φ (e x).1*leftAddChar e ψ (-(e h).1*(e x).1))*
          (f (e x).2*rightAddChar e ψ (-(e h).2*(e x).2)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_crt_factor e ψ (-h*x)]
        simp only [map_mul,map_neg,Prod.fst_mul,Prod.snd_mul,Prod.fst_neg,Prod.snd_neg]
        ring
      _ = ∑x:R×S,(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)) :=
        Equiv.sum_comp e.toEquiv (fun x:R×S=>(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)))
      _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]
  have hc : (Fintype.card T:ℂ)=(Fintype.card R:ℂ)*(Fintype.card S:ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_prod,Nat.cast_mul]
  simp only [finiteAdditiveFourierCoeff,hs,hc]
  ring

end IdealGaussCRT

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O


theorem canonical_finite_reflection_shifted_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ)
    (ψi : ∀i,AddChar (Eis⧸P i) ℂ) (hψi : ∀i,(ψi i).IsPrimitive)
    (k : ∀i,(Eis⧸P i)ˣ)
    (hshift : ∀i,coordinateAddChar (fun i=>Eis⧸P i) e ψ i=(ψi i).mulShift (k i:Eis⧸P i))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let χ := fun i=>actualSextic (P i) (hg i)
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    rw [finite_fourier_weighted_shift_crt (fun i=>Eis⧸P i) e ψ ψi k hshift
      (fun i t=>(χ i^j i) t) (fun i=>frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i))]
    exact Fintype.prod_sum f
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (hψi i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl

end LocalReflectionBrackets

namespace FiniteGaussPhase


open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_factor {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) (H:Eis⧸Ideal.span {∏i,p i}) :
    finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H=
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i)
      ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i) := by
  rw [finiteAdditiveFourierCoeff_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productTraceShift_character,finiteAdditiveFourierCoeff_mulShift]

theorem product_trace_fourier_weighted {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ κ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H *
      ∏i,κ i ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∏i,∑h:Eis⧸Ideal.span {p i},finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) h*κ i h := by
  exact finite_fourier_weighted_shift_crt (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ κ

end FiniteGaussPhase

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O


theorem canonical_product_reflection_crt {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hchar : ∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (x : ∀i,Eis⧸Ideal.span {p i})
    [Fintype (Eis⧸Ideal.span {∏i,p i})] :
    let χ := fun i=>actualSextic (Ideal.span {p i}) (hg i)
    let ψ := quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let ψi := fun i=>quotientTrace (p i) (hp i)
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff ψ
      (principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
        (span_finset_prod Finset.univ p)) H *
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i)
        ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸Ideal.span {p i}):ℂ)⁻¹ else 0) := by
  let e:=productElementCRT p hcop
  have hrow : principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
      (span_finset_prod Finset.univ p)=
      fun t=>∏i,(actualSextic (Ideal.span {p i}) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_shifted_crt (fun i=>Ideal.span {p i}) e _
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop)
    hg hchar j hj σ ε x

end LocalReflectionBrackets

open scoped Classical BigOperators


namespace CubicEisenstein
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
lemma fixedThetaTwist_congr_primary (Ψ Φ:Eis→*ℂ)
    (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n) : fixedThetaTwist Ψ=fixedThetaTwist Φ := by
  funext n
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary Ψ n hn,fixedThetaTwist_primary Φ n hn,h n hn]
  · rw [fixedThetaTwist_not_primary Ψ n hn,fixedThetaTwist_not_primary Φ n hn]
end CubicEisenstein


end

end OAI

end


