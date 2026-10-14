-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0275_parallel2
-- name    : PNT_ZeroFree_433_0275_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:20:44.332022+00:00
-- url     : https://prove2.me/theorems/ccc45cfb-c781-4c83-89e4-7c74ed32b696
-- title:
--   Zero-free region foundations: ChineseRemainder.FrequencyLifts [0275_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/FrequencyLifts.lean#L104-L589

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0012
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0046_1
import Definitions.Def_PNT_ZeroFree_433_0046_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0046_2
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0214_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

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


theorem finiteCrossNumerator_fraction (a c l:Eis) (p h:ι→Eis)
    (hc:c≠0) (hp:∀i,p i≠0) :
    eisEmbedding (finiteCrossNumerator a c l p h)/eisEmbedding (c*∏i,p i)=
      eisEmbedding a/eisEmbedding c+eisEmbedding l^2*
        ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
  have hR:(∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hcC:=eisEmbedding_ne_zero hc
  have hRC:=eisEmbedding_ne_zero hR
  have hs:eisEmbedding (∑i,h i*cofactor p i)/eisEmbedding (∏i,p i)=
      ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
    rw [map_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi:=eisEmbedding_ne_zero (hp i)
    have hr:eisEmbedding (p i)*eisEmbedding (cofactor p i)=eisEmbedding (∏i,p i) := by
      rw [←map_mul,prime_mul_cofactor]
    rw [map_mul]
    apply (div_eq_div_iff hRC hpi).mpr
    linear_combination eisEmbedding (h i)*hr
  simp only [finiteCrossNumerator,map_add,map_mul,map_pow]
  rw [←hs]
  field_simp [hcC,hRC]

end ShortDraftCRT

open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

theorem finite_fourier_sum_reindex {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e:T≃+*∀i,R i)
    (ψ:AddChar T ℂ) (ψi:∀i,AddChar (R i) ℂ) (k:∀i,(R i)ˣ)
    (hψ:∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ:∀i,R i→ℂ) (weight:(∀i,R i)→ℂ) :
    (∑H:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H*
      weight (fun i=>(k i:R i)*e H i))=
    ∑h:∀i,R i,(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h := by
  let E:T≃(∀i,R i):=e.toEquiv.trans (Equiv.piCongrRight (fun i=>(k i).mulLeft))
  have hc (H:T) : finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H=
      ∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) ((k i:R i)*e H i) := by
    rw [finiteAdditiveFourierCoeff_crt]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hψ,finiteAdditiveFourierCoeff_mulShift]
  simp only [hc]
  exact Equiv.sum_comp E
    (fun h:∀i,R i=>(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h)

end IdealGaussCRT

namespace FiniteGaussPhase
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_sum_reindex {ι : Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ:∀i,(Eis⧸Ideal.span {p i})→ℂ)
    (weight:(∀i,Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H*
      weight (fun i=>(productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∑h:∀i,Eis⧸Ideal.span {p i},
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) (h i))*weight h := by
  exact finite_fourier_sum_reindex (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ weight

end FiniteGaussPhase


namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O


theorem canonical_active_stratum {ι : Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hchar:∀i,ringChar (Eis⧸P i)≠2)
    (ψ:∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (A:Finset ι) (j:ι→ℕ) (hj:∀i,j i<6)
    (σ ε:∀i,(Eis⧸P i)ˣ) (x:∀i,Eis⧸P i) :
    (∑h∈FixedRayActiveSet.activeStratum (fun i=>Eis⧸P i) A,
      ∏i,frequencyRow (actualSextic (P i) (hg i)) (ψ i) (j i) (σ i) (ε i) (x i) (h i))=
    (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i)*
      bracket (actualSextic (P i) (hg i)) (j i) (x i))*
    (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψ i) (hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψ i) (j i) (hj i) (σ i) (ε i) (x i)

end LocalReflectionBrackets


namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve QuadraticAllOddCRT
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O


lemma twoSupplement_norm (n:Eis) : ‖twoSupplement n‖≤1 := by
  change ‖cubicTwoSupplement n^2*quadraticTwoSupplement n‖≤1
  rw [norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    _).trans (InitialMeanSquare.normCharacter_norm_le_one _ n)
  exact pow_le_one₀ (norm_nonneg _) (cubicTwoSupplement_norm n)


lemma idealRowHom_two_prime (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hs:Supported (Ideal.span {p})) :
    idealRowHom (2:Eis) (Ideal.span {p})=twoSupplement p := by
  let:(Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  obtain ⟨hg,hc⟩:=supported_prime_data p hp hs
  have h2:idealRowHom (2:Eis) (Ideal.span {p})^2=cubicTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_four_eq_fixed_two (Ideal.span {p}) hg p rfl hprimary
    have hfour:Ideal.Quotient.mk (Ideal.span {p}) (4:Eis)=
      (Ideal.Quotient.mk (Ideal.span {p}) (2:Eis))^2:=by norm_num [map_ofNat]
    rw [hfour,map_pow] at he
    change (actualSextic (Ideal.span {p}) hg) (Ideal.Quotient.mk _ 2)^2=
      (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal p)
    rw [canonicalSextic_pow_two]
    exact he
  have h3:idealRowHom (2:Eis) (Ideal.span {p})^3=quadraticTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    change ((quadraticChar (Eis⧸Ideal.span {p}) (Ideal.Quotient.mk _ (2:Eis)):ℤ):ℂ)=_
    simp only [map_ofNat]
    rw [quadraticChar_two hc]
    have hn:Ideal.absNorm (Ideal.span {p})=Fintype.card (Eis⧸Ideal.span {p}):=by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    change ((ZMod.χ₈ (Fintype.card (Eis⧸Ideal.span {p})):ℤ):ℂ)=
      ((ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})):ℤ):ℂ)
    rw [hn]
  have hn2:(2:Eis)∉Ideal.span {p}:=by
    intro hz
    have he: (2:Eis⧸Ideal.span {p})=0:=by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact Ring.two_ne_zero hc he
  have h6:idealRowHom (2:Eis) (Ideal.span {p})^6=1:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_sixth_power_mask (Ideal.span {p}) hg (2:Eis)
    change actualSextic _ hg (Ideal.Quotient.mk _ ((2:Eis)^6))=_ at he
    simpa only [map_pow,if_neg hn2] using he
  calc
    _=idealRowHom (2:Eis) (Ideal.span {p})*idealRowHom (2:Eis) (Ideal.span {p})^6:=by rw [h6,mul_one]
    _=idealRowHom (2:Eis) (Ideal.span {p})^3*(idealRowHom (2:Eis) (Ideal.span {p})^2)^2:=by ring
    _=twoSupplement p:=by
      rw [h2,h3]
      change quadraticTwoSupplement p*cubicTwoSupplement p^2=cubicTwoSupplement p^2*quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n:Eis) (hn:lambda^2∣n-1)
    (hs:Supported (Ideal.span {n})) :
    idealRowHom (2:Eis) (Ideal.span {n})=twoSupplement n := by
  have hn0:n≠0:=by intro hz;apply hs.1;simp [hz]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty=>simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail:∀q∈s,Prime q ∧ lambda^2∣q-1:=fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit:Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}):=by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_two_prime p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

end


open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O


def reciprocityPhaseMonoid (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase r n
  map_one' := sexticReciprocityPhase_one_right r hr
  map_mul' := sexticReciprocityPhase_mul_right r


end CanonicalRowCompletion

end

end OAI

end


