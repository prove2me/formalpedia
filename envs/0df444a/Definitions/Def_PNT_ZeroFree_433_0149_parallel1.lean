-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0149_parallel1
-- name    : PNT_ZeroFree_433_0149_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:48:26.762005+00:00
-- url     : https://prove2.me/theorems/5a6215d4-ae55-45db-a62e-4d101544ba4a
-- title:
--   Zero-free region foundations: MeanSquare.LogarithmicBins [0149_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L84-L528

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0012
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0079
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0221_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean
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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FourierBridge (logPhase)

def initialOuterWeight {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma initialOuterWeight_continuous {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (x : SecondExpansionData ι) :
    Continuous (fun q => initialOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => logPhase (q.1 + q.2.1) (z x)) :=
    (FourierBridge.logPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (FourierBridge.logPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold initialOuterWeight
  fun_prop

lemma initialOuterWeight_norm {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) :
    ‖initialOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [initialOuterWeight, norm_mul, FourierBridge.logPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def initialSourceSum (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2
    (sourceObservation p x).1 (-(sourceObservation p x).1) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem initialSource_eq_integrated
    (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSourceMode p hp hcop hg (𝓕 A₁) (𝓕 A₂) b s
        (initialOuterWeight V w z ud ue uv kap) F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : SecondExpansionData ι → Frequency → ℂ := fun x q =>
    initialOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ q.1 q.2.2 true) (sourceObservation p x).2 (sourceObservation p x).1) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ q.2.1 q.2.2 false) (sourceObservation p x).2 (-(sourceObservation p x).1)
  let M : SecondExpansionData ι → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true *
      rowMagnitude p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
  have hc (x : SecondExpansionData ι) : Continuous (Q x) := by
    have hw := initialOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : SecondExpansionData ι) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, initialOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, initialOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation


end

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]


omit [DecidableEq ι] in
lemma sourceRow_nonzero (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    (sourceObservation p x).1≠0 := mul_ne_zero (primeSubsetGenerator_ne_zero _ _) hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_span (x : SecondExpansionData ι) :
    Ideal.span {(sourceObservation p x).2}=
      (∏i∈x.divisor,Ideal.span {p i})*(∏i∈x.overlap,Ideal.span {p i}) := by
  simp only [sourceObservation,←Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,FiniteGaussPhase.span_finset_prod]


include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceQuotient_nonzero (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    secondExpansionQuotient p x≠0 := by
  rw [secondExpansionQuotient_of_subset p x hE]
  intro he
  have hh := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
  rw [he,mul_zero] at hh
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hh


end

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))


include hcop in
theorem sourceMask_coprime (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    IsCoprime (Ideal.span {secondExpansionQuotient p x})
      (Ideal.span {(sourceObservation p x).2}) := by
  rw [secondExpansionQuotient_of_subset p x hE,secondMaskQuotient_span,sourceLabel_span]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.mul_right
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => (Finset.mem_sdiff.mp hi).2 (he.symm ▸ hj))
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => Finset.disjoint_left.mp hV (Finset.mem_sdiff.mp hi).1 (he.symm ▸ hj))


end


end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem local_first_conductor_balance (parityBit e₁ e₂ : Bool) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      2*bit (!parityBit && e₁ && e₂)=bit e₁+bit e₂+bit parityBit := by
  cases parityBit <;> cases e₁ <;> cases e₂ <;> decide

theorem local_first_conductor_bound (parityBit e₁ e₂ : Bool) (n : ℕ) (hn : 0<n) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2*n := by
  have h : (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2 := by
    cases parityBit <;> cases e₁ <;> cases e₂ <;> decide
  omega

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

omit [DecidableEq ι] in
theorem firstActiveProduct_as_primeProduct (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)=
      primeProduct p S (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 then 0 else 1) := by
  unfold cubeActiveSupport primeProduct
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 <;> simp [h]

omit [DecidableEq ι] in
theorem first_conductor_product_balance (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)*dilationLabel p S v ε₁ ε₂*j2Label p S v ε₁ ε₂^2 =
      aLabel p S ε₁*aLabel p S ε₂*squarefreeLabel p S v := by
  rw [firstActiveProduct_as_primeProduct]
  simp only [dilationLabel,j2Label,aLabel,squarefreeLabel,primeProduct,← Finset.prod_pow,
    ← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  simpa only [evenDouble,mul_comm] using local_first_conductor_balance (parity (v i)) (ε₁ i) (ε₂ i)

variable [∀ i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by
  rw [firstActiveProduct_as_primeProduct,← primeProduct_add]
  simp only [dilationLabel,jLabel,aLabel,primeProduct,← Finset.prod_pow,← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  simpa only [mul_comm] using local_first_conductor_bound (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i) (v₁ i+v₂ i) (hv i hi)

variable (hp : ∀ i,p i≠0)


end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma first_row_numeric_bound (an en jn a1 a2 cn dn hn fn ell K B F : ℝ)
    (ha : 0≤an) (he : 0≤en) (hj : 0<jn) (h1 : 0<a1) (h2 : 0<a2) (hc : 0<cn)
    (hd : 0≤dn) (_hh : 0≤hn) (hf : 0≤fn) (hell : 0<ell) (hK : 0<K) (_hB : 0<B) (hF : 0<F)
    (hcon : an*en*jn≤a1*a2*B^4) (hfreq : hn≤ell^2*an*dn/(K*a1*a2*cn^2)) (hlabel : fn≤F) :
    hn*fn^2*en≤ell^2*B^4*F^2*dn/(K*cn^2*jn) := by
  have hratio : an*en/(a1*a2)≤B^4/jn := by
    apply (div_le_div_iff₀ (mul_pos h1 h2) hj).mpr
    nlinarith [hcon]
  calc
    hn*fn^2*en ≤ (ell^2*an*dn/(K*a1*a2*cn^2))*F^2*en := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul hfreq (pow_le_pow_left₀ hf hlabel 2) (sq_nonneg _) (by positivity)
    _ = (ell^2*dn*F^2/(K*cn^2))*(an*en/(a1*a2)) := by
      field_simp

    _ ≤ (ell^2*dn*F^2/(K*cn^2))*(B^4/jn) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring


end


end SecondPassArithmetic

end

end OAI

end


