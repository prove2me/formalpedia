-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0041
-- name    : PNT_ZeroFree_433_0041
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:23:33.452119+00:00
-- url     : https://prove2.me/theorems/e7b6d773-c269-4b74-8cef-30be1cb5a887
-- title:
--   Zero-free region foundations: PrimeRows.ActiveGaussFactorization [0041]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/ActiveGaussFactorization.lean#L64-L796

import Definitions.Def_PNT_ZeroFree_433_0040

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/ActiveGaussFactorization.lean#L64-L796
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
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

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT

theorem idealRowSum_smoothed_summable
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O => W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_summable
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    F (idealSupport F) (fun I => baseChangeWeight χ I * A (Ideal.absNorm I))
    W scale hscale

theorem idealRowSum_smoothed_expand
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        ∑' u : O, (star (idealSexticRow F hFpos hFgood I u) *
          idealSexticRow F hFpos hFgood J u) * W (‖eisEmbedding u‖ ^ 2 / scale) := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_expand
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    F (idealSupport F) (fun I => baseChangeWeight χ I * A (Ideal.absNorm I))
    W scale hscale

end ConcretePrimeRowBridge

open scoped BigOperators Classical
namespace ActualEisensteinCubic

def activeSupport {α : Type*} [DecidableEq α] (S T : Finset α) : Finset α :=
  (S \ T) ∪ (T \ S)

abbrev activePrimes {α : Type*} [DecidableEq α]
    (P : α → Ideal O) (S T : Finset α) (i : activeSupport S T) : Ideal O := P i.val

def activeExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 5 else 1

theorem activeExponent_ne_zero {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i ≠ 0 := by
  unfold activeExponent
  split_ifs <;> decide

theorem activeExponent_lt_six {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i < 6 := by
  unfold activeExponent
  split_ifs <;> decide

theorem activePrimes_injective {α : Type*} [DecidableEq α]
    (P : α → Ideal O) (hinj : Function.Injective P) (S T : Finset α) :
    Function.Injective (activePrimes P S T) := by
  intro a b h
  apply Subtype.ext
  exact hinj h

theorem activePrimes_pairwise_isCoprime {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S T : Finset α) :
    Pairwise (Function.onFun IsCoprime (activePrimes P S T)) := by
  intro a b hab
  exact Ideal.isCoprime_of_isMaximal (fun h => hab (activePrimes_injective P hinj S T h))

theorem finiteSexticRow_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val) (activeExponent S T) u =
      star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hpow5 (i : α) :
      (canonicalSextic (P i) (hgood i) ^ 5) (Ideal.Quotient.mk (P i) u) =
        star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)) := by
    rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    rw [canonicalSextic_conj_as_row_label]
    ring
  unfold finiteSexticRow activePrimes activeExponent
  let f : α → ℂ := fun i =>
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)
  change (∏ i : activeSupport S T, f i.val) = _
  rw [Finset.prod_coe_sort (s := activeSupport S T) (f := f)]
  change (∏ i ∈ (S \ T) ∪ (T \ S),
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)) = _
  rw [Finset.prod_union hd]
  simp only [finiteSquarefreeRow, star_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [if_pos hi, hpow5]
  · apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ S \ T := fun h => Finset.disjoint_left.mp hd h hi
    rw [if_neg hnot, pow_one]

theorem finiteSquarefreeRow_pair_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
          (activeExponent S T) u := by
  rw [finiteSexticRow_activeSupport P hgood S T u]
  have hk := finiteSquarefreeRow_pair_kernel P hgood S T u
  simpa only [mul_assoc] using hk

open ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def squarefreePairPoissonKernel
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem finiteSquarefreeRow_pair_radial_poisson
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, (star (finiteSquarefreeRow P hgood S u) *
      finiteSquarefreeRow P hgood T u) * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      squarefreePairPoissonKernel P hinj hgood S T W scale := by
  calc
    _ = ∑' u : O, rowCoprimeMask P (S ∩ T) u *
        finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
          (activeExponent S T) u * W (‖eisEmbedding u‖ ^ 2 / scale) := by
      apply tsum_congr
      intro u
      rw [finiteSquarefreeRow_pair_activeSupport]
    _ = _ := canonical_masked_radial_poisson_collected P hinj (S ∩ T)
      (activePrimes P S T) (activePrimes_pairwise_isCoprime P hinj S T)
      (fun i => hgood i.val) (fun i => hchar i.val)
      (activeExponent S T) (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
      W scale hscale

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def idealPairPoissonKernel
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonKernel (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem idealRowSum_smoothed_poisson
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.1) ≠ 2)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        idealPairPoissonKernel F hFpos hFgood I J W scale := by
  rw [idealRowSum_smoothed_expand F hFpos hFgood χ A W scale hscale]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_pair_radial_poisson
    (fun i : primePool F => i.1) Subtype.val_injective (primePool_good F hFgood)
    hchar (idealSupport F I) (idealSupport F J) W scale hscale

end ConcretePrimeRowBridge

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem gauss_sum_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ x) =
      ∏ i, gaussSum (χ i) (coordinateAddChar R e ψ i) := by
  classical
  calc
    _ = ∑ x : T, ∏ i, χ i (e x i) * coordinateAddChar R e ψ i (e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ x, Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, R i, ∏ i, χ i (x i) * coordinateAddChar R e ψ i (x i) :=
      Equiv.sum_comp e.toEquiv (fun x : ∀ i, R i =>
        ∏ i, χ i (x i) * coordinateAddChar R e ψ i (x i))
    _ = _ := by
      simpa only [gaussSum] using
        (Fintype.prod_sum (fun i (x : R i) => χ i x * coordinateAddChar R e ψ i x)).symm

end IdealGaussCRT

namespace FiniteGaussPhase

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def cofactor {ι : Type*} [Fintype ι] (p : ι → O) (i : ι) : O :=
  ∏ k ∈ Finset.univ.erase i, p k

theorem prime_mul_cofactor {ι : Type*} [Fintype ι]
    (p : ι → O) (i : ι) : p i * cofactor p i = ∏ k, p k :=
  Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

theorem span_finset_prod {ι : Type*} (s : Finset ι) (p : ι → O) :
    Ideal.span {∏ i ∈ s, p i} = ∏ i ∈ s, Ideal.span {p i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem cofactor_coprime {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) : IsCoprime (Ideal.span {p i}) (Ideal.span {cofactor p i}) := by
  rw [cofactor, span_finset_prod]
  exact IsCoprime.prod_right (fun k hk => hcop (Ne.symm (Finset.mem_erase.mp hk).1))

def productElementCRT {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    (O ⧸ Ideal.span {∏ i, p i}) ≃+* ∀ i, O ⧸ Ideal.span {p i} :=
  (Ideal.quotEquivOfEq (span_finset_prod Finset.univ p)).trans
    (IdealGaussCRT.quotientProdEquivPi (fun i => Ideal.span {p i}) hcop)

@[simp] theorem productElementCRT_mk {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (a : O) (i : ι) :
    productElementCRT p hcop (Ideal.Quotient.mk (Ideal.span {∏ k, p k}) a) i =
      Ideal.Quotient.mk (Ideal.span {p i}) a := by
  simp only [productElementCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    IdealGaussCRT.quotientProdEquivPi_mk]

theorem productElementCRT_axis {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (u v : O) (hbez : u * p i + v * cofactor p i = 1) (x : O) :
    (productElementCRT p hcop).symm (Pi.single i (Ideal.Quotient.mk (Ideal.span {p i}) x)) =
      Ideal.Quotient.mk (Ideal.span {∏ k, p k}) (x * v * cofactor p i) := by
  apply (productElementCRT p hcop).injective
  rw [RingEquiv.apply_symm_apply]
  funext k
  rw [productElementCRT_mk]
  by_cases hk : k = i
  · subst k
    simp only [Pi.single_eq_same, map_mul]
    have hlocal := IdealGaussCRT.bezout_inverse_left hbez
    calc
      Ideal.Quotient.mk (Ideal.span {p i}) x =
          Ideal.Quotient.mk (Ideal.span {p i}) x *
            (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i) *
              Ideal.Quotient.mk (Ideal.span {p i}) v) := by rw [hlocal, mul_one]
      _ = _ := by ring
  · have hd : p k ∣ cofactor p i := Finset.dvd_prod_of_mem p (by simp [hk])
    have hz : Ideal.Quotient.mk (Ideal.span {p k}) (cofactor p i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    simp only [Pi.single_eq_of_ne hk, map_mul, hz, mul_zero]

theorem coordinate_trace_character {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (u v : O) (hbez : u * p i + v * cofactor p i = 1) :
    IdealGaussCRT.coordinateAddChar (fun i => O ⧸ Ideal.span {p i}) (productElementCRT p hcop)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ k, p k) (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k))) i =
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (p i) (hp i)).mulShift (Ideal.Quotient.mk (Ideal.span {p i}) v) := by
  classical
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  change eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      (∏ k, p k) (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k)) ((productElementCRT p hcop).symm
        (Pi.single i (Ideal.Quotient.mk (Ideal.span {p i}) x))) =
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      (p i) (hp i) (Ideal.Quotient.mk (Ideal.span {p i}) v *
        Ideal.Quotient.mk (Ideal.span {p i}) x)
  rw [productElementCRT_axis p hcop i u v hbez x, ← map_mul,
    eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE]
  congr 1
  have hb : eisEmbedding (cofactor p i) ≠ 0 :=
    eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k _ => hp k))
  rw [← prime_mul_cofactor p i]
  simp only [map_mul]
  field_simp

theorem gauss_sum_product_element {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    [Fintype (O ⧸ Ideal.span {∏ i, p i})] [∀ i, Fintype (O ⧸ Ideal.span {p i})]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    (∑ x : O ⧸ Ideal.span {∏ i, p i},
      (∏ i, χ i (productElementCRT p hcop x i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) x) =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)) *
        gaussSum (χ i) (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i)) := by
  rw [IdealGaussCRT.gauss_sum_finite_crt]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨u, v, hbez⟩ := IdealGaussCRT.bezout_of_principal_coprime (cofactor_coprime p hcop i)
  rw [coordinate_trace_character p hp hcop i u v hbez]
  exact IdealGaussCRT.gauss_shift_bezout_left hbez (χ i) _

def normalizedProductTraceGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) : ℂ := by
  let hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  letI : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  exact (∑ x : O ⧸ Ideal.span {∏ i, p i},
    (∏ i, χ i (productElementCRT p hcop x i)) *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) hpall x) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)

theorem normalizedProductTraceGauss_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    normalizedProductTraceGauss p hp hcop χ =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)) *
        ConcreteBreveE.normalizedTraceGauss (p i) (hp i) (χ i) := by
  let hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let (i : ι) : Finite (O ⧸ Ideal.span {p i}) := finite_quotient_span (hp i)
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hn : (‖eisEmbedding (∏ i, p i)‖ : ℂ) = ∏ i, (‖eisEmbedding (p i)‖ : ℂ) := by
    rw [map_prod, norm_prod]
    norm_cast
  change (∑ x : O ⧸ Ideal.span {∏ i, p i},
    (∏ i, χ i (productElementCRT p hcop x i)) *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) hpall x) / (‖eisEmbedding (∏ i, p i)‖ : ℂ) = _
  rw [gauss_sum_product_element p hp hcop χ, hn, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change (_ * _) / _ = _ * (_ / _)
  ring

theorem normalizedProductTraceGauss_cross_factors {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    normalizedProductTraceGauss p hp hcop χ =
      (∏ i, ∏ k ∈ Finset.univ.erase i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i) (χ i) := by
  rw [normalizedProductTraceGauss_crt, Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [cofactor, map_prod]

def canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) : ℂ :=
  normalizedProductTraceGauss p hp hcop (fun i => canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i)

theorem canonicalProductGauss_cross_factors {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalProductGauss p hp hcop hgood j =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i) :=
  normalizedProductTraceGauss_cross_factors p hp hcop _

theorem canonicalProductGauss_constant_power {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ℕ) (hj : j ≠ 0) :
    canonicalProductGauss p hp hcop hgood (fun _ => j) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        canonicalSextic (Ideal.span {p i}) (hgood i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) ^ j *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j) := by
  rw [canonicalProductGauss_cross_factors]
  simp only [MulChar.pow_apply' _ hj, Finset.prod_pow]

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def angularFactor (a : O) : ℂ := eisEmbedding a / (‖eisEmbedding a‖ : ℂ)

theorem angularFactor_prod {ι : Type*} [Fintype ι] (p : ι → O) :
    angularFactor (∏ i, p i) = ∏ i, angularFactor (p i) := by
  unfold angularFactor
  rw [map_prod, norm_prod, Complex.ofReal_prod, Finset.prod_div_distrib]

def canonicalCrossFactor {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  ∏ i, ∏ k ∈ Finset.univ.erase i,
    canonicalSextic (Ideal.span {p i}) (hgood i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (p k))

theorem prime_generator_not_mem_other {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : p k ∉ Ideal.span {p i} := by
  intro h
  have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
  have ht := (hcop hik).sup_eq
  rw [sup_eq_left.mpr hle] at ht
  exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht

theorem canonicalCrossFactor_pow_six {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalCrossFactor p hgood ^ 6 = 1 := by
  unfold canonicalCrossFactor
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hnot := prime_generator_not_mem_other p hcop i k
    (Ne.symm (Finset.mem_erase.mp hk).1)
  simpa only [map_pow, if_neg hnot] using
    (canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hgood i) (p k))

def canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  star (angularFactor (∏ i, p i)) * canonicalProductGauss p hp hcop hgood (fun _ => 2)

theorem canonicalProductCoefficient_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalProductCoefficient p hp hcop hgood =
      canonicalCrossFactor p hgood ^ 2 *
        ∏ i, star (angularFactor (p i)) *
          ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
            (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2) := by
  rw [canonicalProductCoefficient, canonicalProductGauss_constant_power p hp hcop hgood 2
    (by decide), angularFactor_prod, star_prod, Finset.prod_mul_distrib]
  unfold canonicalCrossFactor
  ring

theorem product_moebius_eq_sign {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) =
      (-1 : ℂ) ^ Fintype.card ι := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k h
    by_contra hik
    have ht := (hcop hik).sup_eq
    rw [h, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [span_finset_prod]
  simpa only [Finset.card_univ] using
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj Finset.univ

theorem canonicalProductGauss_two_cube {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 2) ^ 3 =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        angularFactor (∏ i, p i) := by
  have hlocal (i : ι) :
      ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2) ^ 3 =
        -angularFactor (p i) := by
    change breveGamma2 (Ideal.span {p i}) (hgood i) (p i) rfl (hp i) ^ 3 = _
    simpa only [angularFactor, neg_div] using
      breveGamma2_cube (Ideal.span {p i}) (hgood i) (p i) rfl (hp i) (hprimary i)
  rw [canonicalProductGauss_constant_power p hp hcop hgood 2 (by decide),
    mul_pow, ← pow_mul]
  change canonicalCrossFactor p hgood ^ 6 * _ = _
  rw [canonicalCrossFactor_pow_six p hcop hgood, one_mul, ← Finset.prod_pow]
  simp_rw [hlocal]
  rw [Finset.prod_neg, product_moebius_eq_sign p hcop, angularFactor_prod]
  rfl

def canonicalProductG {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  (∏ i, canonicalSextic (Ideal.span {p i}) (hgood i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
    canonicalProductGauss p hp hcop hgood (fun _ => 3)

theorem canonicalProductGauss_one_two_relation {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      canonicalProductGauss p hp hcop hgood (fun _ => 2) =
      canonicalProductG p hp hcop hgood *
        canonicalProductGauss p hp hcop hgood (fun _ => 2) ^ 3 := by
  let g (j : ℕ) (i : ι) := ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
    (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j)
  let v (i : ι) := canonicalSextic (Ideal.span {p i}) (hgood i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O))
  have hlocal (i : ι) : g 1 i * g 2 i = (v i)⁻¹ * g 3 i * (g 2 i) ^ 3 := by
    simpa only [g, v, pow_one, ConcreteBreveE.normalizedTraceGauss,
      breveGamma1, breveGamma2, breveGamma3] using
      breveGamma1_gamma2_relation (Ideal.span {p i}) (hgood i) (hchar i)
        (p i) rfl (hp i) (hprimary i)
  have hprod : (∏ i, g 1 i) * (∏ i, g 2 i) =
      (∏ i, v i)⁻¹ * (∏ i, g 3 i) * (∏ i, g 2 i) ^ 3 := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [hlocal]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, Finset.prod_pow]
  rw [canonicalProductG,
    canonicalProductGauss_constant_power p hp hcop hgood 1 (by decide),
    canonicalProductGauss_constant_power p hp hcop hgood 2 (by decide),
    canonicalProductGauss_constant_power p hp hcop hgood 3 (by decide)]
  change (canonicalCrossFactor p hgood ^ 1 * ∏ i, g 1 i) *
    (canonicalCrossFactor p hgood ^ 2 * ∏ i, g 2 i) =
    ((∏ i, v i)⁻¹ * (canonicalCrossFactor p hgood ^ 3 * ∏ i, g 3 i)) *
      (canonicalCrossFactor p hgood ^ 2 * ∏ i, g 2 i) ^ 3
  rw [mul_pow, ← pow_mul]
  change _ = _ * (canonicalCrossFactor p hgood ^ 6 * _)
  rw [canonicalCrossFactor_pow_six p hcop hgood, one_mul]
  calc
    _ = canonicalCrossFactor p hgood ^ 3 * ((∏ i, g 1 i) * ∏ i, g 2 i) := by ring
    _ = _ := by rw [hprod]; ring

theorem canonicalProductGauss_one_two_eq_moebius {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      canonicalProductGauss p hp hcop hgood (fun _ => 2) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        angularFactor (∏ i, p i) * canonicalProductG p hp hcop hgood := by
  rw [canonicalProductGauss_one_two_relation p hp hcop hgood hchar hprimary,
    canonicalProductGauss_two_cube p hp hcop hgood hprimary]
  ring

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem angularFactor_mul_star (a : O) (ha : a ≠ 0) :
    angularFactor a * star (angularFactor a) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj', norm_angularFactor a ha]
  norm_num

theorem norm_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalProductGauss p hp hcop hgood j‖ = 1 := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ := fun i =>
    canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  have hχ : ∀ i, χ i ≠ 1 := fun i =>
    canonicalSextic_pow_ne_one (Ideal.span {p i}) (hgood i) (hchar i) (hj0 i) (hj6 i)
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq
    (fun i => O ⧸ Ideal.span {p i}) e χ ψ hχ
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ Ideal.span {p i}) e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      using eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  change ‖(∑ x : O ⧸ Ideal.span {c}, (∏ i, χ i (e x i)) * ψ x) /
    (‖eisEmbedding c‖ : ℂ)‖ = 1
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))

theorem norm_canonicalProductG {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    ‖canonicalProductG p hp hcop hgood‖ = 1 := by
  have h := congrArg norm
    (canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary)
  simp only [norm_mul, product_moebius_eq_sign p hcop, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_angularFactor _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))] at h
  rw [norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 1)
      (by intro; decide) (by intro; decide),
    norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 2)
      (by intro; decide) (by intro; decide), one_mul] at h
  exact h.symm

theorem canonicalProductCoefficient_mul_gauss_one {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductCoefficient p hp hcop hgood *
      canonicalProductGauss p hp hcop hgood (fun _ => 1) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        canonicalProductG p hp hcop hgood := by
  have hα := angularFactor_mul_star (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  unfold canonicalProductCoefficient
  calc
    _ = star (angularFactor (∏ i, p i)) *
        (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
          canonicalProductGauss p hp hcop hgood (fun _ => 2)) := by ring
    _ = _ := by
      rw [canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary]
      calc
        _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
            ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
              canonicalProductG p hp hcop hgood) := by ring
        _ = _ := by rw [hα, one_mul]

theorem moebius_star_gauss_one_eq_coefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) =
      (canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood := by
  have hα := angularFactor_mul_star (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hg : canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj',
      norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 1)
        (by intro; decide) (by intro; decide)]
    norm_num
  have hG : canonicalProductG p hp hcop hgood ≠ 0 := by
    intro hz
    have hn := norm_canonicalProductG p hp hcop hgood hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hA : canonicalProductCoefficient p hp hcop hgood =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
          canonicalProductG p hp hcop hgood := by
    unfold canonicalProductCoefficient
    calc
      _ = star (angularFactor (∏ i, p i)) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
            (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
              canonicalProductGauss p hp hcop hgood (fun _ => 2)) := by
        calc
          _ = (star (angularFactor (∏ i, p i)) *
              canonicalProductGauss p hp hcop hgood (fun _ => 2)) * 1 := by ring
          _ = _ := by rw [← hg]; ring
      _ = _ := by
        rw [canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary]
        calc
          _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
              ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
                star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
                  canonicalProductG p hp hcop hgood) := by ring
          _ = _ := by rw [hα, one_mul]
  rw [hA]
  field_simp

end FiniteGaussPhase

end

end OAI

end


