-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0045
-- name    : PNT_ZeroFree_433_0045
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:44:40.870737+00:00
-- url     : https://prove2.me/theorems/a9b11d68-31d3-4ef9-8509-33886be27a4f
-- title:
--   Zero-free region foundations: GaussSum.MixedConversion [0045]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.MixedConversion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/MixedConversion.lean#L6-L742

import Definitions.Def_PNT_ZeroFree_433_0043
import Definitions.Def_PNT_ZeroFree_433_0044

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/MixedConversion.lean#L6-L742
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.MixedConversion
section
namespace OAI

private theorem integrable_inv_one_add_mul_sq {b : ℝ} (hb : b ≠ 0) :
    MeasureTheory.Integrable (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) :=
  (MeasureTheory.integrable_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) hb).2
    integrable_inv_one_add_sq

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

open scoped BigOperators Classical

namespace MixedGaussConversion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase

def localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (canonicalSextic (Ideal.span {p}) hg ^ j)

def localCoefficient (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  star (angularFactor p) * localGauss p hp hg 2

def localG (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  breveLocalG (Ideal.span {p}) hg p rfl hp

theorem norm_localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) : ‖localGauss p hp hg j‖ = 1 := by
  let q : Unit → O := fun _ => p
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})) := by
    intro i k hik
    exact (hik (Subsingleton.elim i k)).elim
  have h := norm_canonicalProductGauss q (fun _ => hp) hcop (fun _ => hg)
    (fun _ => hchar) (fun _ => j) (fun _ => hj0) (fun _ => hj6)
  rw [canonicalProductGauss_constant_power q (fun _ => hp) hcop (fun _ => hg) j hj0] at h
  simpa only [q, Fintype.prod_unique, Finset.univ_unique, Finset.erase_singleton,
    Finset.prod_empty, Finset.prod_singleton, one_pow, one_mul, localGauss] using h

theorem canonicalSextic_fifth_eq_inverse (p : O) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    canonicalSextic (Ideal.span {p}) hg ^ 5 = (canonicalSextic (Ideal.span {p}) hg)⁻¹ := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), ← MulChar.star_apply',
    canonicalSextic_conj_as_row_label]
  ring

theorem localGauss_five_eq (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    localGauss p hp hg 5 = breveGammaMinus1 (Ideal.span {p}) hg p rfl hp := by
  rw [localGauss, canonicalSextic_fifth_eq_inverse]
  rfl

theorem local_sign_conversion (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (-localGauss p hp hg 1) * star (localG p hp hg) = star (localCoefficient p hp hg) ∧
    (-localGauss p hp hg 5) * localG p hp hg =
      canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
        localCoefficient p hp hg := by
  have h := first_poisson_prime_sign_pairing (Ideal.span {p}) hg hchar p rfl hp hprimary 1
  dsimp only at h
  simp only [map_one, mul_one, inv_one] at h
  constructor
  · simpa only [localGauss, localG, localCoefficient, angularFactor, pow_one,
      ConcreteBreveE.normalizedTraceGauss, breveGamma1, breveGamma2, star_mul, star_star,
      mul_comm] using h.2.2.1
  · rw [localGauss_five_eq]
    exact h.2.1

theorem norm_localG (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) : ‖localG p hp hg‖ = 1 := by
  have h := congrArg norm (local_sign_conversion p hp hg hchar hprimary).1
  simp only [norm_mul, norm_neg, norm_star, localCoefficient] at h
  rw [norm_localGauss p hp hg hchar 1 (by decide) (by decide), one_mul,
    norm_angularFactor p hp,
    norm_localGauss p hp hg hchar 2 (by decide) (by decide), one_mul] at h
  exact h

def convertedLocal (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (inverse : Bool) : ℂ :=
  if inverse then
    (canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
      localCoefficient p hp hg) / localG p hp hg
  else star (localCoefficient p hp hg) / star (localG p hp hg)

theorem neg_localGauss_eq_converted (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) (inverse : Bool) :
    -localGauss p hp hg (if inverse then 5 else 1) = convertedLocal p hp hg inverse := by
  have hG : localG p hp hg ≠ 0 := by
    intro hz
    have hn := norm_localG p hp hg hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  cases inverse
  · exact (eq_div_iff (star_ne_zero.mpr hG)).mpr
      (local_sign_conversion p hp hg hchar hprimary).1
  · exact (eq_div_iff hG).mpr (local_sign_conversion p hp hg hchar hprimary).2

theorem moebius_mixed_gauss_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (inverse : ι → Bool) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      canonicalProductGauss p hp hcop hgood (fun i => if inverse i then 5 else 1) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
  rw [product_moebius_eq_sign p hcop, canonicalProductGauss_cross_factors]
  have hprod : (-1 : ℂ) ^ Fintype.card ι *
      (∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) =
      ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
    rw [← Finset.card_univ, ← Finset.prod_neg]
    apply Finset.prod_congr rfl
    intro i _
    exact neg_localGauss_eq_converted (p i) (hp i) (hgood i) (hchar i) (hprimary i) (inverse i)
  calc
    _ = (∏ i, ∏ k ∈ Finset.univ.erase i,
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
            (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ((-1 : ℂ) ^ Fintype.card ι *
          ∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) := by
      unfold localGauss
      ring
    _ = _ := by rw [hprod]

end MixedGaussConversion

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion

theorem pair_moebius_eq_active
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (S T : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ) =
      (UniqueFactorizationMonoid.moebius
        (Ideal.span {∏ i : activeSupport S T, p i.val}) : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hcop := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  rw [prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj T,
    product_moebius_eq_sign (fun i : activeSupport S T => p i.val) hcop, ← pow_add]
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have ha : Fintype.card (activeSupport S T) = (S \ T).card + (T \ S).card := by
    rw [Fintype.card_coe, activeSupport, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter S T
  have ht := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at ht
  have hcard : S.card + T.card = Fintype.card (activeSupport S T) + 2 * (S ∩ T).card := by omega
  rw [hcard, pow_add, pow_mul]
  norm_num

def activeConvertedGauss
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  (∏ i : activeSupport S T,
    ∏ k ∈ @Finset.erase (activeSupport S T)
      (fun a b => Classical.propDecidable (a = b)) Finset.univ i,
    (canonicalSextic (Ideal.span {p i.val}) (hgood i.val) ^ activeExponent S T i)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) *
    ∏ i : activeSupport S T,
      convertedLocal (p i.val) (hp i.val) (hgood i.val) (decide (i.val ∈ S \ T))

def activePairDualSeries
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let row := finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
    (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i : activeSupport S T, p i.val
  ∑ E ∈ (S ∩ T).powerset,
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, star (row h) * paperRadialFourier W
        (scale * ‖eisEmbedding h‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

def convertedPairPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  ((scale : ℂ) / (‖eisEmbedding (∏ i : activeSupport S T, p i.val)‖ : ℂ)) *
    activeConvertedGauss p hp hgood S T * activePairDualSeries p hgood S T W scale

theorem moebius_squarefreePairPoissonKernel_conversion
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have hg : (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
        (activeExponent S T) = activeConvertedGauss p hp hgood S T := by
    have he : activeExponent S T =
        (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
      funext i
      simp only [activeExponent, decide_eq_true_eq]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hQ (fun i => hgood i.val)
      (fun i => hchar i.val) (fun i => hprimary i.val) (fun i => decide (i.val ∈ S \ T))
  rw [pair_moebius_eq_active p hinj S T, squarefreePairPoissonKernel_eq_product p hp hinj hgood]
  change (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      (((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
        (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
          activePairDualSeries p hgood S T W scale) = _
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
          canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
            (activeExponent S T)) * activePairDualSeries p hgood S T W scale := by ring
    _ = _ := by rw [hg]; rfl

theorem moebius_pair_radial_poisson_converted
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      (∑' z : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood S z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood T z) *
          W (‖eisEmbedding z‖ ^ 2 / scale)) =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  rw [finiteSquarefreeRow_pair_radial_poisson (fun i => Ideal.span {p i}) hinj hgood hchar
    S T W scale hscale]
  exact moebius_squarefreePairPoissonKernel_conversion p hp hinj hgood hchar hprimary S T W scale

theorem moebius_pair_kernel_conversion_of_generators
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (p : ι → O) (hP : ∀ i, P i = Ideal.span {p i}) (hp : ∀ i, p i ≠ 0)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    letI : ∀ i, (Ideal.span {p i}).IsMaximal := fun i =>
      (hP i) ▸ (inferInstance : (P i).IsMaximal)
    let hg : ∀ i, lambda ∉ Ideal.span {p i} := fun i => (hP i) ▸ hgood i
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, P i) : ℂ)) *
      squarefreePairPoissonKernel P hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hg S T W scale := by
  have hPeq : P = fun i => Ideal.span {p i} := funext hP
  subst P
  exact moebius_squarefreePairPoissonKernel_conversion p hp hinj hgood hchar hprimary S T W scale

end GaussGeneratorTransport

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def mobiusIdealColumn (C : Ideal O → ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * C I

noncomputable def conjugateIdealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) : ℂ :=
  ∑ I ∈ F, mobiusIdealColumn C I * star (idealSexticRow F hFpos hFgood I y)

theorem conjugateIdealRowSum_eq_star
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) :
    conjugateIdealRowSum F hFpos hFgood C y =
      star (∑ I ∈ F, star (mobiusIdealColumn C I) * idealSexticRow F hFpos hFgood I y) := by
  simp only [conjugateIdealRowSum, star_sum, star_mul, star_star, mul_comm]

theorem conjugateIdealRowSum_smoothed_summable
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun y : O => W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_summable
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale

theorem conjugateIdealRowSum_smoothed_poisson
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonKernel F hFpos hFgood J I W scale := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  change (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
    (↑(‖∑ I ∈ F, star (mobiusIdealColumn C I) *
      finiteSquarefreeRow (fun i : primePool F => i.val) (primePool_good F hFgood)
        (idealSupport F I) y‖ ^ 2) : ℂ)) = _
  rw [finiteSquarefreeRow_smoothed_mean_square_expand
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteSquarefreeRow_pair_radial_poisson
    (fun i : primePool F => i.val) Subtype.val_injective (primePool_good F hFgood)
    hchar (idealSupport F J) (idealSupport F I) W scale hscale, star_star]
  rw [mul_comm (mobiusIdealColumn C J)]
  rfl

theorem mobiusIdealColumn_eq_zero_of_not_squarefree
    (C : Ideal O → ℂ) {I : Ideal O} (hI : ¬ Squarefree I) :
    mobiusIdealColumn C I = 0 := by
  simp only [mobiusIdealColumn, UniqueFactorizationMonoid.moebius_of_not_squarefree hI,
    Int.cast_zero, zero_mul]

theorem conjugateIdealRowSum_zeroMode_offDiagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
      idealPairPoissonZeroMode F hFpos hFgood J I W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F J ≠ idealSupport F I := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hJ hI hsJ hsI h).symm
      let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood J I W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.val)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [mobiusIdealColumn_eq_zero_of_not_squarefree C hsJ]
  · simp [mobiusIdealColumn_eq_zero_of_not_squarefree C hsI]

theorem conjugateIdealRowSum_zeroMode_formula
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [idealPairPoissonZeroMode_diag, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    change (star _ * _) * _ = _ * ((star _ * _) * _)
    ring
  · intro J hJ hJI
    exact conjugateIdealRowSum_zeroMode_offDiagonal F hFpos hFgood C hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem conjugateIdealRowSum_smoothed_poisson_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
          idealPairPoissonNonzeroMode F hFpos hFgood J I W scale := by
  rw [conjugateIdealRowSum_smoothed_poisson F hFpos hFgood hchar C W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [conjugateIdealRowSum_zeroMode_formula F hFpos hFgood C W scale]

theorem norm_mobiusIdealColumn_le (C : Ideal O → ℂ) (I : Ideal O) :
    ‖mobiusIdealColumn C I‖ ≤ ‖C I‖ := by
  by_cases hI : Squarefree I
  · simp only [mobiusIdealColumn, hI.moebius_eq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_refl]
  · rw [mobiusIdealColumn_eq_zero_of_not_squarefree C hI, norm_zero]
    exact norm_nonneg _

theorem norm_conjugateIdealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖C I‖ ^ 2 := by
  rw [conjugateIdealRowSum_zeroMode_formula F hFpos hFgood C W scale,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (idealPrimeDensity_mem_Icc F hFpos I).1]
  calc
    _ ≤ ‖mobiusIdealColumn C I‖ ^ 2 := mul_le_of_le_one_right
      (sq_nonneg _) (idealPrimeDensity_mem_Icc F hFpos I).2
    _ ≤ ‖C I‖ ^ 2 := by gcongr; exact norm_mobiusIdealColumn_le C I

theorem norm_secondPoisson_zeroMode_fixed_factors
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (ξ ρ : Ideal O → ℂ) (A : ℕ → ℂ)
    (hξ : ∀ I ∈ F, ‖ξ I‖ ≤ 1) (hρ : ∀ I ∈ F, ‖ρ I‖ ≤ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    let C : Ideal O → ℂ := fun I => ξ I * ρ I * A (Ideal.absNorm I)
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  dsimp only
  refine (norm_conjugateIdealRowSum_zeroMode_le F hFpos hFgood
    (fun I => ξ I * ρ I * A (Ideal.absNorm I)) W scale).trans ?_
  gcongr with I hI
  simp only [norm_mul]
  calc
    ‖ξ I‖ * ‖ρ I‖ * ‖A (Ideal.absNorm I)‖ ≤
        1 * 1 * ‖A (Ideal.absNorm I)‖ := by gcongr; exact hξ I hI; exact hρ I hI
    _ = _ := by ring

end ConcretePrimeRowBridge

open MeasureTheory Set
open scoped BigOperators

namespace EisensteinSchwartzPoisson

theorem scaled_cauchy_antitone (b : ℝ) :
    AntitoneOn (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg b, sq_nonneg (y - x),
    mul_nonneg (sq_nonneg b) (show 0 ≤ y ^ 2 - x ^ 2 by nlinarith)]

theorem scaled_cauchy_nat_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / (2 * b) := by
  have hi := (integrable_inv_one_add_mul_sq hb.ne').integrableOn (s := Ioi 0)
  have ht := (scaled_cauchy_antitone b).tsum_le_integral hi
    (fun t ht => by positivity)
  have he : (∫ x : ℝ in Ioi 0, (1 + (b * x) ^ 2)⁻¹) = Real.pi / (2 * b) := by
    rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
      smul_eq_mul]
    ring
  simpa [he] using ht

theorem summable_scaled_cauchy_nat (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℕ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  exact (scaled_cauchy_antitone b).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_mul_sq hb.ne').integrableOn (fun _ _ => by positivity)

theorem summable_scaled_cauchy_int (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_scaled_cauchy_nat b hb
  · simpa [mul_neg] using summable_scaled_cauchy_nat b hb

theorem scaled_cauchy_int_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / b := by
  have hs := summable_scaled_cauchy_nat b hb
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      (1 + (b * ((-(n + 1) : ℤ) : ℝ)) ^ 2)⁻¹) := by
    convert! hs1 using 1
    ext n
    push_cast
    congr 1
    ring
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹)
    (by simpa only [Int.cast_natCast] using hs) hneg]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, mul_neg,
    neg_sq]
  have hz := hs.tsum_eq_zero_add
  have he : (∑' n : ℕ, (1 + (b * (↑n + 1)) ^ 2)⁻¹) =
      (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hz.symm
  rw [he]
  have := scaled_cauchy_nat_bound b hb
  have hh : Real.pi / (2 * b) = (Real.pi / b) / 2 := by ring
  rw [hh] at this
  linarith

open ConcreteTraceCRT ActualEisensteinCubic

theorem scaled_eisenstein_cauchy_summable (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hp.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (b * (p.1 : ℝ)) (b * (p.2 : ℝ))
    (K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (by positivity)
  change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
    K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]

theorem scaled_eisenstein_cauchy_bound (K : ℝ) (hK : 0 < K) :
    (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi / Real.sqrt K) ^ 2 := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have he : (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) =
      ∑' p : ℤ × ℤ, ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹ :=
    (latticeCoordEquiv.symm.tsum_eq _).symm
  rw [he]
  calc
    _ ≤ ∑' p : ℤ × ℤ, 4 * ((1 + (b * (p.1 : ℝ)) ^ 2)⁻¹ *
          (1 + (b * (p.2 : ℝ)) ^ 2)⁻¹) := by
      apply ((latticeCoordEquiv.symm.summable_iff).mpr
        (scaled_eisenstein_cauchy_summable K hK)).tsum_le_tsum _ (hp.mul_left 4)
      intro p
      apply inverse_square_le_cauchy_product _ _ _ (by positivity)
      change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
        K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
      rw [eisEmbedding_eval_norm_sq]
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
    _ = 4 * (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ^ 2 := by
      rw [tsum_mul_left, ← hs.tsum_mul_tsum hs hp, pow_two]
    _ ≤ 4 * (1 + Real.pi / b) ^ 2 := by
      gcongr
      exact scaled_cauchy_int_bound b hb

theorem scaled_eisenstein_cauchy_small (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    K * (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi) ^ 2 := by
  have hs := scaled_eisenstein_cauchy_bound K hK
  have hb : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hb1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
  have hsq := Real.sq_sqrt hK.le
  calc
    _ ≤ K * (4 * (1 + Real.pi / Real.sqrt K) ^ 2) :=
      mul_le_mul_of_nonneg_left hs hK.le
    _ = 4 * (Real.sqrt K + Real.pi) ^ 2 := by
      nth_rw 1 [← hsq]
      field_simp
    _ ≤ _ := by gcongr

theorem one_le_eisenstein_norm_sq (h : O) (hh : h ≠ 0) :
    1 ≤ ‖eisEmbedding h‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {h}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hh)

theorem cauchy_large_scale_pointwise (K q : ℝ) (hK : 1 ≤ K) (hq : 1 ≤ q) :
    K * ((1 + K * q) ^ 2)⁻¹ ≤ 4 * ((1 + q) ^ 2)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have h1 : K * (1 + q) ≤ 2 * (1 + K * q) := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ K * (1 + q)) h1 2
  have h3 : K * (1 + q) ^ 2 ≤ K ^ 2 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (1 + q)]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + K * q) ^ 2)
    (by positivity : 0 < (1 + q) ^ 2)).mpr
  nlinarith

theorem lattice_profile_nonzero_scaled_bound
    (F : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * ‖F t‖ ≤ B)
    (K : ℝ) (hK : 0 < K) :
    K * (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * B := by
  have hm (h : O) : ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      B * ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hF (K * ‖eisEmbedding h‖ ^ 2) (by positivity)
  have hs := scaled_eisenstein_cauchy_summable K hK
  have hf : Summable (fun h : O => ‖F (K * ‖eisEmbedding h‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hm (hs.mul_left B)
  have hsub := hf.subtype (fun h : O => h ≠ 0)
  have hc := eisenstein_cauchy_summable.subtype (fun h : O => h ≠ 0)
  by_cases hK1 : K ≤ 1
  · have htotal : (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        ∑' h : O, ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ :=
      hsub.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf
    have hbound := hf.tsum_le_tsum hm (hs.mul_left B)
    rw [tsum_mul_left] at hbound
    calc
      _ ≤ K * (B * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (htotal.trans hbound) hK.le
      _ = B * (K * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by ring
      _ ≤ B * (4 * (1 + Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_eisenstein_cauchy_small K hK hK1) hB
      _ ≤ _ := by nlinarith [eisensteinCauchyMass_nonneg]
  · have hp (h : {h : O // h ≠ 0}) :
        K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
      calc
        _ ≤ K * (B * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hm h.val) hK.le
        _ = B * (K * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
        _ ≤ B * (4 * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (cauchy_large_scale_pointwise K _
            (le_of_not_ge hK1) (one_le_eisenstein_norm_sq h.val h.property)) hB
        _ = _ := by ring
    calc
      _ = ∑' h : {h : O // h ≠ 0}, K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left.symm
      _ ≤ ∑' h : {h : O // h ≠ 0}, (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
        (hsub.mul_left K).tsum_le_tsum hp (hc.mul_left (4 * B))
      _ = (4 * B) * ∑' h : {h : O // h ≠ 0}, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (4 * B) * eisensteinCauchyMass := mul_le_mul_of_nonneg_left
        (eisensteinCauchyMass_subtype (fun h : O => h ≠ 0)) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (1 + Real.pi)]

theorem paperRadialFourier_nonzero_lattice_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (K : ℝ), 0 < K →
        K * (∑' h : {h : O // h ≠ 0},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨s, (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * C, ?_, ?_⟩
  · have := eisensteinCauchyMass_nonneg
    have := Real.pi_pos
    positivity
  · intro W K hK
    simpa only [mul_assoc] using lattice_profile_nonzero_scaled_bound
      (paperRadialFourier W) (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
        (by positivity) (hb W) K hK

end EisensteinSchwartzPoisson

end

end OAI

end


