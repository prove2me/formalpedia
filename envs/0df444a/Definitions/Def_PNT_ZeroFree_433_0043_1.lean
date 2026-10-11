-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0043_1
-- name    : PNT_ZeroFree_433_0043_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:41:55.80752+00:00
-- url     : https://prove2.me/theorems/ff1d80bf-6748-4763-ac79-e2d6223dfd24
-- title:
--   Zero-free region foundations: GaussSum.ActiveConductor [0043_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.ActiveConductor
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ActiveConductor.lean#L69-L347

import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0042

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ActiveConductor.lean
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

namespace ActualEisensteinCubic

section

 theorem activeSupport_nonempty_of_ne {α : Type*} [DecidableEq α]
    {S T : Finset α} (h : S ≠ T) : (activeSupport S T).Nonempty := by
  by_contra hn
  apply h
  have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  ext i
  simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
  exact ⟨fun hi => he.1 hi, fun hi => he.2 hi⟩

 theorem activeRow_zero_of_ne {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) {S T : Finset α} (h : S ≠ T) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) 0 = 0 := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne h).to_subtype
  exact finiteSexticRow_zero _ _ _

open ConcreteTraceCRT EisensteinSchwartzPoisson

 theorem finiteSexticRow_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 1 := by
  simp [finiteSexticRow]

 theorem finitePrimeModulus_norm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) : ‖eisEmbedding (finitePrimeModulus P)‖ = 1 := by
  have h := finitePrimeModulus_norm_sq P
  simp only [Finset.univ_eq_empty, Finset.prod_empty, map_one, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (finitePrimeModulus P))]

 theorem canonicalGaussSum_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalGaussSum P hcop hgood j = 1 := by
  let c := finitePrimeModulus P
  have hc : Ideal.span {c} = ⊤ := by
    simpa only [c, Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top] using
      span_finitePrimeModulus P
  have hzero (r : O ⧸ Ideal.span {c}) : r = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hc]; trivial)
  let : Subsingleton (O ⧸ Ideal.span {c}) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  unfold canonicalGaussSum
  change (∑ r : O ⧸ Ideal.span {c}, _ ) = 1
  rw [Fintype.sum_subsingleton _ 0]
  simp [principalSexticRow, finiteSexticQuotientRow]

 theorem canonicalNormalizedGauss_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j = 1 := by
  rw [canonicalNormalizedGauss, canonicalGaussSum_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, div_one]

noncomputable def squarefreePairPoissonZeroMode
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
        (star (row 0) * paperRadialFourier W 0)

 theorem squarefreePairPoissonZeroMode_eq_zero_of_ne
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    {S T : Finset ι} (hST : S ≠ T) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S T W scale = 0 := by
  simp only [squarefreePairPoissonZeroMode, activeRow_zero_of_ne P hgood hST,
    star_zero, zero_mul, mul_zero, Finset.sum_const_zero]

 theorem squarefreePairPoissonZeroMode_diag
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ) := by
  have hempty : activeSupport S S = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport S S) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [squarefreePairPoissonZeroMode, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    Finset.inter_self, finiteSexticRow_of_isEmpty, star_one, one_mul]
  rw [← Finset.sum_mul]
  have hn (E : Finset ι) : ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
      (ConcretePrimeRowBridge.span_idealGenerator _)
  simp_rw [hn, Complex.ofReal_natCast]
  ring

end

open EisensteinSchwartzPoisson

theorem primeSubset_moebius_norm_sum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  simp only [Finset.prod_const_one, mul_one,  map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

theorem primeDensity_nonneg_le_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    0 ≤ (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ∧
      (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ≤ 1 := by
  have hfactor (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (P i) ∧
      1 - (1 : ℝ) / Ideal.absNorm (P i) ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Ideal.absNorm (P i) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (P i)))
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hnorm)
    · have : 0 ≤ (1 : ℝ) / Ideal.absNorm (P i) := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i _ => (hfactor i).1),
    Finset.prod_le_one (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)⟩

theorem squarefreePairPoissonZeroMode_diag_product
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [squarefreePairPoissonZeroMode_diag, primeSubset_moebius_norm_sum P hprime hinj]

theorem norm_squarefreePairPoissonZeroMode_diag_le
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖squarefreePairPoissonZeroMode P hinj hgood S S W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ := by
  rw [squarefreePairPoissonZeroMode_diag_product P hprime]
  have hp : (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) =
      ((∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) : ℝ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hp, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeDensity_nonneg_le_one P S).1]
  exact mul_le_of_le_one_right (by positivity) (primeDensity_nonneg_le_one P S).2

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

noncomputable def idealPairPoissonZeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonZeroMode (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem weighted_idealPairPoissonZeroMode_eq_zero_of_ne
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F I ≠ idealSupport F J := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hI hJ hsI hsJ h)
      let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.1)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsJ]
  · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsI]

theorem idealRowSum_zeroMode_diagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
      idealPairPoissonZeroMode F hFpos hFgood I I W scale := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  · intro J hJ hJI
    exact weighted_idealPairPoissonZeroMode_eq_zero_of_ne F hFpos hFgood
      χ A hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem norm_idealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2 := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨I, hI, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have hb : ‖idealPairPoissonZeroMode F hFpos hFgood I I W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ :=
    norm_squarefreePairPoissonZeroMode_diag_le (fun i : primePool F => i.val)
      hprime Subtype.val_injective (primePool_good F hFgood) (idealSupport F I) W scale
  nlinarith [mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖)]

end ConcretePrimeRowBridge

open scoped BigOperators Classical SchwartzMap ContDiff
namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem activeRow_norm_le_one
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι) (h : O) :
    ‖finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) h‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (finiteSquarefreeRow_norm_le_one P hgood (S \ T) h)
      (finiteSquarefreeRow_norm_le_one P hgood (T \ S) h) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem activeRow_paperFourier_summable
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun h : O => star (finiteSexticRow (activePrimes P S T)
      (fun i => hgood i.val) (activeExponent S T) h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W scale hscale)
  intro h
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (activeRow_norm_le_one P hgood S T h)


end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson


end ConcretePrimeRowBridge

namespace ShortDraftHeckeBridge


end ShortDraftHeckeBridge

namespace ConcretePrimeRowBridge

section
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson


end

open ActualEisensteinCubic ShortDraftHeckeBridge


end ConcretePrimeRowBridge

namespace ActualEisensteinCubic


end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge


end ConcretePrimeRowBridge

end

end OAI

end


