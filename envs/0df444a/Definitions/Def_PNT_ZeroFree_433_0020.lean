-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0020
-- name    : PNT_ZeroFree_433_0020
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:39:20.787743+00:00
-- url     : https://prove2.me/theorems/5ec7e67b-b897-4cab-8d9b-c0f04a53728b
-- title:
--   Zero-free region foundations: Poisson.GaussianMoments [0020]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.GaussianMoments
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L21-L573

import Definitions.Def_PNT_ZeroFree_433_0019

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L21-L573
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Poisson.GaussianMoments
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

namespace GaussianMoment

theorem x_exp_neg_le (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

theorem gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by
  have h := x_exp_neg_le (t * q) (mul_nonneg ht.le hq)
  have hpos : 0 ≤ t := ht.le
  calc
    q * Real.exp (-t * q) =
        ((t * q) * Real.exp (-(t * q))) / t := by
          field_simp
    _ ≤ (2 * Real.exp (-(t * q / 2))) / t :=
      div_le_div_of_nonneg_right h hpos
    _ = (2 / t) * Real.exp (-(t * q / 2)) := by ring

end GaussianMoment
namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

theorem rational_sixth_row_approx_two_factors
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, r ∈ P i) → a ∣ n ∨ b ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
      (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by
  classical
  let Bad := columns.filter (fun n => ∃ i ∈ support n, r ∈ P i)
  let Sa := columns.filter (fun n => a ∣ n)
  let Sb := columns.filter (fun n => b ∣ n)
  have hsub : Bad ⊆ Sa ∪ Sb := by
    intro n hn
    obtain ⟨hcol, hbad⟩ := Finset.mem_filter.mp hn
    rcases hfactor n hcol hbad with hna | hnb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcol, hna⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcol, hnb⟩)
  have hSa : Sa.card ≤ 64 * (D / qNat a + 1) :=
    finite_divisible_count a ha Sa D
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (by intro n hn; exact hcolnorm n (Finset.mem_filter.mp hn).1)
  have hSb : Sb.card ≤ 64 * (D / qNat b + 1) :=
    finite_divisible_count b hb Sb D
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (by intro n hn; exact hcolnorm n (Finset.mem_filter.mp hn).1)
  have hcard : Bad.card ≤
      64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) := by
    calc
      Bad.card ≤ (Sa ∪ Sb).card := Finset.card_le_card hsub
      _ ≤ Sa.card + Sb.card := Finset.card_union_le Sa Sb
      _ ≤ 64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) :=
        Nat.add_le_add hSa hSb
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
        ∑ n ∈ Bad, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight r
    _ ≤ ∑ n ∈ Bad, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (Bad.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by
      exact_mod_cast hcard

theorem rational_qNat (r : ℕ) (hr : r ≠ 0) :
    qNat (r : O) = r ^ 2 := by
  calc
    qNat (r : O) = Ideal.absNorm (Ideal.span {(r : O)}) :=
      qNat_eq_absNorm_span _
    _ = Nat.card (O ⧸ Ideal.span {(r : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = r ^ 2 := rational_modulus_card r hr

theorem rational_qNat_pow (r k : ℕ) (hr : r ≠ 0) :
    qNat ((r : O) ^ k) = (r ^ 2) ^ k := by
  induction k with
  | zero =>
      simpa using rational_qNat 1 (by decide)
  | succ k ih =>
      calc
        qNat ((r : O) ^ (k + 1)) =
            qNat ((r : O) ^ k) * qNat (r : O) := by
          rw [pow_succ, qNat_mul]
        _ = (r ^ 2) ^ k * (r ^ 2) := by rw [ih, rational_qNat r hr]
        _ = (r ^ 2) ^ (k + 1) := (pow_succ (r ^ 2) k).symm

theorem rational_sixth_injective :
    Function.Injective (fun r : ℕ => (r : O) ^ 6) := by
  intro r s hrs
  have hcast : ((r ^ 6 : ℕ) : O) = ((s ^ 6 : ℕ) : O) := by
    simpa only [Nat.cast_pow] using hrs
  exact Nat.pow_left_injective (by decide : 6 ≠ 0) (Nat.cast_injective hcast)

theorem rational_sixth_norm_interval
    (L r R : ℕ) (hr : r.Prime) (hL : L ≤ r) (hR : r ≤ R) :
    L ^ 12 ≤ qNat ((r : O) ^ 6) ∧
      qNat ((r : O) ^ 6) ≤ R ^ 12 := by
  rw [rational_qNat_pow r 6 hr.ne_zero]
  have hpow : (r ^ 2) ^ 6 = r ^ 12 := by ring
  rw [hpow]
  exact ⟨Nat.pow_le_pow_left hL 12, Nat.pow_le_pow_left hR 12⟩

theorem rational_qNat_eq_one_iff (x : O) : qNat x = 1 ↔ IsUnit x := by
  rw [qNat_eq_absNorm_span, Ideal.absNorm_eq_one_iff,
    Ideal.span_singleton_eq_top]

theorem rational_prime_factor_cases (r : ℕ) (hr : r.Prime) :
    (Ideal.span {(r : O)} : Ideal O).IsMaximal ∨
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧ (r : O) = a * b ∧
      qNat a = r ∧ qNat b = r ∧
      (Ideal.span {a} : Ideal O).IsMaximal ∧
      (Ideal.span {b} : Ideal O).IsMaximal := by
  have hru : ¬ IsUnit (r : O) := by
    rw [← rational_qNat_eq_one_iff, rational_qNat r hr.ne_zero]
    have htwo := hr.two_le
    nlinarith
  rcases irreducible_or_factor hru with hirr | ⟨a, b, hna, hnb, hab⟩
  · left
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  · right
    have hqa1 : qNat a ≠ 1 := by
      intro h
      exact hna ((rational_qNat_eq_one_iff a).mp h)
    have hqb1 : qNat b ≠ 1 := by
      intro h
      exact hnb ((rational_qNat_eq_one_iff b).mp h)
    have hqprod : qNat a * qNat b = r ^ 2 := by
      rw [← qNat_mul, ← hab, rational_qNat r hr.ne_zero]
    obtain ⟨hqa, hqb⟩ := (hr.mul_eq_prime_sq_iff hqa1 hqb1).mp hqprod
    have ha0 : a ≠ 0 := by
      intro h
      have hqa0 : qNat a = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqa] at hqa0
      exact hr.ne_zero hqa0
    have hb0 : b ≠ 0 := by
      intro h
      have hqb0 : qNat b = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqb] at hqb0
      exact hr.ne_zero hqb0
    have hpa : Prime a := by
      apply Ideal.prime_of_irreducible_absNorm_span ha0
      rw [← qNat_eq_absNorm_span, hqa]
      exact hr.prime.irreducible
    have hpb : Prime b := by
      apply Ideal.prime_of_irreducible_absNorm_span hb0
      rw [← qNat_eq_absNorm_span, hqb]
      exact hr.prime.irreducible
    exact ⟨a, b, ha0, hb0, hab, hqa, hqb,
      PrincipalIdealRing.isMaximal_of_irreducible hpa.irreducible,
      PrincipalIdealRing.isMaximal_of_irreducible hpb.irreducible⟩

theorem maximal_ideal_eq_span_of_mem
    (Q : Ideal O) (hQ : Q.IsMaximal) (a : O)
    (ha : (Ideal.span {a} : Ideal O).IsMaximal) (hamem : a ∈ Q) :
    Q = Ideal.span {a} := by
  have hle : (Ideal.span {a} : Ideal O) ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hamem
  exact (ha.eq_of_le hQ.ne_top hle).symm

theorem rational_prime_ideal_cover (r : ℕ) (hr : r.Prime) :
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      r ≤ qNat a ∧ r ≤ qNat b ∧
      ∀ (Q : Ideal O), Q.IsMaximal → (r : O) ∈ Q →
        Q = Ideal.span {a} ∨ Q = Ideal.span {b} := by
  rcases rational_prime_factor_cases r hr with hmax |
      ⟨a, b, ha0, hb0, hab, hqa, hqb, hma, hmb⟩
  · have hr0 : (r : O) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hq : qNat (r : O) = r ^ 2 := rational_qNat r hr.ne_zero
    have hrle : r ≤ r ^ 2 := by nlinarith [hr.two_le]
    refine ⟨(r : O), (r : O), hr0, hr0, ?_, ?_, ?_⟩
    · rw [hq]; exact hrle
    · rw [hq]; exact hrle
    · intro Q hQ hrQ
      exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ (r : O) hmax hrQ)
  · refine ⟨a, b, ha0, hb0, ?_, ?_, ?_⟩
    · rw [hqa]
    · rw [hqb]
    · intro Q hQ hrQ
      rw [hab] at hrQ
      rcases hQ.isPrime.mem_or_mem hrQ with haQ | hbQ
      · exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ a hma haQ)
      · exact Or.inr (maximal_ideal_eq_span_of_mem Q hQ b hmb hbQ)

end

theorem rational_prime_sixth_row_approx
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r : ℕ) (hr : r.Prime) (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤
      (128 * (D / r + 1) : ℕ) := by
  obtain ⟨a, b, ha0, hb0, hra, hrb, hcover⟩ :=
    rational_prime_ideal_cover r hr
  have hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, (r : O) ∈ P i) → a ∣ n ∨ b ∣ n := by
    intro n hn ⟨i, hi, hri⟩
    rcases hcover (P i) (inferInstance) hri with hPa | hPb
    · have hmem : n ∈ (Ideal.span {a} : Ideal O) := by
        rw [← hPa]
        exact hsupport n hn i hi
      exact Or.inl (Ideal.mem_span_singleton.mp hmem)
    · have hmem : n ∈ (Ideal.span {b} : Ideal O) := by
        rw [← hPb]
        exact hsupport n hn i hi
      exact Or.inr (Ideal.mem_span_singleton.mp hmem)
  have hrow := rational_sixth_row_approx_two_factors
    P hgood columns support weight (r : O) a b ha0 hb0 D
    hfactor hcolnorm hweight
  have hAdiv : D / ShortDraftLatticeCount.qNat a ≤ D / r :=
    Nat.div_le_div_left hra hr.pos
  have hBdiv : D / ShortDraftLatticeCount.qNat b ≤ D / r :=
    Nat.div_le_div_left hrb hr.pos
  have hnat :
      64 * (D / ShortDraftLatticeCount.qNat a + 1) +
      64 * (D / ShortDraftLatticeCount.qNat b + 1) ≤
      128 * (D / r + 1) := by omega
  exact hrow.trans (by exact_mod_cast hnat)

end ActualEisensteinCubic

open ActualEisensteinCubic

namespace RationalPrimeExtraction

noncomputable def selected (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime

theorem lower_count_and_extract
    [DecidableEq O] (A : O → ℂ) (rows : Finset O) (E B : ℝ) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (selected Y).image (fun r : ℕ => (r : O) ^ 6) ⊆ rows →
      (∀ r ∈ selected Y, ‖A 1 - A ((r : O) ^ 6)‖ ≤ E) →
      (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ B →
      (Real.log 2 / 20) * (Y / Real.log Y) * ‖A 1‖ ^ 2 ≤
        2 * B + 2 * ((selected Y).card : ℝ) * E ^ 2 := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  refine ⟨Y₀, ?_⟩
  intro Y hY hrows happrox hmean
  have hcard : (Real.log 2 / 20) * (Y / Real.log Y) ≤
      ((selected Y).card : ℝ) := hcount Y hY
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6)
      ((selected Y : Finset ℕ) : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hmain := ShortDraft.complex_row_extraction rows (selected Y)
    (fun r : ℕ => (r : O) ^ 6) A 1 E B hE hrows hinj happrox hmean
  have hsquared : 0 ≤ ‖A 1‖ ^ 2 := sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hcard hsquared).trans hmain

end RationalPrimeExtraction

namespace OscSpecial

private theorem real_quadratic_lower {u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (_hdet : 0 < u * v - w ^ 2)
    (x y : ℝ) :
    ((u * v - w ^ 2) / (u + v)) * (x ^ 2 + y ^ 2) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 := by
  have hsum : 0 < u + v := add_pos hu hv
  have hid :
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) -
        (u * v - w ^ 2) * (x ^ 2 + y ^ 2) =
      (u * x - w * y) ^ 2 + (w * x - v * y) ^ 2 := by ring
  have hsq := add_nonneg (sq_nonneg (u * x - w * y))
    (sq_nonneg (w * x - v * y))
  have hnum : (u * v - w ^ 2) * (x ^ 2 + y ^ 2) ≤
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) := by
    linarith
  have h : ((u * v - w ^ 2) * (x ^ 2 + y ^ 2)) / (u + v) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 :=
    (div_le_iff₀ hsum).2 (by simpa only [mul_comm] using hnum)
  simpa only [div_mul_eq_mul_div] using h

private theorem schur_eq_real_det_div {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    RankTwoComplex.schur a b d = (R : ℂ) / a := by
  unfold RankTwoComplex.schur
  rw [← hdet]
  field_simp [ha]

private theorem determinant_real_components {a b d : ℂ} {R : ℝ}
    (hdet : a * d - b ^ 2 = (R : ℂ)) :
    a.re * d.re - a.im * d.im - b.re ^ 2 + b.im ^ 2 = R ∧
    a.re * d.im + a.im * d.re - 2 * b.re * b.im = 0 := by
  constructor
  · have h := congrArg Complex.re hdet
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re] at h
    have hb : (b ^ 2).re = b.re ^ 2 - b.im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    rw [hb] at h
    linarith
  · have h := congrArg Complex.im hdet
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im] at h
    have hb : (b ^ 2).im = 2 * b.re * b.im := by
      rw [pow_two, Complex.mul_im]
      ring
    rw [hb] at h
    linarith

private theorem first_real_coefficients {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    (a⁻¹).re = a.re / Complex.normSq a ∧
    (RankTwoComplex.schur a b d).re = R * a.re / Complex.normSq a ∧
    (Complex.I * b / a).re =
      (b.re * a.im - b.im * a.re) / Complex.normSq a := by
  constructor
  · exact Complex.inv_re a
  constructor
  · rw [schur_eq_real_det_div ha hdet]
    simp [Complex.div_re]
  · rw [Complex.div_re]
    simp [Complex.mul_re, Complex.mul_im]
    ring

private theorem first_real_determinant {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    (a.re / Complex.normSq a) * (R * a.re / Complex.normSq a) -
      ((b.re * a.im - b.im * a.re) / Complex.normSq a) ^ 2 =
      (a.re * d.re - b.re ^ 2) / Complex.normSq a := by
  have hN : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  obtain ⟨hr, hi⟩ := determinant_real_components hdet
  have hid :
      R * a.re ^ 2 - (b.re * a.im - b.im * a.re) ^ 2 =
      (a.re ^ 2 + a.im ^ 2) * (a.re * d.re - b.re ^ 2) -
        a.im * a.re * (a.re * d.im + a.im * d.re - 2 * b.re * b.im) := by
    rw [← hr]
    ring
  rw [hi, mul_zero, sub_zero] at hid
  simp only [Complex.normSq_apply] at hN ⊢
  have hN' : a.re ^ 2 + a.im ^ 2 ≠ 0 := by simpa [pow_two] using hN
  field_simp [hN']
  nlinarith [hid]

private noncomputable def middleForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a⁻¹ * (z.1 : ℂ) ^ 2 -
    2 * (Complex.I * b / a) * (z.1 : ℂ) * (z.2 : ℂ) +
    RankTwoComplex.schur a b d * (z.2 : ℂ) ^ 2

private theorem middleForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (middleForm a b d z).re =
      (a⁻¹).re * (z.1 : ℝ) ^ 2 -
      2 * (Complex.I * b / a).re * (z.1 : ℝ) * (z.2 : ℝ) +
      (RankTwoComplex.schur a b d).re * (z.2 : ℝ) ^ 2 := by
  simp [middleForm, Complex.add_re, Complex.sub_re, Complex.mul_re, pow_two]

private theorem middleForm_exp (a b d : ℂ) (z : ℤ × ℤ) :
    RankTwoComplex.firstGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * middleForm a b d z) := by
  simp only [RankTwoComplex.firstGaussian, middleForm]
  rw [← Complex.exp_add]
  congr 1
  simp [div_eq_mul_inv]
  ring

private theorem firstGaussian_summable {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.firstGaussian a b d) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  let u : ℝ := a.re / Complex.normSq a
  let v : ℝ := R * a.re / Complex.normSq a
  let w : ℝ := (b.re * a.im - b.im * a.re) / Complex.normSq a
  have hu : 0 < u := div_pos ha hN
  have hv : 0 < v := div_pos (mul_pos hR ha) hN
  have hq : 0 < u * v - w ^ 2 := by
    dsimp [u, v, w]
    rw [first_real_determinant ha0 hdet]
    exact div_pos hpd hN
  let eps : ℝ := (u * v - w ^ 2) / (u + v)
  have heps : 0 < eps := div_pos hq (add_pos hu hv)
  have hcoeff := first_real_coefficients ha0 hdet
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (middleForm a b d z).re := by
    rw [middleForm_real, hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    exact real_quadratic_lower hu hv hq (z.1 : ℝ) (z.2 : ℝ)
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (middleForm a b d) heps hbound).congr (fun z => (middleForm_exp a b d z).symm)

private noncomputable def originalForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2

private theorem originalForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (originalForm a b d z).re =
      a.re * (z.1 : ℝ) ^ 2 + 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
      d.re * (z.2 : ℝ) ^ 2 := by
  simp [originalForm, Complex.add_re, Complex.mul_re, pow_two]

private theorem originalGaussian_summable {a b d : ℂ}
    (ha : 0 < a.re) (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.binaryGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := (a.re * d.re - b.re ^ 2) / (a.re + d.re)
  have heps : 0 < eps := div_pos hpd (add_pos ha hd)
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (originalForm a b d z).re := by
    rw [originalForm_real]
    dsimp [eps]
    convert! real_quadratic_lower (w := -b.re) ha hd (by simpa using hpd)
      (z.1 : ℝ) (z.2 : ℝ) using 1 <;> ring
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (originalForm a b d) heps hbound).congr (fun z => by rfl)

noncomputable def inverseForm (a b d : ℂ) (R : ℝ) (z : ℤ × ℤ) : ℂ :=
  (d * (z.1 : ℂ) ^ 2 - 2 * b * (z.1 : ℂ) * (z.2 : ℂ) +
    a * (z.2 : ℂ) ^ 2) / (R : ℂ)

private theorem inverseForm_real (a b d : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℤ × ℤ) :
    (inverseForm a b d R z).re =
      (d.re * (z.1 : ℝ) ^ 2 - 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
        a.re * (z.2 : ℝ) ^ 2) / R := by
  simp [inverseForm, Complex.div_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.normSq_apply, pow_two]
  field_simp [hR]

theorem dualGaussian_inverseForm {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : R ≠ 0)
    (hdet : a * d - b ^ 2 = (R : ℂ)) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * inverseForm a b d R z) := by
  unfold RankTwoComplex.dualGaussian
  rw [← Complex.exp_add]
  congr 1
  rw [schur_eq_real_det_div ha hdet]
  dsimp [inverseForm]
  have hdet0 : a * d - b ^ 2 ≠ 0 := by rw [hdet]; exact_mod_cast hR
  rw [← hdet]
  field_simp [ha, hdet0] ; ring

private theorem dualGaussian_summable {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.dualGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := ((d.re * a.re - b.re ^ 2) / (d.re + a.re)) / R
  have heps : 0 < eps := div_pos (div_pos (by nlinarith [hpd]) (add_pos hd ha)) hR
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (inverseForm a b d R z).re := by
    rw [inverseForm_real a b d hR.ne']
    have hbase := real_quadratic_lower (u := d.re) (v := a.re) (w := b.re)
      hd ha (by nlinarith [hpd]) (z.1 : ℝ) (z.2 : ℝ)
    have hdivide := div_le_div_of_nonneg_right hbase hR.le
    simpa [eps, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdivide
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (inverseForm a b d R) heps hbound).congr
      (fun z => (dualGaussian_inverseForm ha0 hR.ne' hdet z).symm)

theorem binary_gaussian_poisson_real_det {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  have hδ : 0 < (RankTwoComplex.schur a b d).re := by
    rw [schur_eq_real_det_div ha0 hdet]
    simpa [Complex.div_re] using div_pos (mul_pos hR ha) hN
  have hO := originalGaussian_summable ha hpd
  have hM := firstGaussian_summable ha hR hdet hpd
  have hD := dualGaussian_summable ha hR hdet hpd
  calc
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (RankTwoComplex.schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z :=
      RankTwoComplex.binary_gaussian_poisson ha hδ hO hM hD
    _ = (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
          ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
      rw [schur_eq_real_det_div ha0 hdet,
        SqrtBranch.prefactor_product ha hR]

noncomputable def q (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2
noncomputable def A (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * (b : ℂ) / (q a b : ℂ)
noncomputable def B (η a b : ℝ) : ℂ :=
  -(η : ℂ) / 2 - 2 * Complex.I * (a : ℂ) / (q a b : ℂ)
noncomputable def D (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * ((a-b : ℝ) : ℂ) / (q a b : ℂ)
noncomputable def R (η a b : ℝ) : ℝ := 4 / q a b + 3 * η ^ 2 / 4

theorem coefficient_re (η a b : ℝ) (_hq : q a b ≠ 0) :
    (A η a b).re = η ∧ (B η a b).re = -η / 2 ∧ (D η a b).re = η := by
  simp [A, B, D, Complex.div_re, Complex.normSq_apply]

theorem oscillatory_determinant (η a b : ℝ) (hq : q a b ≠ 0) :
    A η a b * D η a b - (B η a b) ^ 2 = (R η a b : ℂ) := by
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hRcast : (R η a b : ℂ) = 4 / (q a b : ℂ) + 3 * (η : ℂ) ^ 2 / 4 := by
    simp [R]
  rw [hRcast]
  dsimp [A, B, D]
  field_simp [hqc]
  rw [hqexpr]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem real_positive_definite {η a b : ℝ} (hη : 0 < η) (hq : q a b ≠ 0) :
    0 < (A η a b).re * (D η a b).re - (B η a b).re ^ 2 := by
  obtain ⟨hA, hB, hD⟩ := coefficient_re η a b hq
  rw [hA, hB, hD]
  nlinarith [sq_pos_of_pos hη]

end OscSpecial

end

end OAI

end


