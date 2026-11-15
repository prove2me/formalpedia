-- Prove2me | Definitions.Def_RPLib_S3_DWSOEC
-- name    : RPLib_S3_DWSOEC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:36:26.309206+00:00
-- url     : https://prove2.me/theorems/86954551-f09a-4061-b9cb-7a151f52b1e4
-- title:
--   Weight-two Ramanujan-Petersson library: the level-one ordinary mass from Kronecker-Hurwitz
-- statement:
--   The level-one ordinary mass from Kronecker-Hurwitz.
--
--   With `hKH : KroneckerHurwitz` (frozen `Prop` of `Statements.lean`, an explicit hypothesis, owner S3-ES-Wt2):
--   * `khR n = 2σ(n) - Σ_{d ∣ n} min(d, n/d)` and `khR_rec` : `khR(p^(k+2)) - p · khR(p^k) = 2 p^(k+2)`;
--   * `kh_le`, `le_kh` : `khR n ≤ 2 Σ_{|t| ≤ 2n} ellCount_1(t, n) ≤ khR n + 1/6` (`H(0) = -1/12`, at most two `t` with `t² = 4n`);
--   * **`sum_ord_ell1_le`** : `Σ_{p ∤ t, |t| ≤ 2q} ellCount_1(t, q) ≤ q + C` uniformly in `q = p^m` (the p-chain `Ssum1_bdd`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOEB

/-!
# S3-DWS-Ordinary, part EC: the level-one ordinary mass from Kronecker-Hurwitz

With `hKH : KroneckerHurwitz` (frozen `Prop` of `Statements.lean`, an explicit hypothesis, owner S3-ES-Wt2):
* `khR n = 2σ(n) - Σ_{d ∣ n} min(d, n/d)` and `khR_rec` : `khR(p^(k+2)) - p · khR(p^k) = 2 p^(k+2)`;
* `kh_le`, `le_kh` : `khR n ≤ 2 Σ_{|t| ≤ 2n} ellCount_1(t, n) ≤ khR n + 1/6` (`H(0) = -1/12`, at most two `t` with `t² = 4n`);
* **`sum_ord_ell1_le`** : `Σ_{p ∤ t, |t| ≤ 2q} ellCount_1(t, q) ≤ q + C` uniformly in `q = p^m` (the p-chain `Ssum1_bdd`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open RamanujanPetersson.S3.Conj RamanujanPetersson.S3.DWSS

namespace RamanujanPetersson.S3.DWSO

/-- The right-hand side of `KroneckerHurwitz`. -/
noncomputable def khR (n : ℕ) : ℚ :=
  2 * ∑ d ∈ n.divisors, (d : ℚ) - ∑ d ∈ n.divisors, ((min d (n / d) : ℕ) : ℚ)

lemma ell_nonneg (t : ℤ) (n : ℕ) : 0 ≤ ellCount 1 1 t n :=
  Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

section KH

variable {p : ℕ} [Fact p.Prime]

lemma min_pow (k i : ℕ) (hi : i ≤ k) : min (p ^ i) (p ^ k / p ^ i) = p ^ (min i (k - i)) := by
  have hp := (Fact.out : p.Prime)
  rw [Nat.pow_div hi hp.pos]
  rcases le_total i (k - i) with h | h
  · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right hp.pos h)]
  · rw [min_eq_right h, min_eq_right (Nat.pow_le_pow_right hp.pos h)]

lemma khR_pow (k : ℕ) : khR (p ^ k) = 2 * ∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ i -
    ∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ (min i (k - i)) := by
  have hp := (Fact.out : p.Prime)
  unfold khR
  rw [Nat.sum_divisors_prime_pow hp, Nat.sum_divisors_prime_pow hp]
  congr 1
  · simp only [Nat.cast_pow]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [min_pow k i (by rw [Finset.mem_range] at hi; omega), Nat.cast_pow]

lemma khR_rec (k : ℕ) : khR (p ^ (k + 2)) - p * khR (p ^ k) = 2 * (p : ℚ) ^ (k + 2) := by
  rw [khR_pow, khR_pow]
  have h1 : ∑ i ∈ Finset.range (k + 2 + 1), (p : ℚ) ^ i =
      (p : ℚ) * ∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ i + 1 + (p : ℚ) ^ (k + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i ∈ Finset.range (k + 2 + 1), (p : ℚ) ^ (min i (k + 2 - i)) =
      (p : ℚ) * ∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ (min i (k - i)) + 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.mul_sum]
    have e0 : min 0 (k + 2 - 0) = 0 := by omega
    have e1 : min (k + 2) (k + 2 - (k + 2)) = 0 := by omega
    rw [e0, e1, pow_zero]
    have hs : ∑ i ∈ Finset.range (k + 1), (p : ℚ) ^ (min (i + 1) (k + 2 - (i + 1))) =
        ∑ i ∈ Finset.range (k + 1), (p : ℚ) * (p : ℚ) ^ (min i (k - i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      have e : min (i + 1) (k + 2 - (i + 1)) = min i (k - i) + 1 := by omega
      rw [e, pow_succ, mul_comm]
    rw [hs]
    ring
  rw [h1, h2]
  ring

lemma khR_lt_two (m : ℕ) (hm : m < 2) : khR (p ^ m) ≤ 2 * (p : ℚ) ^ m := by
  rw [khR_pow]
  interval_cases m
  · simp
  · simp [Finset.sum_range_succ]
    ring_nf
    rfl

end KH

lemma two_ell_eq (n : ℕ) (t : ℤ) (h : t ^ 2 ≤ 4 * (n : ℤ)) :
    2 * ellCount 1 1 t n =
      hurwitzH (4 * (n : ℤ) - t ^ 2).toNat + (if t ^ 2 = 4 * (n : ℤ) then 1 / 12 else 0) := by
  rcases lt_or_eq_of_le h with h | h
  · rw [level1Ell n t h, if_neg h.ne, add_zero]
  · rw [ellCount_eq_zero_of_le 1 h.ge, if_pos h, h, sub_self]
    simp [hurwitzH]
    norm_num

lemma sum_ell_filter (n : ℕ) (S : Finset ℤ) :
    ∑ t ∈ S, ellCount 1 1 t n = ∑ t ∈ S.filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)), ellCount 1 1 t n := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with h
  · rfl
  · exact ellCount_eq_zero_of_le 1 (le_of_lt (not_le.1 h))

lemma card_sq_le_two (S : Finset ℤ) (c : ℤ) : (S.filter fun t => t ^ 2 = c).card ≤ 2 := by
  rcases (S.filter fun t => t ^ 2 = c).eq_empty_or_nonempty with h | ⟨t₀, ht₀⟩
  · rw [h]; simp
  · have hsub : S.filter (fun t => t ^ 2 = c) ⊆ {t₀, -t₀} := by
      intro t ht
      have h1 := (Finset.mem_filter.1 ht).2
      have h2 := (Finset.mem_filter.1 ht₀).2
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans h2.symm) with h | h <;> simp [h]
    exact ((Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)).trans (by simp)

lemma kh_le (hKH : KroneckerHurwitz) {n : ℕ} (hn : 0 < n) :
    khR n ≤ 2 * ∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n), ellCount 1 1 t n := by
  rw [sum_ell_filter, Finset.mul_sum, khR, ← hKH n hn]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [two_ell_eq n t (Finset.mem_filter.1 ht).2]
  split_ifs <;> norm_num

lemma le_kh (hKH : KroneckerHurwitz) {n : ℕ} (hn : 0 < n) :
    2 * ∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n), ellCount 1 1 t n ≤ khR n + 1 / 6 := by
  rw [sum_ell_filter, Finset.mul_sum, khR, ← hKH n hn,
    Finset.sum_congr rfl fun t ht => two_ell_eq n t (Finset.mem_filter.1 ht).2, Finset.sum_add_distrib]
  rw [add_le_add_iff_left]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hc := card_sq_le_two ((Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ))
    (4 * (n : ℤ))
  have hc' : ((((Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)).filter
      fun t => t ^ 2 = 4 * (n : ℤ)).card : ℚ) ≤ 2 := by exact_mod_cast hc
  linarith

section Main

variable {p : ℕ} [Fact p.Prime]

lemma sum_le_sum_dvd (k : ℕ) :
    (p : ℚ) * ∑ s ∈ Finset.Icc (-(2 * p ^ k : ℤ)) (2 * p ^ k), ellCount 1 1 s (p ^ k) ≤
      ∑ t ∈ (Finset.Icc (-(2 * p ^ (k + 2) : ℤ)) (2 * p ^ (k + 2))).filter (fun t => (p : ℤ) ∣ t),
        (p : ℚ) * ellCount 1 1 (t / p) (p ^ k) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hpk : (0 : ℤ) < p ^ k := pow_pos hp0 k
  rw [Finset.mul_sum]
  have hinj : Set.InjOn (fun s : ℤ => (p : ℤ) * s) (Finset.Icc (-(2 * p ^ k : ℤ)) (2 * p ^ k) : Set ℤ) :=
    fun a _ b _ h => mul_left_cancel₀ hp0.ne' h
  calc ∑ s ∈ Finset.Icc (-(2 * p ^ k : ℤ)) (2 * p ^ k), (p : ℚ) * ellCount 1 1 s (p ^ k)
      = ∑ t ∈ (Finset.Icc (-(2 * p ^ k : ℤ)) (2 * p ^ k)).image (fun s : ℤ => (p : ℤ) * s),
          (p : ℚ) * ellCount 1 1 (t / p) (p ^ k) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Int.mul_ediv_cancel_left _ hp0.ne']
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (ell_nonneg _ _)
        intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
        rw [Finset.mem_Icc] at hs
        rw [Finset.mem_filter, Finset.mem_Icc]
        have e : (p : ℤ) ^ (k + 2) = p * (p * p ^ k) := by ring
        have h1 := mul_le_mul_of_nonneg_left hs.1 hp0.le
        have h2 := mul_le_mul_of_nonneg_left hs.2 hp0.le
        have h3 : (p : ℤ) * (2 * p ^ k) ≤ 2 * p ^ (k + 2) := by
          rw [e]; nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ p - 1) (mul_nonneg hp0.le hpk.le)]
        refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩ <;> linarith

/-- **Level-one ordinary mass.** Under Kronecker-Hurwitz, `Σ_{p ∤ t, |t| ≤ 2q} ellCount_1(t, q) ≤ q + C`. -/
theorem sum_ord_ell1_le (hKH : KroneckerHurwitz) : ∃ C : ℚ, 0 ≤ C ∧ ∀ m : ℕ,
    ∑ t ∈ (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter (fun t => ¬ (p : ℤ) ∣ t),
      ellCount 1 1 t (p ^ m) ≤ (p : ℚ) ^ m + C := by
  obtain ⟨CB, hCB0, hCB⟩ := Ssum1_bdd (p := p)
  refine ⟨1 / 12 + CB, by positivity, fun m => ?_⟩
  have hpos : ∀ j : ℕ, 0 < p ^ j := fun j => pow_pos (Fact.out : p.Prime).pos j
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m))
    (fun t => (p : ℤ) ∣ t) fun t => ellCount 1 1 t (p ^ m)
  have hup := le_kh hKH (hpos m)
  push_cast at hup
  by_cases hm : m < 2
  · have hdv : 0 ≤ ∑ t ∈ (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter (fun t => (p : ℤ) ∣ t),
        ellCount 1 1 t (p ^ m) :=
      Finset.sum_nonneg fun t _ => ell_nonneg _ _
    have := khR_lt_two (p := p) m hm
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hlow := kh_le hKH (hpos k)
  push_cast at hlow
  have hre := sum_le_sum_dvd (p := p) k
  have hrec := khR_rec (p := p) k
  have e1 : (1 : ZMod 1) * (p : ZMod 1)⁻¹ = 1 := Subsingleton.elim _ _
  have hEf : ∀ t : ℤ, (p : ℚ) * ellCount 1 1 (t / p) (p ^ k) - |Ef 1 p 1 t (k + 2)| ≤
      ellCount 1 1 t (p ^ (k + 2)) := by
    intro t
    have hd : Ef 1 p 1 t (k + 2) = ellCount 1 1 t (p ^ (k + 2)) - p * ellCount 1 1 (t / p) (p ^ k) := by
      simp only [Ef, if_pos (by omega : 2 ≤ k + 2), e1, Nat.add_sub_cancel]
    have h := neg_abs_le (Ef 1 p 1 t (k + 2))
    linarith
  have hsum : ∑ t ∈ (Finset.Icc (-(2 * p ^ (k + 2) : ℤ)) (2 * p ^ (k + 2))).filter (fun t => (p : ℤ) ∣ t),
      ((p : ℚ) * ellCount 1 1 (t / p) (p ^ k) - |Ef 1 p 1 t (k + 2)|) ≤
      ∑ t ∈ (Finset.Icc (-(2 * p ^ (k + 2) : ℤ)) (2 * p ^ (k + 2))).filter (fun t => (p : ℤ) ∣ t),
        ellCount 1 1 t (p ^ (k + 2)) :=
    Finset.sum_le_sum fun t _ => hEf t
  rw [Finset.sum_sub_distrib] at hsum
  have hSs : ∑ t ∈ (Finset.Icc (-(2 * p ^ (k + 2) : ℤ)) (2 * p ^ (k + 2))).filter (fun t => (p : ℤ) ∣ t),
      |Ef 1 p 1 t (k + 2)| = Ssum 1 p 1 (k + 2) := rfl
  have hC := hCB (k + 2)
  have hp0 : (0 : ℚ) ≤ p := Nat.cast_nonneg _
  have hlowp := mul_le_mul_of_nonneg_left hlow hp0
  linarith

end Main

end RamanujanPetersson.S3.DWSO


