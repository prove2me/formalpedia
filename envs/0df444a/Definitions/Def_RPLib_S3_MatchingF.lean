-- Prove2me | Definitions.Def_RPLib_S3_MatchingF
-- name    : RPLib_S3_MatchingF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:36:58.177066+00:00
-- url     : https://prove2.me/theorems/637ee667-b8d2-4ca9-a9c1-3d4bd7fcc9a3
-- title:
--   Weight-two Ramanujan-Petersson library: `U`-sums over the Hasse range, and the pairs with `j ∈ {0, 1728}`
-- statement:
--   `U`-sums over the Hasse range, and the pairs with `j ∈ {0, 1728}`.
--
--   * `sqrt_pow_eq`, `sqrt_natCast_pow`: `√(p^m)^j = √p^(j m)`.
--   * `abs_sum_chebU_le`: `|Σ_t f(t) U_j(t, q)| ≤ (j+1) √q^j Σ_t |f t|` when `f` vanishes for `t² > 4q`.
--   * `pairCount_eq_zero`: no pairs with `t² > 4q` (Hasse).
--   * `pcBad`, `pairCount_eq_add`, `sum_pcBad_le` (`≤ 2M²`, `jFibre`), `abs_pairSumU_sub_j_le`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingB
import Definitions.Def_RPLib_S3_DWSSupersingular
import Definitions.Def_RPLib_S2_HasseA

/-!
# S3-Matching, part F: `U`-sums over the Hasse range, and the pairs with `j ∈ {0, 1728}`

* `sqrt_pow_eq`, `sqrt_natCast_pow`: `√(p^m)^j = √p^(j m)`.
* `abs_sum_chebU_le`: `|Σ_t f(t) U_j(t, q)| ≤ (j+1) √q^j Σ_t |f t|` when `f` vanishes for `t² > 4q`.
* `pairCount_eq_zero`: no pairs with `t² > 4q` (Hasse).
* `pcBad`, `pairCount_eq_add`, `sum_pcBad_le` (`≤ 2M²`, `jFibre`), `abs_pairSumU_sub_j_le`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

open RPLib RPLib.TateNF

lemma sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : Real.sqrt (x ^ m) = Real.sqrt x ^ m := by
  rw [Real.sqrt_eq_iff_mul_self_eq (pow_nonneg hx m) (pow_nonneg (Real.sqrt_nonneg x) m), ← mul_pow,
    Real.mul_self_sqrt hx]

lemma sqrt_natCast_pow (p m j : ℕ) : Real.sqrt ((p ^ m : ℕ) : ℝ) ^ j = Real.sqrt p ^ (j * m) := by
  rw [Nat.cast_pow, sqrt_pow_eq _ (Nat.cast_nonneg p), ← pow_mul, mul_comm]

/-- **`U`-sums in the Hasse range.** -/
lemma abs_sum_chebU_le (j q : ℕ) (s : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ t ∈ s, 4 * (q : ℤ) < t ^ 2 → f t = 0) :
    |∑ t ∈ s, f t * (chebU j t q : ℝ)| ≤ (j + 1) * Real.sqrt q ^ j * ∑ t ∈ s, |f t| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht => ?_)
  rw [abs_mul, mul_comm |f t|]
  by_cases h : 4 * (q : ℤ) < t ^ 2
  · rw [hf t ht h, abs_zero, mul_zero, mul_zero]
  · have := abs_chebU_le j (t := t) (n := (q : ℤ)) (not_lt.1 h)
    rw [Int.cast_natCast] at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
lemma trace_tate_sq_le {b c : F} (hD : tateDisc b c ≠ 0) :
    EllFq.trace (tate b c) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  have : (tate b c).IsElliptic := DWSS.isElliptic_tate hD
  have h := RPLib.Hasse.trace_sq_le_four_mul (tate b c)
  rw [EllFq.trace_eq]
  exact h

/-- **Hasse**: no pairs with `t² > 4q`. -/
lemma pairCount_eq_zero (M : ℕ) {t : ℤ} (h : 4 * (Fintype.card F : ℤ) < t ^ 2) : pairCount F M t = 0 := by
  unfold pairCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨bc, hY, ht⟩
  have := trace_tate_sq_le hY.1
  rw [ht] at this
  linarith

/-- Pairs with trace `t` and `j ∈ {0, 1728}` (`c₄ = 0` or `c₆ = 0`). -/
noncomputable def pcBad (F : Type) [Field F] [DecidableEq F] (M : ℕ) (t : ℤ) : ℕ :=
  Nat.card {bc : F × F // bc ∈ Y1 F M ∧ EllFq.trace (tate bc.1 bc.2) = t ∧
    ((tate bc.1 bc.2).c₄ = 0 ∨ (tate bc.1 bc.2).c₆ = 0)}

lemma pairCount_eq_add (M : ℕ) (t : ℤ) :
    pairCount F M t = Nat.card {bc : F × F // bc ∈ Y1 F M ∧ EllFq.trace (tate bc.1 bc.2) = t ∧
      (tate bc.1 bc.2).c₄ ≠ 0 ∧ (tate bc.1 bc.2).c₆ ≠ 0} + pcBad F M t := by
  classical
  unfold pairCount pcBad
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun bc : F × F =>
    bc ∈ Y1 F M ∧ EllFq.trace (tate bc.1 bc.2) = t)
    (fun bc : F × F => (tate bc.1 bc.2).c₄ ≠ 0 ∧ (tate bc.1 bc.2).c₆ ≠ 0), Finset.filter_filter,
    Finset.filter_filter]
  congr 2
  · ext bc; simp only [and_assoc]
  · ext bc; simp only [ne_eq, not_and_or, not_not, and_assoc]

lemma sum_pcBad_le (M : ℕ) (hM : 4 ≤ M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
    (hq : Fintype.card F = p ^ m) (T : Finset ℤ) : ∑ t ∈ T, pcBad F M t ≤ 2 * M ^ 2 := by
  classical
  have hJ := jFibre M hM p hpM m F hq
  set A := Finset.univ.filter
    (fun bc : F × F => bc ∈ Y1 F M ∧ ((tate bc.1 bc.2).c₄ = 0 ∨ (tate bc.1 bc.2).c₆ = 0)) with hAdef
  have hA : A.card ≤ 2 * M ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hJ
    convert hJ using 2
  have hfib : ∀ t, pcBad F M t = (A.filter (fun bc => EllFq.trace (tate bc.1 bc.2) = t)).card := by
    intro t
    unfold pcBad
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hAdef, Finset.filter_filter]
    congr 1
    ext bc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp only [hfib]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans hA

lemma pairSumU_sub_j (M k q : ℕ) :
    pairSumU F M k q - pairSumU_j F M k q =
      ∑ t ∈ Finset.Icc (-(2 * q : ℤ)) (2 * q), (pcBad F M t : ℤ) * chebU (k - 2) t q := by
  unfold pairSumU pairSumU_j
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pairCount_eq_add M t]; push_cast; ring

/-- `|Σ U (pairs) - Σ U (pairs, j ∉ {0, 1728})| ≤ (k-1) √q^{k-2} 2M²`. -/
lemma abs_pairSumU_sub_j_le (M : ℕ) (hM : 4 ≤ M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m k : ℕ)
    (hq : Fintype.card F = p ^ m) :
    |((pairSumU F M k (p ^ m) - pairSumU_j F M k (p ^ m) : ℤ) : ℝ)| ≤
      ((k - 2 : ℕ) + 1) * Real.sqrt p ^ ((k - 2) * m) * (2 * M ^ 2) := by
  rw [pairSumU_sub_j, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_natCast]
  have h := abs_sum_chebU_le (k - 2) (p ^ m) (Finset.Icc (-(2 * (p ^ m : ℕ) : ℤ)) (2 * (p ^ m : ℕ)))
    (fun t => (pcBad F M t : ℝ)) (fun t _ ht => by
      have h0 : pairCount F M t = 0 := pairCount_eq_zero M (by rw [hq]; exact_mod_cast ht)
      have h1 := pairCount_eq_add (F := F) M t
      have : pcBad F M t = 0 := by omega
      rw [this, Nat.cast_zero])
  rw [sqrt_natCast_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simp only [Nat.abs_cast]
  exact_mod_cast sum_pcBad_le M hM p hpM m hq _

end RamanujanPetersson.S3.Match


