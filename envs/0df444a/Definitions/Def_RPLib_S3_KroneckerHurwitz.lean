-- Prove2me | Definitions.Def_RPLib_S3_KroneckerHurwitz
-- name    : RPLib_S3_KroneckerHurwitz
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:41:40.586204+00:00
-- url     : https://prove2.me/theorems/32400c9b-2518-4b45-a794-a0cbf4497f6c
-- title:
--   The Kronecker-Hurwitz class number relation (elementary proof)
-- statement:
--   The Kronecker-Hurwitz class number relation.
--
--   `Σ_{t² ≤ 4n} H(4n - t²) = 2σ(n) - Σ_{d ∣ n} min(d, n/d)` for every `n ≥ 1` (`KroneckerHurwitz`, Statements.lean).
--
--   Proof (Popa-Zagier's tessellation argument, reformulated as a telescoping identity, files KH_A..KH_F):
--   `tsum_eq` + `bridge` turn the left side into `2 ∑ᶠ_{det N = n, R > 0} w(N) - (1/12) #{t : t² = 4n}`;
--   `sumY` + `T12` evaluate the matrix sum as `Σ_{d ∣ n} U(d)`; this file finishes with two elementary lemmas:
--   * `sq_count` : `#{t : t² = 4n} = 2 Σ_{d ∣ n} [d = n/d]`;
--   * `div_id` : `2 Σ_d U(d) - (1/6) Σ_d [d = n/d] = 2σ(n) - Σ_d min(d, n/d)` (involution `d ↦ n/d`).
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KHF

/-!
# S3-KH: the Kronecker-Hurwitz class number relation

`Σ_{t² ≤ 4n} H(4n - t²) = 2σ(n) - Σ_{d ∣ n} min(d, n/d)` for every `n ≥ 1` (`KroneckerHurwitz`, Statements.lean).

Proof (Popa-Zagier's tessellation argument, reformulated as a telescoping identity, files KH_A..KH_F):
`tsum_eq` + `bridge` turn the left side into `2 ∑ᶠ_{det N = n, R > 0} w(N) - (1/12) #{t : t² = 4n}`;
`sumY` + `T12` evaluate the matrix sum as `Σ_{d ∣ n} U(d)`; this file finishes with two elementary lemmas:
* `sq_count` : `#{t : t² = 4n} = 2 Σ_{d ∣ n} [d = n/d]`;
* `div_id` : `2 Σ_d U(d) - (1/6) Σ_d [d = n/d] = 2σ(n) - Σ_d min(d, n/d)` (involution `d ↦ n/d`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

open RamanujanPetersson.S3

/-- The value of one divisor term of `sumY`. -/
noncomputable def U (n d : ℕ) : ℚ :=
  if d < n / d then ((n / d : ℕ) : ℚ) else if d = n / d then (d : ℚ) / 2 + 1 / 12 else 0

lemma hT (n d : ℕ) : T1 ((n : ℤ) / d - d) + T2 d ((n : ℤ) / d) = U n d := by
  rw [T12, ← Int.natCast_div]
  simp only [U, Nat.cast_lt, Nat.cast_inj, Int.cast_natCast]

/-- The square terms. -/
lemma sq_count {n : ℕ} (hn : 0 < n) :
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
        (if t ^ 2 = 4 * (n : ℤ) then (1 : ℚ) else 0) =
      2 * ∑ d ∈ n.divisors, (if d = n / d then (1 : ℚ) else 0) := by
  classical
  by_cases hsq : ∃ m : ℕ, m * m = n
  · obtain ⟨m, rfl⟩ := hsq
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    rw [Finset.sum_eq_single m]
    · rw [if_pos (Nat.mul_div_cancel m hm).symm, Finset.sum_boole]
      have hset : ((Finset.Icc (-(2 * ((m * m : ℕ) : ℤ))) (2 * ((m * m : ℕ) : ℤ))).filter
          (fun t : ℤ => t ^ 2 ≤ 4 * ((m * m : ℕ) : ℤ))).filter (fun t : ℤ => t ^ 2 = 4 * ((m * m : ℕ) : ℤ)) =
          {2 * (m : ℤ), -(2 * (m : ℤ))} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        push_cast
        constructor
        · rintro ⟨-, h⟩
          have h0 : (t - 2 * m) * (t + 2 * m) = 0 := by linear_combination h
          rcases mul_eq_zero.1 h0 with h1 | h1
          · left; linarith
          · right; linarith
        · rintro (rfl | rfl) <;> refine ⟨⟨⟨by nlinarith, by nlinarith⟩, by nlinarith⟩, by ring⟩
      rw [hset, Finset.card_pair (by omega)]
      norm_num
    · intro d hd hne
      rw [if_neg]
      intro h
      apply hne
      have hdvd := Nat.dvd_of_mem_divisors hd
      have h2 : d * d = m * m := by
        conv_lhs => rhs; rw [h]
        exact Nat.mul_div_cancel' hdvd
      exact Nat.mul_self_inj.1 h2
    · intro h
      exact absurd (Nat.mem_divisors.2 ⟨dvd_mul_right m m, hn.ne'⟩) h
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · norm_num
    · intro d hd
      rw [if_neg]
      intro h
      apply hsq
      refine ⟨d, ?_⟩
      conv_lhs => rhs; rw [h]
      exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    · intro t _
      rw [if_neg]
      intro h
      have hev : Even (t ^ 2) := ⟨2 * n, by rw [h]; ring⟩
      obtain ⟨s, rfl⟩ := (Int.even_pow.1 hev).1
      apply hsq
      have hs : s * s = (n : ℤ) := by linarith [h, show (s + s) ^ 2 = 4 * (s * s) by ring]
      refine ⟨s.natAbs, ?_⟩
      have := Int.natAbs_mul_self (a := s)
      exact_mod_cast this.trans hs

/-- The divisor identity. -/
lemma div_id {n : ℕ} (hn : 0 < n) :
    2 * ∑ d ∈ n.divisors, U n d - 1 / 12 * (2 * ∑ d ∈ n.divisors, (if d = n / d then (1 : ℚ) else 0)) =
      2 * ∑ d ∈ n.divisors, (d : ℚ) - ∑ d ∈ n.divisors, ((min d (n / d) : ℕ) : ℚ) := by
  classical
  set f : ℕ → ℚ := fun d => if d < n / d then ((n / d : ℕ) : ℚ) else 0 with hf
  set g : ℕ → ℚ := fun d => if n / d < d then (d : ℚ) else 0 with hg
  set J : ℕ → ℚ := fun d => if d = n / d then (d : ℚ) else 0 with hJ
  have hfg : ∑ d ∈ n.divisors, f d = ∑ d ∈ n.divisors, g d := by
    rw [← Nat.sum_div_divisors n g]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdn : n / (n / d) = d := Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn.ne'
    simp only [hf, hg, hdn]
  have he : ∑ d ∈ n.divisors, ((n / d : ℕ) : ℚ) = ∑ d ∈ n.divisors, (d : ℚ) :=
    Nat.sum_div_divisors n (fun d => (d : ℚ))
  have p1 : ∀ d ∈ n.divisors,
      2 * U n d - 1 / 6 * (if d = n / d then (1 : ℚ) else 0) = 2 * f d + J d := by
    intro d _
    simp only [U, hf, hJ]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have p2 : ∀ d ∈ n.divisors,
      f d + g d + J d = (d : ℚ) + ((n / d : ℕ) : ℚ) - ((min d (n / d) : ℕ) : ℚ) := by
    intro d _
    simp only [hf, hg, hJ, min_def]
    generalize n / d = e
    split_ifs <;> first | ring1 | (exfalso; omega) | (subst_vars; ring1)
  have s1 := Finset.sum_congr rfl p1
  have s2 := Finset.sum_congr rfl p2
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at s1 s2
  linarith [s1, s2, hfg, he]

/-- **Kronecker-Hurwitz class number relation.** -/
theorem kroneckerHurwitz : KroneckerHurwitz := by
  intro n hn
  rw [tsum_eq hn, ← bridge hn, sumY hn, sq_count hn, Finset.sum_congr rfl (fun d _ => hT n d)]
  exact div_id hn

end RamanujanPetersson.S3.KH


