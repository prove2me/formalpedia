-- Prove2me | Definitions.Def_RPLib_S3_KHD
-- name    : RPLib_S3_KHD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:38:20.957065+00:00
-- url     : https://prove2.me/theorems/048ea20a-ebd1-4d7b-ab3a-a3c86bbb114b
-- title:
--   Kronecker-Hurwitz class number relation: the root sums
-- statement:
--   The root sums.
--
--   * `rs1` : `∑ᶠ_{Xn n, R = S} kN = Σ_{d ∣ n} T1 (n/d - d)` (`N = (P, P - n/d, d, d)`);
--   * `rs2` : `∑ᶠ_{Yn n, S = 0} wN = Σ_{d ∣ n} T2 d (n/d)` (`N = (P, -n/d, d, 0)`);
--   * **`sumY`** : `∑ᶠ_{Yn n} wN = Σ_{d ∣ n} (T1 (n/d - d) + T2 d (n/d))`, and `T12` evaluates the summand:
--     `n/d` if `d < n/d`, `d/2 + 1/12` if `d = n/d`, `0` otherwise.
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KHC

/-!
# S3-KH, part D: the root sums

* `rs1` : `∑ᶠ_{Xn n, R = S} kN = Σ_{d ∣ n} T1 (n/d - d)` (`N = (P, P - n/d, d, d)`);
* `rs2` : `∑ᶠ_{Yn n, S = 0} wN = Σ_{d ∣ n} T2 d (n/d)` (`N = (P, -n/d, d, 0)`);
* **`sumY`** : `∑ᶠ_{Yn n} wN = Σ_{d ∣ n} (T1 (n/d - d) + T2 d (n/d))`, and `T12` evaluates the summand:
  `n/d` if `d < n/d`, `d/2 + 1/12` if `d = n/d`, `0` otherwise.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

/-- Root term of the `R = S` sum. -/
def T1 (L : ℤ) : ℚ := (if 0 < L then (L : ℚ) else 0) + (if L = 0 then 1 / 6 else 0)

/-- Root term of the `S = 0` sum. -/
def T2 (d c : ℤ) : ℚ := d * hs (c - d) - (if c = d then 1 / 12 else 0)

/-- `(d, P) ↦ (P, P - n/d, d, d)`. -/
def g1 (n : ℤ) (x : ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (x.2, x.2 - n / x.1, x.1, x.1)

/-- `(d, P) ↦ (P, -(n/d), d, 0)`. -/
def g2 (n : ℤ) (x : ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (x.2, -(n / x.1), x.1, 0)

lemma g1_inj (n : ℤ) : Function.Injective (g1 n) := by
  rintro ⟨d, P⟩ ⟨d', P'⟩ h
  simp only [g1, Prod.mk.injEq] at h
  obtain ⟨h1, -, h3, -⟩ := h
  rw [h1, h3]

lemma g2_inj (n : ℤ) : Function.Injective (g2 n) := by
  rintro ⟨d, P⟩ ⟨d', P'⟩ h
  simp only [g2, Prod.mk.injEq] at h
  obtain ⟨h1, -, h3, -⟩ := h
  rw [h1, h3]

theorem rs1 {n : ℕ} (hn : 0 < n) :
    ∑ᶠ N, (Xn n ∩ {N | N.2.2.1 = N.2.2.2}).indicator kN N =
      ∑ d ∈ n.divisors, T1 ((n : ℤ) / d - d) := by
  classical
  rw [fs_red _ (g1 n) (g1_inj n) ?_ ((box (2 * n)).finite_toSet.subset (supp_k n Set.inter_subset_left))]
  · refine Eq.trans ?_ (fs_div hn (fun d : ℤ => T1 ((n : ℤ) / d - d)))
    refine finsum_congr fun d => ?_
    by_cases hc : 0 < d ∧ d ∣ (n : ℤ)
    · rw [if_pos hc, T1, ← sum1 ((n : ℤ) / d - d)]
      refine finsum_congr fun P => ?_
      have hmem : g1 n (d, P) ∈ Xn n ∩ {N | N.2.2.1 = N.2.2.2} :=
        ⟨⟨by simp only [g1, det4]; linarith [Int.ediv_mul_cancel hc.2], hc.1, hc.1⟩, rfl⟩
      rw [Set.indicator_of_mem hmem]
      simp only [g1, kN, kp]
      rw [(by ring : d - (d - P) = P), (by ring : -(P - (n : ℤ) / d) - d = (n : ℤ) / d - d - P)]
    · rw [if_neg hc]
      refine (finsum_congr fun P => ?_).trans finsum_zero
      refine Set.indicator_of_notMem (fun h => hc ⟨h.1.2.1, ?_⟩) _
      have h1 := h.1.1
      simp only [g1, det4] at h1
      exact Dvd.intro_left ((n : ℤ) / d) (by linarith)
  · intro N hN
    rw [Function.mem_support] at hN
    by_cases hX : N ∈ Xn n ∩ {N | N.2.2.1 = N.2.2.2}
    · obtain ⟨P, Q, R, S⟩ := N
      obtain ⟨⟨hd, hR, -⟩, hRS⟩ := hX
      simp only [det4, Set.mem_ofPred_eq] at hd hR hRS
      refine ⟨(R, P), ?_⟩
      have e : (n : ℤ) / R = P - Q := by
        rw [← hd, ← hRS, (by ring : P * R - Q * R = R * (P - Q)), mul_div_cancel_left₀ _ hR.ne']
      show (P, P - (n : ℤ) / R, R, R) = (P, Q, R, S)
      rw [e, hRS, sub_sub_cancel]
    · rw [Set.indicator_of_notMem hX] at hN; exact absurd rfl hN

theorem rs2 {n : ℕ} (hn : 0 < n) :
    ∑ᶠ N, (Yn n ∩ {N | N.2.2.2 = 0}).indicator wN N = ∑ d ∈ n.divisors, T2 d ((n : ℤ) / d) := by
  classical
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  rw [fs_red _ (g2 n) (g2_inj n) ?_ (Y_fin hn' Set.inter_subset_left)]
  · refine Eq.trans ?_ (fs_div hn (fun d : ℤ => T2 d ((n : ℤ) / d)))
    refine finsum_congr fun d => ?_
    by_cases hc : 0 < d ∧ d ∣ (n : ℤ)
    · rw [if_pos hc, T2, ← sum2 d ((n : ℤ) / d) hc.1]
      refine finsum_congr fun P => ?_
      have hmem : g2 n (d, P) ∈ Yn n ∩ {N | N.2.2.2 = 0} :=
        ⟨⟨by simp only [g2, det4]; linarith [Int.ediv_mul_cancel hc.2], hc.1⟩, rfl⟩
      rw [Set.indicator_of_mem hmem]
      simp only [g2, wN, neg_neg]
    · rw [if_neg hc]
      refine (finsum_congr fun P => ?_).trans finsum_zero
      refine Set.indicator_of_notMem (fun h => hc ⟨h.1.2, ?_⟩) _
      have h1 := h.1.1
      simp only [g2, det4] at h1
      exact Dvd.intro_left ((n : ℤ) / d) (by linarith)
  · intro N hN
    rw [Function.mem_support] at hN
    by_cases hX : N ∈ Yn n ∩ {N | N.2.2.2 = 0}
    · obtain ⟨P, Q, R, S⟩ := N
      obtain ⟨⟨hd, hR⟩, hS⟩ := hX
      simp only [det4, Set.mem_ofPred_eq] at hd hR hS
      refine ⟨(R, P), ?_⟩
      have e : (n : ℤ) / R = -Q := by
        rw [← hd, hS, (by ring : P * 0 - Q * R = R * (-Q)), mul_div_cancel_left₀ _ hR.ne']
      show (P, -((n : ℤ) / R), R, 0) = (P, Q, R, S)
      rw [e, neg_neg, hS]
    · rw [Set.indicator_of_notMem hX] at hN; exact absurd rfl hN

/-- **The sum over `Yn n`** as a divisor sum. -/
theorem sumY {n : ℕ} (hn : 0 < n) :
    ∑ᶠ N, (Yn n).indicator wN N = ∑ d ∈ n.divisors, (T1 ((n : ℤ) / d - d) + T2 d ((n : ℤ) / d)) := by
  rw [splitY (by exact_mod_cast hn), tele, rs1 hn, rs2 hn, Finset.sum_add_distrib]

lemma T12 (d e : ℤ) :
    T1 (e - d) + T2 d e = if d < e then (e : ℚ) else if d = e then (d : ℚ) / 2 + 1 / 12 else 0 := by
  simp only [T1, T2]
  rcases lt_trichotomy d e with h | h | h <;>
  simp (disch := omega) only [if_pos, if_neg, hs_pos, hs_zero, hs_neg] <;> (push_cast; ring)

end RamanujanPetersson.S3.KH


