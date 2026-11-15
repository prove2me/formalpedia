-- Prove2me | Definitions.Def_RPLib_S3_MatchingH
-- name    : RPLib_S3_MatchingH
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:39:01.666375+00:00
-- url     : https://prove2.me/theorems/38dbab1d-6272-4f23-a6e8-c033171dbd94
-- title:
--   Weight-two Ramanujan-Petersson library: bound helpers for identity (I')
-- statement:
--   Bound helpers for identity (I').
--
--   `abs5q` (five-piece triangle inequality through the `ℚ → ℝ` cast), `piece_sum` (a `U`-weighted sum over the Hasse
--   range), `abs_scalD_le` (scalar piece), `abs_hypD_le` (hyperbolic piece).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingC
import Definitions.Def_RPLib_S3_MatchingD
import Definitions.Def_RPLib_S3_MatchingF

/-!
# S3-Matching, part H: bound helpers for identity (I')

`abs5q` (five-piece triangle inequality through the `ℚ → ℝ` cast), `piece_sum` (a `U`-weighted sum over the Hasse
range), `abs_scalD_le` (scalar piece), `abs_hypD_le` (hyperbolic piece).
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

lemma abs5q {a b c d e : ℚ} {X1 X2 X3 X4 X5 : ℝ} (h1 : |(a : ℝ)| ≤ X1) (h2 : |(b : ℝ)| ≤ X2)
    (h3 : |(c : ℝ)| ≤ X3) (h4 : |(d : ℝ)| ≤ X4) (h5 : |(e : ℝ)| ≤ X5) :
    |((a + b - c - d + e : ℚ) : ℝ)| ≤ X1 + X2 + X3 + X4 + X5 := by
  push_cast
  have e1 := abs_add_le ((a : ℝ) + b - c - d) e
  have e2 := abs_sub ((a : ℝ) + b - c) d
  have e3 := abs_sub ((a : ℝ) + b) c
  have e4 := abs_add_le (a : ℝ) b
  linarith

lemma piece_sum (p m j : ℕ) (s : Finset ℤ) (g : ℤ → ℚ) (hg : ∀ t ∈ s, 4 * ((p ^ m : ℕ) : ℤ) < t ^ 2 → g t = 0)
    {X : ℝ} (hX : ∑ t ∈ s, |(g t : ℝ)| ≤ X) :
    |((∑ t ∈ s, (chebU j t (p ^ m : ℕ) : ℚ) * g t : ℚ) : ℝ)| ≤ (j + 1) * Real.sqrt p ^ (j * m) * X := by
  rw [Rat.cast_sum]
  simp only [Rat.cast_mul, Rat.cast_intCast]
  have h := abs_sum_chebU_le j (p ^ m) s (fun t => (g t : ℝ)) (fun t ht h => by rw [hg t ht h, Rat.cast_zero])
  rw [Finset.sum_congr rfl fun t _ => mul_comm ((chebU j t (p ^ m : ℕ) : ℤ) : ℝ) (g t : ℝ), ← sqrt_natCast_pow]
  exact h.trans (mul_le_mul_of_nonneg_left hX (by positivity))

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
lemma abs_scalD_le {p : ℕ} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    |((scalarG1 M k (p ^ m) 1 -
        (if 2 ≤ m then (p : ℚ) ^ (k - 1) * scalarG1 M k (p ^ (m - 2)) (p : ZMod M) else 0) : ℚ) : ℝ)| ≤
      ((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * (1 + p) * Real.sqrt p ^ ((k - 2) * m) := by
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hψ : (0 : ℝ) ≤ (dedekindPsi M : ℝ) := by exact_mod_cast dedekindPsi_nonneg M
  have hK : 0 ≤ ((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) := by positivity
  have hS : 0 ≤ Real.sqrt p ^ ((k - 2) * m) := by positivity
  have h1 := abs_scalarG1_le M k (p ^ m) (by omega) 1
  rw [sqrt_natCast_pow] at h1
  split_ifs with h2
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    have h3 := abs_scalarG1_le M k (p ^ m') (by omega) (p : ZMod M)
    rw [sqrt_natCast_pow] at h3
    have hpow : (p : ℝ) ^ (k - 1) * Real.sqrt p ^ ((k - 2) * m') = p * Real.sqrt p ^ ((k - 2) * (m' + 2)) := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
      rw [show k' + 2 - 1 = k' + 1 by omega, show k' + 2 - 2 = k' by omega,
        show k' * (m' + 2) = k' * m' + 2 * k' by ring, pow_add (Real.sqrt p) (k' * m'),
        pow_mul (Real.sqrt p) 2 k', hs]
      ring
    rw [Nat.add_sub_cancel]
    push_cast
    have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ (k - 1) := by positivity
    calc |(scalarG1 M k (p ^ (m' + 2)) 1 : ℝ) - (p : ℝ) ^ (k - 1) * (scalarG1 M k (p ^ m') (p : ZMod M) : ℝ)|
        ≤ |(scalarG1 M k (p ^ (m' + 2)) 1 : ℝ)| + (p : ℝ) ^ (k - 1) * |(scalarG1 M k (p ^ m') (p : ZMod M) : ℝ)| := by
          refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_of_nonneg hp0]
      _ ≤ ((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * Real.sqrt p ^ ((k - 2) * (m' + 2)) +
          (p : ℝ) ^ (k - 1) * (((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * Real.sqrt p ^ ((k - 2) * m')) := by
          gcongr
      _ = _ := by rw [mul_left_comm, hpow]; ring
  · rw [sub_zero]
    refine h1.trans ?_
    have : (1 : ℝ) ≤ 1 + p := by have := Nat.cast_nonneg (α := ℝ) p; linarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hK hS)]

lemma abs_hypD_le {p : ℕ} (hM : 1 < M) (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) (hm : 1 ≤ m) :
    |hypG1 M k (p ^ m) 1 - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * hypG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)| ≤
      hypB M := by
  split_ifs with h2
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    rw [Nat.add_sub_cancel]; exact abs_hyp_diff_le hM hp hpM k m'
  · obtain rfl : m = 1 := by omega
    rw [sub_zero]; exact abs_hypG1_prime_le hp k 1

end RamanujanPetersson.S3.Match


