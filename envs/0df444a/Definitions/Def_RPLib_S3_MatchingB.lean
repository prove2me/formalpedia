-- Prove2me | Definitions.Def_RPLib_S3_MatchingB
-- name    : RPLib_S3_MatchingB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:42.53994+00:00
-- url     : https://prove2.me/theorems/87a8185b-3a8d-43fb-8c0d-8d6877a4d22e
-- title:
--   Weight-two Ramanujan-Petersson library: the `U` bound and the Eisenstein term at prime powers
-- statement:
--   The `U` bound and the Eisenstein term at prime powers.
--
--   * `norm_ellRho`: `‖ρ‖ = √n` for the root `ρ` of `X² - tX + n` (`t² ≤ 4n`).
--   * `abs_chebU_le`: `|U_j(t, n)| ≤ (j + 1) √n^j` for `t² ≤ 4n`.
--   * `eisG1_pow`: `eisG1 M k p^m = [k = 2] Σ_{i ≤ m} p^i` (`p ∤ M`).
--   * `eis_diff`: `eisG1 M k p^{m+2} - p^{k-1} eisG1 M k p^m = [k = 2](1 + p^{m+2})`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_Statements
import Definitions.Def_RPLib_S3_EllipticTermC

/-!
# S3-Matching, part B: the `U` bound and the Eisenstein term at prime powers

* `norm_ellRho`: `‖ρ‖ = √n` for the root `ρ` of `X² - tX + n` (`t² ≤ 4n`).
* `abs_chebU_le`: `|U_j(t, n)| ≤ (j + 1) √n^j` for `t² ≤ 4n`.
* `eisG1_pow`: `eisG1 M k p^m = [k = 2] Σ_{i ≤ m} p^i` (`p ∤ M`).
* `eis_diff`: `eisG1 M k p^{m+2} - p^{k-1} eisG1 M k p^m = [k = 2](1 + p^{m+2})`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

open ComplexConjugate

lemma norm_ellRho {t n : ℤ} (h : t ^ 2 ≤ 4 * n) : ‖EllTerm.ellRho t n‖ = Real.sqrt n := by
  have h1 := EllTerm.ellRho_mul h
  rw [Complex.mul_conj] at h1
  have h2 : Complex.normSq (EllTerm.ellRho t n) = (n : ℝ) := by exact_mod_cast h1
  rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, h2]

/-- `|U_j(t, n)| ≤ (j + 1) √n^j` in the Hasse range `t² ≤ 4n`. -/
lemma abs_chebU_le (j : ℕ) {t n : ℤ} (h : t ^ 2 ≤ 4 * n) :
    |(chebU j t n : ℝ)| ≤ (j + 1) * Real.sqrt n ^ j := by
  set ρ := EllTerm.ellRho t n
  have hU : (chebU j t n : ℂ) = SymTrace.U j (ρ + conj ρ) (ρ * conj ρ) := by
    rw [EllTerm.ellRho_add, EllTerm.ellRho_mul h, chebU]
    have h1 := SymTrace.map_U (Int.castRingHom ℂ) j t n
    simp only [eq_intCast] at h1
    exact h1
  rw [SymTrace.U_add_mul] at hU
  have habs : |(chebU j t n : ℝ)| = ‖((chebU j t n : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
  rw [habs, hU]
  calc ‖∑ i ∈ Finset.range (j + 1), ρ ^ i * conj ρ ^ (j - i)‖
      ≤ ∑ i ∈ Finset.range (j + 1), ‖ρ ^ i * conj ρ ^ (j - i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (j + 1), Real.sqrt n ^ j := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_ellRho h, ← pow_add,
          Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    _ = (j + 1) * Real.sqrt n ^ j := by simp

variable {M : ℕ} {p : ℕ}

/-- The Eisenstein term at `n = p^m`, `p ∤ M`. -/
lemma eisG1_pow (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) :
    eisG1 M k (p ^ m) = if k = 2 then ∑ i ∈ Finset.range (m + 1), (p : ℚ) ^ i else 0 := by
  unfold eisG1
  split_ifs with hk
  · have hcop : Nat.Coprime M (p ^ m) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM))
    rw [Finset.filter_true_of_mem fun e he =>
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)) hcop]
    rw [Nat.sum_divisors_prime_pow hp]
    push_cast
    rfl
  · rfl

/-- `σ(p^{m+2}) - p σ(p^m) = 1 + p^{m+2}` at `k = 2`; both sides vanish for `k ≠ 2`. -/
lemma eis_diff (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) :
    eisG1 M k (p ^ (m + 2)) - (p : ℚ) ^ (k - 1) * eisG1 M k (p ^ m) =
      if k = 2 then 1 + (p : ℚ) ^ (m + 2) else 0 := by
  rw [eisG1_pow hp hpM, eisG1_pow hp hpM]
  split_ifs with hk
  · subst hk
    rw [Finset.sum_range_succ' (fun i => (p : ℚ) ^ i) (m + 2),
      Finset.sum_range_succ (fun i => (p : ℚ) ^ (i + 1)) (m + 1), Finset.mul_sum]
    have h1 : ∀ i : ℕ, (p : ℚ) ^ (2 - 1) * (p : ℚ) ^ i = (p : ℚ) ^ (i + 1) := fun i => by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, pow_succ, mul_comm]
    simp only [h1]
    ring
  · ring

end RamanujanPetersson.S3.Match


