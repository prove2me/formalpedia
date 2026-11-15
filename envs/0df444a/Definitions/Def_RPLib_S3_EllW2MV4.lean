-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV4
-- name    : RPLib_S3_EllW2MV4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:27:07.875409+00:00
-- url     : https://prove2.me/theorems/68b3d59e-d482-49f3-86a4-41d5f510507c
-- title:
--   The Eichler-Selberg trace formula in weight two: `φ(k)/k = (φ(e)/e) · Σ_{j ∣ k} [j ⊥ m] μ(j)/j`, `e = gcd(k, m)`
-- statement:
--   `φ(k)/k = (φ(e)/e) · Σ_{j ∣ k} [j ⊥ m] μ(j)/j`, `e = gcd(k, m)`.
--
--   * `phiR`, `gcdR m`, `muR m`: the arithmetic functions `k ↦ φ(k)/k`, `k ↦ φ(gcd(k,m))/gcd(k,m)`,
--     `j ↦ [j ⊥ m] μ(j)/j` over `ℝ`; all multiplicative.
--   * `phiR_eq`: `phiR = (gcdR m).pmul (muR m * ζ)` (`eq_iff_eq_on_prime_powers`).
--   * **`phi_div_eq`** (`k ≠ 0`): `φ(k)/k = φ(gcd(k,m))/gcd(k,m) · Σ_{j ∈ k.divisors} [j ⊥ m] μ(j)/j`.
--   * `abs_muR_le`: `|[j ⊥ m] μ(j)/j| ≤ 1/j`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib

/-!
# S3-ES-Wt2 (O6, file MV4): `φ(k)/k = (φ(e)/e) · Σ_{j ∣ k} [j ⊥ m] μ(j)/j`, `e = gcd(k, m)`

* `phiR`, `gcdR m`, `muR m`: the arithmetic functions `k ↦ φ(k)/k`, `k ↦ φ(gcd(k,m))/gcd(k,m)`,
  `j ↦ [j ⊥ m] μ(j)/j` over `ℝ`; all multiplicative.
* `phiR_eq`: `phiR = (gcdR m).pmul (muR m * ζ)` (`eq_iff_eq_on_prime_powers`).
* **`phi_div_eq`** (`k ≠ 0`): `φ(k)/k = φ(gcd(k,m))/gcd(k,m) · Σ_{j ∈ k.divisors} [j ⊥ m] μ(j)/j`.
* `abs_muR_le`: `|[j ⊥ m] μ(j)/j| ≤ 1/j`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- `k ↦ φ(k)/k`. -/
def phiR : ArithmeticFunction ℝ := ⟨fun k => (k.totient : ℝ) / k, by simp⟩

/-- `k ↦ φ(gcd(k,m))/gcd(k,m)` (`0` at `0`). -/
def gcdR (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k = 0 then 0 else ((k.gcd m).totient : ℝ) / (k.gcd m), by simp⟩

/-- `j ↦ [j ⊥ m] μ(j)/j`. -/
def muR (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun j => if j.Coprime m then (μ j : ℝ) / j else 0, by simp⟩

lemma phiR_apply (k : ℕ) : phiR k = (k.totient : ℝ) / k := rfl

lemma gcdR_apply (m k : ℕ) :
    gcdR m k = if k = 0 then 0 else ((k.gcd m).totient : ℝ) / (k.gcd m) := rfl

lemma muR_apply (m j : ℕ) : muR m j = if j.Coprime m then (μ j : ℝ) / j else 0 := rfl

lemma totient_div_mul {a b : ℕ} (h : a.Coprime b) :
    (((a * b).totient : ℕ) : ℝ) / ((a * b : ℕ) : ℝ) =
      ((a.totient : ℝ) / a) * ((b.totient : ℝ) / b) := by
  rw [Nat.totient_mul h]; push_cast; rw [div_mul_div_comm]

lemma isMultiplicative_phiR : phiR.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [phiR_apply], fun {a b} _ _ h => ?_⟩
  rw [phiR_apply, phiR_apply, phiR_apply]; exact totient_div_mul h

lemma isMultiplicative_gcdR (m : ℕ) : (gcdR m).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [gcdR_apply], fun {a b} ha hb h => ?_⟩
  rw [gcdR_apply, gcdR_apply, gcdR_apply, if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb]
  have hg : (a * b).gcd m = a.gcd m * b.gcd m := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul m h, Nat.gcd_comm m a, Nat.gcd_comm m b]
  have hc : (a.gcd m).Coprime (b.gcd m) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a m)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left b m) h)
  rw [hg]; exact totient_div_mul hc

lemma isMultiplicative_muR (m : ℕ) : (muR m).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [muR_apply], fun {a b} _ _ h => ?_⟩
  rw [muR_apply, muR_apply, muR_apply]
  have hmu : ((μ (a * b) : ℤ) : ℝ) = (μ a : ℝ) * μ b := by
    rw [isMultiplicative_moebius.map_mul_of_coprime h, Int.cast_mul]
  by_cases ha : a.Coprime m <;> by_cases hb : b.Coprime m
  · rw [if_pos (Nat.Coprime.mul ha hb), if_pos ha, if_pos hb, hmu, Nat.cast_mul,
      div_mul_div_comm]
  · rw [if_neg (fun hab => hb (Nat.Coprime.coprime_mul_left hab)), if_neg hb, mul_zero]
  · rw [if_neg (fun hab => ha (Nat.Coprime.coprime_mul_right hab)), if_neg ha, zero_mul]
  · rw [if_neg (fun hab => ha (Nat.Coprime.coprime_mul_right hab)), if_neg ha, zero_mul]

lemma isMultiplicative_GR (m : ℕ) : (muR m * (ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
  (isMultiplicative_muR m).mul isMultiplicative_zeta.natCast

lemma phi_div_prime_pow {p : ℕ} (hp : p.Prime) (b : ℕ) :
    ((p ^ (b + 1)).totient : ℝ) / ((p ^ (b + 1) : ℕ) : ℝ) = 1 - 1 / p := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [Nat.totient_prime_pow_succ hp]
  push_cast [Nat.cast_sub hp.one_le]
  field_simp
  ring

lemma muR_prime_pow_add_two (m : ℕ) {p : ℕ} (hp : p.Prime) (t : ℕ) :
    muR m (p ^ (t + 1 + 1)) = 0 := by
  rw [muR_apply, moebius_apply_prime_pow hp (by omega), if_neg (show ¬ (t + 1 + 1 = 1) by omega)]
  simp

lemma GR_prime_pow (m : ℕ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (muR m * (ζ : ArithmeticFunction ℝ)) (p ^ (i + 1)) = 1 + muR m p := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ',
    Finset.sum_range_succ', Finset.sum_eq_zero (fun t _ => muR_prime_pow_add_two m hp t)]
  simp only [zero_add, pow_zero, pow_one]
  rw [(isMultiplicative_muR m).map_one]
  ring

theorem phiR_eq (m : ℕ) : phiR = (gcdR m).pmul (muR m * (ζ : ArithmeticFunction ℝ)) := by
  have hmul := (isMultiplicative_gcdR m).pmul (isMultiplicative_GR m)
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ isMultiplicative_phiR _ hmul).2
    fun p i hp => ?_
  rcases i with _ | i
  · rw [pow_zero, isMultiplicative_phiR.map_one, hmul.map_one]
  rw [pmul_apply, GR_prime_pow m hp i, phiR_apply, phi_div_prime_pow hp i, gcdR_apply,
    if_neg (pow_ne_zero _ hp.ne_zero), muR_apply]
  by_cases hpm : p ∣ m
  · have hnc : ¬ p.Coprime m := fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 h hpm
    rw [if_neg hnc, add_zero, mul_one]
    obtain ⟨b, -, hbe⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (p ^ (i + 1)) m)
    have hb0 : b ≠ 0 := by
      rintro rfl
      have hd : p ∣ (p ^ (i + 1)).gcd m := Nat.dvd_gcd (dvd_pow_self p (Nat.succ_ne_zero i)) hpm
      rw [hbe, pow_zero] at hd
      exact hp.one_lt.ne' (Nat.dvd_one.1 hd)
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [hbe, phi_div_prime_pow hp b']
  · have hc : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    rw [if_pos hc, (Nat.Coprime.pow_left (i + 1) hc).gcd_eq_one, moebius_apply_prime hp,
      Nat.totient_one]
    push_cast
    ring

/-- **MV4**: `φ(k)/k = φ(gcd(k,m))/gcd(k,m) · Σ_{j ∣ k} [j ⊥ m] μ(j)/j` for `k ≠ 0`. -/
theorem phi_div_eq (m : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (k.totient : ℝ) / k = ((k.gcd m).totient : ℝ) / (k.gcd m) *
      ∑ j ∈ k.divisors, (if j.Coprime m then (μ j : ℝ) / j else 0) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f k) (phiR_eq m)
  simp only [phiR_apply, pmul_apply, coe_mul_zeta_apply, gcdR_apply, if_neg hk, muR_apply] at h
  exact h

lemma abs_muR_le (m j : ℕ) : |(if j.Coprime m then (μ j : ℝ) / j else 0)| ≤ 1 / j := by
  split_ifs
  · rw [abs_div, Nat.abs_cast]
    gcongr
    exact_mod_cast abs_moebius_le_one
  · rw [abs_zero]; positivity

end RamanujanPetersson.EllW2


