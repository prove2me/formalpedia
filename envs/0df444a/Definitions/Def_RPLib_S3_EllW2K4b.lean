-- Prove2me | Definitions.Def_RPLib_S3_EllW2K4b
-- name    : RPLib_S3_EllW2K4b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:02:02.602293+00:00
-- url     : https://prove2.me/theorems/dab1392d-4ae7-4ad0-987a-0029b7904d82
-- title:
--   The Eichler-Selberg trace formula in weight two: the per-`c` discrepancy bound in Euler-product form
-- statement:
--   The per-`c` discrepancy bound in Euler-product form.
--
--   * `fp_mul_fp`, `cast_rpow_eq_fp` (`n^s = Π_{p^e ∥ n} (p^e)^s`), `card_divisors_eq_fp` (`τ(n) = Π (e+1)`),
--     `fp_sPart`, `fp_rPart` (products over the smooth / rough prime factors).
--   * `small_eq`, `large_le`: the local inequalities; `sPart_rpow`, `rPart_le`: their products.
--   * `N0f M n = n⁺ + M + 16`, `Af`, `Bf` (smooth / rough parts of `|c|` at `N0f`), `Bc` (the K3 bound).
--   * **`norm_sum_WcF_sub_le_Bc`**: `‖Σ_{u<m} (WcF c u - μ_c)‖ ≤ Bc M n c` (for `0 < n`, `c ≠ 0`).
--   * **`Bc_le`**: `Bc M n c ≤ 33 · L · M^(33/32) · |c|² · fp (fW (N0f M n)) |c|`;
--     **`norm_sum_WcF_sub_le_fW`**: the two combined.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K4a

/-!
# S3-ES-Wt2 (O6, file K4b): the per-`c` discrepancy bound in Euler-product form

* `fp_mul_fp`, `cast_rpow_eq_fp` (`n^s = Π_{p^e ∥ n} (p^e)^s`), `card_divisors_eq_fp` (`τ(n) = Π (e+1)`),
  `fp_sPart`, `fp_rPart` (products over the smooth / rough prime factors).
* `small_eq`, `large_le`: the local inequalities; `sPart_rpow`, `rPart_le`: their products.
* `N0f M n = n⁺ + M + 16`, `Af`, `Bf` (smooth / rough parts of `|c|` at `N0f`), `Bc` (the K3 bound).
* **`norm_sum_WcF_sub_le_Bc`**: `‖Σ_{u<m} (WcF c u - μ_c)‖ ≤ Bc M n c` (for `0 < n`, `c ≠ 0`).
* **`Bc_le`**: `Bc M n c ≤ 33 · L · M^(33/32) · |c|² · fp (fW (N0f M n)) |c|`;
  **`norm_sum_WcF_sub_le_fW`**: the two combined.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-! ### Products over the factorization -/

lemma fp_mul_fp (f g : ℕ → ℕ → ℝ) (n : ℕ) :
    KL.fp f n * KL.fp g n = KL.fp (fun p e => f p e * g p e) n := by
  unfold KL.fp
  rw [← Finset.prod_mul_distrib]

lemma cast_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  simp only [Nat.cast_prod, Nat.cast_pow]

lemma cast_rpow_eq_fp {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    (n : ℝ) ^ s = KL.fp (fun p e => ((p : ℝ) ^ e) ^ s) n := by
  unfold KL.fp
  rw [cast_eq_prod hn]
  exact (Real.finsetProd_rpow _ _ (fun p _ => by positivity) s).symm

lemma card_divisors_eq_fp {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) = KL.fp (fun _ e => (e : ℝ) + 1) n := by
  unfold KL.fp
  rw [Nat.card_divisors hn]
  simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_one]

lemma fp_sPart (f : ℕ → ℕ → ℝ) (N c : ℕ) :
    KL.fp f (KL.sPart N c) = ∏ p ∈ c.primeFactors with p < N, f p (c.factorization p) := by
  unfold KL.sPart
  exact KL.fp_prod_prime_pow f (fun p => c.factorization p) (Finset.filter (fun p => p < N) c.primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)
    (fun p hp => KL.factorization_ne_zero_of_mem (Finset.mem_filter.1 hp).1)

lemma fp_rPart (f : ℕ → ℕ → ℝ) (N c : ℕ) :
    KL.fp f (KL.rPart N c) = ∏ p ∈ c.primeFactors with ¬ p < N, f p (c.factorization p) := by
  unfold KL.rPart
  exact KL.fp_prod_prime_pow f (fun p => c.factorization p)
    (Finset.filter (fun p => ¬ p < N) c.primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)
    (fun p hp => KL.factorization_ne_zero_of_mem (Finset.mem_filter.1 hp).1)

lemma sPart_ne_zero (N c : ℕ) : KL.sPart N c ≠ 0 := by
  unfold KL.sPart
  exact Finset.prod_ne_zero_iff.2 (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne_zero)

lemma rPart_ne_zero (N c : ℕ) : KL.rPart N c ≠ 0 := by
  unfold KL.rPart
  exact Finset.prod_ne_zero_iff.2 (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne_zero)

lemma coprime_rPart_of_lt {N c k : ℕ} (hk : 0 < k) (hkN : k < N) : (KL.rPart N c).Coprime k := by
  refine Nat.coprime_of_dvd (fun p hp hpB hpk => ?_)
  have hmem : p ∈ (KL.rPart N c).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpB, rPart_ne_zero N c⟩
  have h1 := KL.le_of_mem_primeFactors_rPart hmem
  have h2 := Nat.le_of_dvd hk hpk
  omega

/-! ### The local inequalities -/

lemma small_eq {N0 p e : ℕ} (hp : p.Prime) (hpN : p < N0) (he : e ≠ 0) :
    ((p : ℝ) ^ e) ^ ((7 : ℝ) / 4) * ((p : ℝ) ^ e) ^ ((1 : ℝ) / 32) =
      ((p : ℝ) ^ e) ^ (2 : ℝ) * fW N0 p e := by
  have hX : (0 : ℝ) < (p : ℝ) ^ e := pow_pos (by exact_mod_cast hp.pos) e
  rw [fW, if_neg he, if_pos hpN, Real.rpow_pow_comm (Nat.cast_nonneg p) (-(7 / 32 : ℝ)) e,
    ← Real.rpow_add hX, ← Real.rpow_add hX]
  norm_num

lemma large_le {N0 p e : ℕ} (hp : p.Prime) (hpN : ¬ p < N0) (he : e ≠ 0) :
    bq p e * ((e : ℝ) + 1) * ((p : ℝ) ^ e) ^ ((1 : ℝ) / 32) ≤ ((p : ℝ) ^ e) ^ (2 : ℝ) * fW N0 p e := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rcases eq_or_ne e 1 with rfl | he1
  · rw [bq, if_pos rfl, fW, if_neg one_ne_zero, if_neg hpN, if_pos rfl, pow_one]
    have h1 : (p : ℝ) ^ ((7 : ℝ) / 8) * (p : ℝ) ^ ((1 : ℝ) / 32) =
        (p : ℝ) ^ (2 : ℝ) * (p : ℝ) ^ (-(35 / 32 : ℝ)) := by
      rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]; norm_num
    have h2 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rw [h2]
    calc (p : ℝ) ^ ((7 : ℝ) / 8) * 2 * (p : ℝ) ^ ((1 : ℝ) / 32)
        = 2 * ((p : ℝ) ^ ((7 : ℝ) / 8) * (p : ℝ) ^ ((1 : ℝ) / 32)) := by ring
      _ = 2 * ((p : ℝ) ^ (2 : ℝ) * (p : ℝ) ^ (-(35 / 32 : ℝ))) := by rw [h1]
      _ ≤ (p : ℝ) ^ (2 : ℝ) * (2 * (p : ℝ) ^ (-(35 / 32 : ℝ))) := le_of_eq (by ring)
  · have hX : (0 : ℝ) < (p : ℝ) ^ e := pow_pos hp0 e
    rw [bq, if_neg he1, fW, if_neg he, if_neg hpN, if_neg he1, mul_pow,
      Real.rpow_pow_comm (Nat.cast_nonneg p) (-(31 / 32 : ℝ)) e]
    set X : ℝ := (p : ℝ) ^ e with hXdef
    have h1 : X ^ ((1 : ℝ) / 32) * X = X ^ (2 : ℝ) * X ^ (-(31 / 32 : ℝ)) := by
      rw [← Real.rpow_add_one hX.ne', ← Real.rpow_add hX]; norm_num
    have h2e : (e : ℝ) + 1 ≤ (2 : ℝ) ^ e := by
      have h : e + 1 ≤ 2 ^ e := (Nat.lt_two_pow_self : e < 2 ^ e)
      have h' : ((e + 1 : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := Nat.cast_le.2 h
      push_cast at h'
      exact h'
    have hY : 0 ≤ X ^ ((1 : ℝ) / 32) * X := by positivity
    calc X * ((e : ℝ) + 1) * X ^ ((1 : ℝ) / 32) = ((e : ℝ) + 1) * (X ^ ((1 : ℝ) / 32) * X) := by ring
      _ ≤ (2 : ℝ) ^ e * (X ^ ((1 : ℝ) / 32) * X) := mul_le_mul_of_nonneg_right h2e hY
      _ = X ^ (2 : ℝ) * ((2 : ℝ) ^ e * X ^ (-(31 / 32 : ℝ))) := by rw [h1]; ring

lemma sPart_rpow (N c : ℕ) :
    (KL.sPart N c : ℝ) ^ ((7 : ℝ) / 4) * (KL.sPart N c : ℝ) ^ ((1 : ℝ) / 32) =
      (KL.sPart N c : ℝ) ^ (2 : ℝ) * KL.fp (fW N) (KL.sPart N c) := by
  have h0 := sPart_ne_zero N c
  rw [cast_rpow_eq_fp h0 ((7 : ℝ) / 4), cast_rpow_eq_fp h0 ((1 : ℝ) / 32), cast_rpow_eq_fp h0 (2 : ℝ),
    fp_mul_fp, fp_mul_fp, fp_sPart, fp_sPart]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  exact small_eq (Nat.prime_of_mem_primeFactors hp.1) hp.2 (KL.factorization_ne_zero_of_mem hp.1)

lemma rPart_le (N c : ℕ) :
    Bq (KL.rPart N c) * ((KL.rPart N c).divisors.card : ℝ) * (KL.rPart N c : ℝ) ^ ((1 : ℝ) / 32) ≤
      (KL.rPart N c : ℝ) ^ (2 : ℝ) * KL.fp (fW N) (KL.rPart N c) := by
  have h0 := rPart_ne_zero N c
  rw [Bq, card_divisors_eq_fp h0, cast_rpow_eq_fp h0 ((1 : ℝ) / 32), cast_rpow_eq_fp h0 (2 : ℝ),
    fp_mul_fp, fp_mul_fp, fp_mul_fp, fp_rPart, fp_rPart]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · exact mul_nonneg (mul_nonneg (bq_nonneg _ _) (by positivity)) (by positivity)
  · rw [Finset.mem_filter] at hp
    exact large_le (Nat.prime_of_mem_primeFactors hp.1) hp.2 (KL.factorization_ne_zero_of_mem hp.1)

lemma one_add_log_le {x : ℝ} (hx : 1 ≤ x) : 1 + Real.log x ≤ 33 * x ^ ((1 : ℝ) / 32) := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (by norm_num : (0 : ℝ) < 1 / 32)
  have h2 : 1 ≤ x ^ ((1 : ℝ) / 32) := Real.one_le_rpow hx (by norm_num)
  have h3 : x ^ ((1 : ℝ) / 32) / (1 / 32) = 32 * x ^ ((1 : ℝ) / 32) := by ring
  linarith

/-! ### The per-`c` bound -/

/-- The cut-off `N0 = n⁺ + M + 16` between small and large primes. -/
def N0f (M : ℕ) (n : ℤ) : ℕ := n.toNat + M + 16

lemma sixteen_le_N0f (M : ℕ) (n : ℤ) : 16 ≤ N0f M n := by unfold N0f; omega

/-- The smooth part of `|c|`. -/
def Af (M : ℕ) (n c : ℤ) : ℕ := KL.sPart (N0f M n) c.natAbs

/-- The rough part of `|c|`. -/
def Bf (M : ℕ) (n c : ℤ) : ℕ := KL.rPart (N0f M n) c.natAbs

/-- The K3 bound for the modulus `c`. -/
def Bc (M : ℕ) [NeZero M] (n c : ℤ) : ℝ :=
  (Fintype.card (Fin 2 → ZMod M) : ℝ) * M * (Af M n c : ℝ) ^ ((7 : ℝ) / 4) * Bq (Bf M n c) *
    (((Bf M n c).divisors.card : ℝ) * (1 + Real.log (Af M n c * M * Bf M n c : ℕ)))

variable {M : ℕ} [NeZero M]

theorem norm_sum_WcF_sub_le_Bc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) (m : ℕ) :
    ‖∑ u ∈ range m, (WcF M n δ' c u - muc M n δ' c)‖ ≤ Bc M n c := by
  have hc' : c.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hc
  have : NeZero (Af M n c) := ⟨sPart_ne_zero _ _⟩
  have : NeZero (Bf M n c) := ⟨rPart_ne_zero _ _⟩
  have hM0 : 0 < M := NeZero.pos M
  have hAB : c.natAbs = Af M n c * Bf M n c := (KL.sPart_mul_rPart _ hc').symm
  have hcop : (Af M n c).Coprime (Bf M n c) := KL.coprime_sPart_rPart _ _
  have hBM : (Bf M n c).Coprime M := coprime_rPart_of_lt hM0 (by unfold N0f; omega)
  have hBn : (Bf M n c).Coprime n.toNat := coprime_rPart_of_lt (by omega) (by unfold N0f; omega)
  have hnB : IsUnit (n : ZMod (Bf M n c)) := by
    have h := Int.toNat_of_nonneg hn.le
    have e : (n : ZMod (Bf M n c)) = ((n.toNat : ℕ) : ZMod (Bf M n c)) := by
      calc (n : ZMod (Bf M n c)) = (((n.toNat : ℕ) : ℤ) : ZMod (Bf M n c)) := by rw [h]
        _ = ((n.toNat : ℕ) : ZMod (Bf M n c)) := Int.cast_natCast _
    rw [e, ZMod.isUnit_iff_coprime]
    exact hBn.symm
  have h11 : ∀ p ∈ (Bf M n c).primeFactors, 11 ≤ p := fun p hp => by
    have := KL.le_of_mem_primeFactors_rPart hp
    unfold N0f at this
    omega
  exact norm_sum_WcF_sub_le (A0 := Af M n c) (B := Bf M n c) n δ' hc hAB hcop hBM hnB h11 m

theorem Bc_le (n : ℤ) {c : ℤ} (hc : c ≠ 0) :
    Bc M n c ≤ 33 * (Fintype.card (Fin 2 → ZMod M) : ℝ) * (M : ℝ) ^ ((33 : ℝ) / 32) *
      (c.natAbs : ℝ) ^ 2 * KL.fp (fW (N0f M n)) c.natAbs := by
  have hc' : c.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hc
  have hM0 : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  unfold Bc Af Bf
  set N := N0f M n
  set A := KL.sPart N c.natAbs with hA
  set B := KL.rPart N c.natAbs with hB
  have hA0 : A ≠ 0 := sPart_ne_zero _ _
  have hB0 : B ≠ 0 := rPart_ne_zero _ _
  have hAB : A * B = c.natAbs := KL.sPart_mul_rPart _ hc'
  have hcop : A.Coprime B := KL.coprime_sPart_rPart _ _
  have hApart : (A : ℝ) ^ ((7 : ℝ) / 4) * (A : ℝ) ^ ((1 : ℝ) / 32) = (A : ℝ) ^ (2 : ℝ) * KL.fp (fW N) A :=
    sPart_rpow N c.natAbs
  have hBpart : Bq B * (B.divisors.card : ℝ) * (B : ℝ) ^ ((1 : ℝ) / 32) ≤
      (B : ℝ) ^ (2 : ℝ) * KL.fp (fW N) B := rPart_le N c.natAbs
  have hx : (1 : ℝ) ≤ ((A * M * B : ℕ) : ℝ) :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hA0 (NeZero.ne M)) hB0))
  have hlog := one_add_log_le hx
  have hsplit : ((A * M * B : ℕ) : ℝ) ^ ((1 : ℝ) / 32) =
      (A : ℝ) ^ ((1 : ℝ) / 32) * (M : ℝ) ^ ((1 : ℝ) / 32) * (B : ℝ) ^ ((1 : ℝ) / 32) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [hsplit] at hlog
  have hm : (M : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 32) = (M : ℝ) ^ ((33 : ℝ) / 32) := by
    rw [mul_comm, ← Real.rpow_add_one hM0.ne']; norm_num
  have hc2 : (c.natAbs : ℝ) ^ 2 = (A : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
    rw [← hAB, Nat.cast_mul, mul_pow]
  have hfp : KL.fp (fW N) c.natAbs = KL.fp (fW N) A * KL.fp (fW N) B := by
    rw [← hAB, KL.fp_mul _ hcop]
  set L : ℝ := (Fintype.card (Fin 2 → ZMod M) : ℝ) with hL
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hτ0 : (0 : ℝ) ≤ (B.divisors.card : ℝ) := Nat.cast_nonneg _
  have hK0 : 0 ≤ L * (M : ℝ) * (A : ℝ) ^ ((7 : ℝ) / 4) * Bq B :=
    mul_nonneg (by positivity) (Bq_nonneg B)
  have hFA := fp_fW_nonneg N A
  calc L * (M : ℝ) * (A : ℝ) ^ ((7 : ℝ) / 4) * Bq B *
        ((B.divisors.card : ℝ) * (1 + Real.log ((A * M * B : ℕ) : ℝ)))
      ≤ L * (M : ℝ) * (A : ℝ) ^ ((7 : ℝ) / 4) * Bq B *
        ((B.divisors.card : ℝ) * (33 * ((A : ℝ) ^ ((1 : ℝ) / 32) * (M : ℝ) ^ ((1 : ℝ) / 32) *
          (B : ℝ) ^ ((1 : ℝ) / 32)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hτ0) hK0
    _ = 33 * L * ((M : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 32)) *
          ((A : ℝ) ^ ((7 : ℝ) / 4) * (A : ℝ) ^ ((1 : ℝ) / 32)) *
          (Bq B * (B.divisors.card : ℝ) * (B : ℝ) ^ ((1 : ℝ) / 32)) := by ring
    _ ≤ 33 * L * ((M : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 32)) * ((A : ℝ) ^ (2 : ℝ) * KL.fp (fW N) A) *
          ((B : ℝ) ^ (2 : ℝ) * KL.fp (fW N) B) := by
        rw [hApart]
        exact mul_le_mul_of_nonneg_left hBpart
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) hFA))
    _ = 33 * L * (M : ℝ) ^ ((33 : ℝ) / 32) * (c.natAbs : ℝ) ^ 2 * KL.fp (fW N) c.natAbs := by
        rw [hm, Real.rpow_two, Real.rpow_two, hc2, hfp]; ring

theorem norm_sum_WcF_sub_le_fW {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) (m : ℕ) :
    ‖∑ u ∈ range m, (WcF M n δ' c u - muc M n δ' c)‖ ≤
      33 * (Fintype.card (Fin 2 → ZMod M) : ℝ) * (M : ℝ) ^ ((33 : ℝ) / 32) *
        (c.natAbs : ℝ) ^ 2 * KL.fp (fW (N0f M n)) c.natAbs :=
  (norm_sum_WcF_sub_le_Bc hn δ' hc m).trans (Bc_le n hc)

end RamanujanPetersson.EllW2


