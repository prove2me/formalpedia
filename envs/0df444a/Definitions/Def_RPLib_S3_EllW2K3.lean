-- Prove2me | Definitions.Def_RPLib_S3_EllW2K3
-- name    : RPLib_S3_EllW2K3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:56:45.345262+00:00
-- url     : https://prove2.me/theorems/09e66dff-8a79-475f-a990-4029d7d8ee41
-- title:
--   The Eichler-Selberg trace formula in weight two: the `j`-sum of the discrepancy bound
-- statement:
--   The `j`-sum of the discrepancy bound.
--
--   * `Bq B = Π_{p^e ∥ B} (p^(7/8) if e = 1, p^e otherwise)`; **`Bnd_le_Bq`**: `Bnd B m r ≤ Bq B · gcd(m, B)^(1/8)`.
--   * `sum_range_inv_succ_le`: `Σ_{i<n} 1/(i+1) ≤ 1 + log n`; `sum_range_dvd_inv_le`: the same over multiples of `e`, `≤ (1 + log q)/e`.
--   * `sum_gcd_inv_le`: `Σ_{w<q} gcd(w+1, B)^(1/8)/(w+1) ≤ τ(B)(1 + log q)`.
--   * **`sum_dft_weight_le`**: `Σ_{j ≠ 0 mod q} gcd(j, B)^(1/8) / (2 min(j, q-j)) ≤ τ(B)(1 + log q)` for `B ∣ q`.
--   * **`norm_sum_WcF_sub_le`**: for `|c| = A0 B` as in K2c,
--     `‖Σ_{u<m} (WcF c u - μ_c)‖ ≤ #(Fin 2 → ZMod M) · M · A0^(7/4) · Bq B · τ(B) (1 + log (A0 M B))`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K2d
import Definitions.Def_RPLib_S3_KloostermanC

/-!
# S3-ES-Wt2 (O6, file K3): the `j`-sum of the discrepancy bound

* `Bq B = Π_{p^e ∥ B} (p^(7/8) if e = 1, p^e otherwise)`; **`Bnd_le_Bq`**: `Bnd B m r ≤ Bq B · gcd(m, B)^(1/8)`.
* `sum_range_inv_succ_le`: `Σ_{i<n} 1/(i+1) ≤ 1 + log n`; `sum_range_dvd_inv_le`: the same over multiples of `e`, `≤ (1 + log q)/e`.
* `sum_gcd_inv_le`: `Σ_{w<q} gcd(w+1, B)^(1/8)/(w+1) ≤ τ(B)(1 + log q)`.
* **`sum_dft_weight_le`**: `Σ_{j ≠ 0 mod q} gcd(j, B)^(1/8) / (2 min(j, q-j)) ≤ τ(B)(1 + log q)` for `B ∣ q`.
* **`norm_sum_WcF_sub_le`**: for `|c| = A0 B` as in K2c,
  `‖Σ_{u<m} (WcF c u - μ_c)‖ ≤ #(Fin 2 → ZMod M) · M · A0^(7/4) · Bq B · τ(B) (1 + log (A0 M B))`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-! ### The local bound -/

/-- Local factor of `Bq`: `p^(7/8)` at exponent `1`, `p^e` otherwise. -/
def bq (p e : ℕ) : ℝ := if e = 1 then (p : ℝ) ^ ((7 : ℝ) / 8) else (p : ℝ) ^ e

/-- `Bq B = Π_{p^e ∥ B} bq p e`. -/
def Bq (B : ℕ) : ℝ := KL.fp bq B

lemma bq_nonneg (p e : ℕ) : 0 ≤ bq p e := by unfold bq; split_ifs <;> positivity

lemma Bq_nonneg (B : ℕ) : 0 ≤ Bq B := by
  unfold Bq KL.fp
  exact Finset.prod_nonneg (fun _ _ => bq_nonneg _ _)

lemma bp_le_bq_mul {p : ℕ} (hp : p.Prime) (e m : ℕ) (r : ℤ) :
    KL.bp p e (m : ℤ) r ≤ bq p e * KL.dF m p := by
  have hD := KL.one_le_dF hp m
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold KL.bp bq
  by_cases he : e = 1
  · rw [if_pos he, if_pos he]
    by_cases hd : (p : ℤ) ∣ (m : ℤ) ∧ (p : ℤ) ∣ r
    · rw [if_pos hd, KL.dF, if_pos (Int.natCast_dvd_natCast.mp hd.1), ← Real.rpow_add hp0]
      norm_num
    · rw [if_neg hd]
      exact le_mul_of_one_le_right (by positivity) hD
  · rw [if_neg he, if_neg he]
    exact le_mul_of_one_le_right (by positivity) hD

lemma prod_dF_primeFactors_le {B : ℕ} (hB : B ≠ 0) (m : ℕ) :
    ∏ p ∈ B.primeFactors, KL.dF m p ≤ (Nat.gcd m B : ℝ) ^ ((1 : ℝ) / 8) := by
  have hg : Nat.gcd m B ≠ 0 := (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hB)).ne'
  have h1 : ∏ p ∈ B.primeFactors, KL.dF m p =
      ∏ p ∈ B.primeFactors with p.Prime, KL.dF (Nat.gcd m B) p := by
    rw [Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpB : p ∣ B := Nat.dvd_of_mem_primeFactors hp
    unfold KL.dF
    simp only [Nat.dvd_gcd_iff, hpB, and_true]
  rw [h1]
  exact KL.prod_dF_le _ hg

/-- **The Kloosterman bound with the `gcd` factored out.** -/
theorem Bnd_le_Bq {B : ℕ} (hB : B ≠ 0) (m : ℕ) (r : ℤ) :
    KL.Bnd B (m : ℤ) r ≤ Bq B * (Nat.gcd m B : ℝ) ^ ((1 : ℝ) / 8) := by
  have h1 : KL.Bnd B (m : ℤ) r ≤ ∏ p ∈ B.primeFactors, (bq p (B.factorization p) * KL.dF m p) := by
    unfold KL.Bnd
    exact Finset.prod_le_prod (fun p _ => KL.bp_nonneg _ _ _ _)
      (fun p hp => bp_le_bq_mul (Nat.prime_of_mem_primeFactors hp) _ m r)
  have h2 : ∏ p ∈ B.primeFactors, (bq p (B.factorization p) * KL.dF m p) =
      Bq B * ∏ p ∈ B.primeFactors, KL.dF m p := by
    rw [Finset.prod_mul_distrib]; rfl
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (prod_dF_primeFactors_le hB m) (Bq_nonneg B))

/-! ### Harmonic sums -/

lemma sum_range_inv_succ_le (n : ℕ) : ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have he : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one,
      Nat.cast_add, Nat.cast_one]
  linarith

lemma sum_range_dvd_inv_le {e : ℕ} (he : 0 < e) (q : ℕ) :
    ∑ w ∈ range q, (if e ∣ w + 1 then ((w : ℝ) + 1)⁻¹ else 0) ≤ (e : ℝ)⁻¹ * (1 + Real.log q) := by
  rw [← Finset.sum_filter]
  set S := (range q).filter (fun w => e ∣ w + 1) with hS
  set φ : ℕ → ℕ := fun w => (w + 1) / e - 1 with hφ
  have hφw : ∀ w, φ w = (w + 1) / e - 1 := fun w => rfl
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hterm : ∀ w ∈ S, ((w : ℝ) + 1)⁻¹ = (e : ℝ)⁻¹ * ((φ w : ℝ) + 1)⁻¹ := by
    intro w hw
    have hdvd : e ∣ w + 1 := (Finset.mem_filter.1 hw).2
    have h1 : 0 < (w + 1) / e := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos w) hdvd) he
    have h2 : φ w + 1 = (w + 1) / e := by rw [hφw]; omega
    have h3 : ((φ w : ℝ) + 1) = ((w : ℝ) + 1) / e := by
      have := congrArg (fun k : ℕ => (k : ℝ)) h2
      simp only [Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_div hdvd he0, Nat.cast_add, Nat.cast_one]
    rw [h3, inv_div, ← mul_div_assoc, inv_mul_cancel₀ he0, one_div]
  have hinj : Set.InjOn φ S := by
    intro w hw w' hw' h
    have hw1 : w ∈ S := hw
    have hw1' : w' ∈ S := hw'
    have hd : e ∣ w + 1 := (Finset.mem_filter.1 hw1).2
    have hd' : e ∣ w' + 1 := (Finset.mem_filter.1 hw1').2
    have h1 : 0 < (w + 1) / e := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos w) hd) he
    have h1' : 0 < (w' + 1) / e := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos w') hd') he
    have h2 : (w + 1) / e = (w' + 1) / e := by
      have h0 : φ w = φ w' := h
      rw [hφw, hφw] at h0
      omega
    have e1 := Nat.mul_div_cancel' hd
    have e2 := Nat.mul_div_cancel' hd'
    rw [h2] at e1
    omega
  have hsub : S.image φ ⊆ range q := by
    intro k hk
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hk
    have hwq : w < q := Finset.mem_range.1 (Finset.mem_filter.1 hw).1
    rw [Finset.mem_range, hφw]
    have : (w + 1) / e ≤ w + 1 := Nat.div_le_self _ _
    omega
  calc ∑ w ∈ S, ((w : ℝ) + 1)⁻¹ = ∑ w ∈ S, (e : ℝ)⁻¹ * ((φ w : ℝ) + 1)⁻¹ :=
        Finset.sum_congr rfl hterm
    _ = (e : ℝ)⁻¹ * ∑ k ∈ S.image φ, ((k : ℝ) + 1)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (e : ℝ)⁻¹ * ∑ k ∈ range q, ((k : ℝ) + 1)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ (e : ℝ)⁻¹ * (1 + Real.log q) :=
        mul_le_mul_of_nonneg_left (sum_range_inv_succ_le q) (by positivity)

lemma rpow_gcd_le_sum (B v : ℕ) (hB : B ≠ 0) :
    (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) ≤
      ∑ e ∈ B.divisors, (if e ∣ v then (e : ℝ) ^ ((1 : ℝ) / 8) else 0) := by
  have hmem : Nat.gcd v B ∈ B.divisors := Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right v B, hB⟩
  have h := Finset.single_le_sum (f := fun e => if e ∣ v then (e : ℝ) ^ ((1 : ℝ) / 8) else 0)
    (fun e _ => by split_ifs <;> positivity) hmem
  rw [if_pos (Nat.gcd_dvd_left v B)] at h
  exact h

theorem sum_gcd_inv_le {B : ℕ} (hB : B ≠ 0) (q : ℕ) :
    ∑ w ∈ range q, (Nat.gcd (w + 1) B : ℝ) ^ ((1 : ℝ) / 8) * ((w : ℝ) + 1)⁻¹ ≤
      (B.divisors.card : ℝ) * (1 + Real.log q) := by
  have hlog : 0 ≤ 1 + Real.log q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
      linarith
  calc ∑ w ∈ range q, (Nat.gcd (w + 1) B : ℝ) ^ ((1 : ℝ) / 8) * ((w : ℝ) + 1)⁻¹
      ≤ ∑ w ∈ range q, ∑ e ∈ B.divisors,
          (if e ∣ w + 1 then (e : ℝ) ^ ((1 : ℝ) / 8) else 0) * ((w : ℝ) + 1)⁻¹ := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (rpow_gcd_le_sum B (w + 1) hB) (by positivity)
    _ = ∑ e ∈ B.divisors, (e : ℝ) ^ ((1 : ℝ) / 8) *
          ∑ w ∈ range q, (if e ∣ w + 1 then ((w : ℝ) + 1)⁻¹ else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        split_ifs <;> simp
    _ ≤ ∑ e ∈ B.divisors, (e : ℝ) ^ ((1 : ℝ) / 8) * ((e : ℝ)⁻¹ * (1 + Real.log q)) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have he0 : 0 < e := Nat.pos_of_mem_divisors he
        exact mul_le_mul_of_nonneg_left (sum_range_dvd_inv_le he0 q) (by positivity)
    _ ≤ ∑ e ∈ B.divisors, (1 + Real.log q) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have he1 : (1 : ℝ) ≤ e := by exact_mod_cast Nat.pos_of_mem_divisors he
        have h : (e : ℝ) ^ ((1 : ℝ) / 8) * (e : ℝ)⁻¹ ≤ 1 := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add (by linarith)]
          exact Real.rpow_le_one_of_one_le_of_nonpos he1 (by norm_num)
        rw [← mul_assoc]
        exact mul_le_of_le_one_left hlog h
    _ = (B.divisors.card : ℝ) * (1 + Real.log q) := by
        rw [Finset.sum_const, nsmul_eq_mul]

lemma gcd_eq_of_add_eq {a b q B : ℕ} (hB : B ∣ q) (h : a + b = q) : Nat.gcd a B = Nat.gcd b B := by
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
    have h1 : Nat.gcd a B ∣ a + b := by rw [h]; exact (Nat.gcd_dvd_right a B).trans hB
    exact (Nat.dvd_add_right (Nat.gcd_dvd_left a B)).1 h1
  · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
    have h1 : Nat.gcd b B ∣ a + b := by rw [h]; exact (Nat.gcd_dvd_right b B).trans hB
    exact (Nat.dvd_add_left (Nat.gcd_dvd_left b B)).1 h1

/-- **The weighted `j`-sum.** -/
theorem sum_dft_weight_le {q B : ℕ} [NeZero q] (hBq : B ∣ q) (hB : B ≠ 0) :
    ∑ j ∈ univ.erase (0 : ZMod q),
        (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) ≤
      (B.divisors.card : ℝ) * (1 + Real.log q) := by
  have h1 : ∑ j ∈ univ.erase (0 : ZMod q),
        (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) =
      ∑ j : ZMod q, (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) :=
    Finset.sum_erase _ (by simp)
  have h2 : ∑ j : ZMod q, (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) /
        (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) =
      ∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min v (q - v) : ℕ) : ℝ)) :=
    sum_zmod_val' (fun v => (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min v (q - v) : ℕ) : ℝ)))
  have hpt : ∀ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min v (q - v) : ℕ) : ℝ)) ≤
      (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹ / 2 +
        (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * ((q - v : ℕ) : ℝ)⁻¹ / 2 := by
    intro v _
    have ha : (0 : ℝ) ≤ (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹ / 2 := by positivity
    have hb : (0 : ℝ) ≤ (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * ((q - v : ℕ) : ℝ)⁻¹ / 2 := by positivity
    rcases le_total v (q - v) with h | h
    · rw [min_eq_left h]
      have : (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) / (2 * (v : ℝ)) =
          (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹ / 2 := by ring
      linarith
    · rw [min_eq_right h]
      have : (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((q - v : ℕ) : ℝ)) =
          (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * ((q - v : ℕ) : ℝ)⁻¹ / 2 := by ring
      linarith
  have hA : ∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹ ≤
      ∑ w ∈ range q, (Nat.gcd (w + 1) B : ℝ) ^ ((1 : ℝ) / 8) * ((w : ℝ) + 1)⁻¹ := by
    calc ∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹
        ≤ ∑ v ∈ range (q + 1), (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ q))
            (fun _ _ _ => by positivity)
      _ = ∑ w ∈ range q, (Nat.gcd (w + 1) B : ℝ) ^ ((1 : ℝ) / 8) * ((w : ℝ) + 1)⁻¹ := by
          rw [Finset.sum_range_succ']
          simp
  have hB2 : ∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * ((q - v : ℕ) : ℝ)⁻¹ =
      ∑ w ∈ range q, (Nat.gcd (w + 1) B : ℝ) ^ ((1 : ℝ) / 8) * ((w : ℝ) + 1)⁻¹ := by
    refine (Finset.sum_range_reflect _ q).symm.trans (Finset.sum_congr rfl (fun j hj => ?_))
    have hjq : j < q := Finset.mem_range.1 hj
    have hsub : q - (q - 1 - j) = j + 1 := by omega
    have hgcd : Nat.gcd (q - 1 - j) B = Nat.gcd (j + 1) B := gcd_eq_of_add_eq hBq (by omega)
    rw [hsub, hgcd, Nat.cast_add, Nat.cast_one]
  rw [h1, h2]
  calc ∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min v (q - v) : ℕ) : ℝ))
      ≤ ∑ v ∈ range q, ((Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹ / 2 +
          (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * ((q - v : ℕ) : ℝ)⁻¹ / 2) := Finset.sum_le_sum hpt
    _ = (∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * (v : ℝ)⁻¹) / 2 +
          (∑ v ∈ range q, (Nat.gcd v B : ℝ) ^ ((1 : ℝ) / 8) * ((q - v : ℕ) : ℝ)⁻¹) / 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    _ ≤ ∑ w ∈ range q, (Nat.gcd (w + 1) B : ℝ) ^ ((1 : ℝ) / 8) * ((w : ℝ) + 1)⁻¹ := by
        rw [hB2]; linarith
    _ ≤ _ := sum_gcd_inv_le hB q

/-! ### The discrepancy of `WcF c ·` -/

variable {M : ℕ} [NeZero M]

/-- **Per-`c` discrepancy bound** (`|c| = A0 B` as in `norm_dft_WcF_le`). -/
theorem norm_sum_WcF_sub_le (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {A0 B : ℕ} [NeZero A0] [NeZero B]
    (hAB : c.natAbs = A0 * B) (hcop : A0.Coprime B) (hBM : B.Coprime M) (hnB : IsUnit (n : ZMod B))
    (h11 : ∀ p ∈ B.primeFactors, 11 ≤ p) (m : ℕ) :
    ‖∑ u ∈ range m, (WcF M n δ' c u - muc M n δ' c)‖ ≤
      (Fintype.card (Fin 2 → ZMod M) : ℝ) * M * (A0 : ℝ) ^ ((7 : ℝ) / 4) * Bq B *
        ((B.divisors.card : ℝ) * (1 + Real.log (A0 * M * B : ℕ))) := by
  have hq : A0 * M * B = c.natAbs * M := by rw [hAB]; ring
  have hf : ∀ t : ℤ, WcF M n δ' c (t + ((A0 * M * B : ℕ) : ℤ)) = WcF M n δ' c t := by
    intro t; rw [hq]; exact WcF_periodic n δ' c t
  have hμ : ∑ u ∈ range (A0 * M * B), WcF M n δ' c (u : ℤ) =
      ((A0 * M * B : ℕ) : ℂ) * muc M n δ' c := by
    rw [hq]; exact sum_WcF_eq n δ' hc
  refine (norm_sum_sub_le_dft_int hf hμ m).trans ?_
  set K : ℝ := (Fintype.card (Fin 2 → ZMod M) : ℝ) * M * (A0 : ℝ) ^ ((7 : ℝ) / 4) * Bq B with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (Bq_nonneg B)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hterm : ∀ j : ZMod (A0 * M * B),
      ‖ZMod.dft (fun x : ZMod (A0 * M * B) => WcF M n δ' c (x.val : ℤ)) j‖ ≤
        K * (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) := by
    intro j
    have h2 := norm_dft_WcF_le n δ' hc hAB hcop hBM hnB h11 j
    have hPA := card_PA_le M n (A0 := A0)
    have hBnd := Bnd_le_Bq (NeZero.ne B) j.val ((j.val : ℤ) * n)
    have hL0 : (0 : ℝ) ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := Nat.cast_nonneg _
    have h3 := mul_le_mul (mul_le_mul_of_nonneg_left hPA hL0) hBnd (KL.Bnd_nonneg _ _ _)
      (by positivity)
    have h4 : 2 * (M : ℝ) * ‖ZMod.dft (fun x : ZMod (A0 * M * B) => WcF M n δ' c (x.val : ℤ)) j‖ ≤
        2 * (M : ℝ) * (K * (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8)) := by
      refine h2.trans (h3.trans (le_of_eq ?_))
      rw [hK]; ring
    exact le_of_mul_le_mul_left h4 (by positivity)
  calc ∑ j ∈ univ.erase (0 : ZMod (A0 * M * B)),
        ‖ZMod.dft (fun x : ZMod (A0 * M * B) => WcF M n δ' c (x.val : ℤ)) j‖ /
          (2 * ((min j.val (A0 * M * B - j.val) : ℕ) : ℝ))
      ≤ ∑ j ∈ univ.erase (0 : ZMod (A0 * M * B)),
          K * ((Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) /
            (2 * ((min j.val (A0 * M * B - j.val) : ℕ) : ℝ))) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (hterm j) (by positivity)
    _ = K * ∑ j ∈ univ.erase (0 : ZMod (A0 * M * B)),
          (Nat.gcd j.val B : ℝ) ^ ((1 : ℝ) / 8) / (2 * ((min j.val (A0 * M * B - j.val) : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ K * ((B.divisors.card : ℝ) * (1 + Real.log (A0 * M * B : ℕ))) :=
        mul_le_mul_of_nonneg_left (sum_dft_weight_le (Dvd.intro_left _ rfl) (NeZero.ne B)) hK0

end RamanujanPetersson.EllW2


