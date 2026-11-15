-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV8
-- name    : RPLib_S3_EllW2MV8
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:53:54.174198+00:00
-- url     : https://prove2.me/theorems/4773bc0c-98c3-43b0-bdb3-8117f1f1141b
-- title:
--   The Eichler-Selberg trace formula in weight two: the mean of `fpm` (assembly of MV1-MV7)
-- statement:
--   The mean of `fpm` (assembly of MV1-MV7).
--
--   * `Bm r = Σ_{G ∈ T_r} L̄(G) / #T_r`; `muc_eq`: `muc c = N(|c|)/(2|c|) · B(c̄)` (real, `≥ 0`).
--   * `fpm_eq`: `fpm k = N(k)/k · (B(k̄) + B(-k̄))/2`.
--   * `Am_eq_card`: `A_M(r) = #T_r / M²`; `sum_W_card`: `Σ_r (B r + B(-r))/2 · #T_r = Σ_r #T_r` (MV7).
--   * **`tendsto_fpm_mean`** (`n ≠ 0`, `|n| ⊥ M`, `δ'` a unit):
--     `(1/N) Σ_{k ≤ N} fpm k → σ_{-1}(|n|) · 6/π²`.
--   * **`tendsto_ZS_val`** (`0 < n`): `s · ZS(s, y) → 3 σ_{-1}(n)` as `s → 0+`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV7
import Definitions.Def_RPLib_S3_EllW2MV6c
import Definitions.Def_RPLib_S3_EllW2AB2

/-!
# S3-ES-Wt2 (O6, file MV8): the mean of `fpm` (assembly of MV1-MV7)

* `Bm r = Σ_{G ∈ T_r} L̄(G) / #T_r`; `muc_eq`: `muc c = N(|c|)/(2|c|) · B(c̄)` (real, `≥ 0`).
* `fpm_eq`: `fpm k = N(k)/k · (B(k̄) + B(-k̄))/2`.
* `Am_eq_card`: `A_M(r) = #T_r / M²`; `sum_W_card`: `Σ_r (B r + B(-r))/2 · #T_r = Σ_r #T_r` (MV7).
* **`tendsto_fpm_mean`** (`n ≠ 0`, `|n| ⊥ M`, `δ'` a unit):
  `(1/N) Σ_{k ≤ N} fpm k → σ_{-1}(|n|) · 6/π²`.
* **`tendsto_ZS_val`** (`0 < n`): `s · ZS(s, y) → 3 σ_{-1}(n)` as `s → 0+`.
-/

open Finset Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- `B(r) = Σ_{G ∈ T_r} L̄(G) / #T_r`. -/
def Bm (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (r : ZMod M) : ℝ :=
  (∑ G ∈ TR M n r, (Lbar M δ' G : ℝ)) / (TR M n r).card

lemma Bm_nonneg (n : ℤ) (δ' r : ZMod M) : 0 ≤ Bm M n δ' r :=
  div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [NeZero M] in
lemma isUnit_of_coprime {n : ℤ} (h : Nat.Coprime n.natAbs M) : IsUnit (n : ZMod M) := by
  have hu := (ZMod.isUnit_iff_coprime n.natAbs M).2 h
  rcases Int.natAbs_eq n with hn | hn
  · rw [hn]
    simpa using hu
  · rw [hn]
    simpa using hu

theorem muc_eq {n : ℤ} (hnM : Nat.Coprime n.natAbs M) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) :
    muc M n δ' c =
      (((Nk n c.natAbs : ℝ) / (2 * c.natAbs) * Bm M n δ' (c : ZMod M) : ℝ) : ℂ) := by
  have hn := isUnit_of_coprime hnM
  have : NeZero (c.natAbs * M) := ⟨(Nat.mul_pos (Int.natAbs_pos.2 hc) (NeZero.pos M)).ne'⟩
  have hMq : M ∣ c.natAbs * M := dvd_mul_left M _
  have h1 := two_mul_muc_eq_fib n δ' hc rfl hMq hn
  have h2 := card_Xc_eq n hc rfl hMq hn
  rw [card_Xc_eq_Nk n hc (q := c.natAbs * M) rfl] at h2
  rw [Tc_eq_TR] at h1 h2
  rw [Nat.cast_mul] at h1
  have hT : 0 < (TR M n (c : ZMod M)).card := card_TR_pos n hnM _
  have hTc : ((TR M n (c : ZMod M)).card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
  have hc' : (c.natAbs : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Int.natAbs_pos.2 hc).ne'
  have h2' : (M : ℂ) * M * Nk n c.natAbs =
      fibC M n c hMq (G0c M n c) * (TR M n (c : ZMod M)).card := by exact_mod_cast h2
  have hfib : (fibC M n c hMq (G0c M n c) : ℂ) =
      M * M * Nk n c.natAbs / (TR M n (c : ZMod M)).card := by
    rw [eq_div_iff hTc]
    exact h2'.symm
  have hden : (2 * (M : ℂ) * (c.natAbs * M)) ≠ 0 := by
    have h2c : (2 : ℂ) ≠ 0 := two_ne_zero
    exact mul_ne_zero (mul_ne_zero h2c hM) (mul_ne_zero hc' hM)
  have hmuc : muc M n δ' c = (fibC M n c hMq (G0c M n c) : ℂ) *
      (∑ G ∈ TR M n (c : ZMod M), (Lbar M δ' G : ℂ)) / (2 * (M : ℂ) * (c.natAbs * M)) := by
    rw [eq_div_iff hden, ← h1]
    ring
  rw [hmuc, hfib, Bm]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sum,
    Complex.ofReal_ofNat]
  first | (field_simp; ring) | field_simp

theorem norm_muc_eq {n : ℤ} (hnM : Nat.Coprime n.natAbs M) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) :
    ‖muc M n δ' c‖ = (Nk n c.natAbs : ℝ) / (2 * c.natAbs) * Bm M n δ' (c : ZMod M) := by
  rw [muc_eq hnM δ' hc, Complex.norm_of_nonneg
    (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) (Bm_nonneg _ _ _))]

theorem fpm_eq {n : ℤ} (hnM : Nat.Coprime n.natAbs M) (δ' : ZMod M) {k : ℕ} (hk : 0 < k) :
    fpm M n δ' k = (Nk n k : ℝ) / k *
      ((Bm M n δ' (k : ZMod M) + Bm M n δ' (-(k : ZMod M))) / 2) := by
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (-(k : ℤ)) ≠ 0 := neg_ne_zero.2 hk0
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [fpm, norm_muc_eq hnM δ' hk0, norm_muc_eq hnM δ' hk1]
  simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
  field_simp

theorem Am_eq_card {n : ℤ} (hnM : Nat.Coprime n.natAbs M) (r : ZMod M) :
    Am M r = (TR M n r).card / ((M : ℝ) * M) := by
  have he : Nat.gcd M r.val ∣ M := Nat.gcd_dvd_left _ _
  have he0 : (Nat.gcd M r.val : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.gcd_pos_of_pos_left _ (NeZero.pos M)).ne'
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
  rw [Am, card_TR n hnM r, Nat.gcd_comm r.val M, Nat.cast_mul, Nat.cast_mul, Nat.cast_div he he0]
  first | (field_simp; ring) | field_simp

theorem sum_W_card {n : ℤ} (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M} (hδ : IsUnit δ') :
    ∑ r : ZMod M, (Bm M n δ' r + Bm M n δ' (-r)) / 2 * (TR M n r).card =
      ∑ r : ZMod M, ((TR M n r).card : ℝ) := by
  have hBc : ∀ r : ZMod M, Bm M n δ' r * (TR M n r).card = ∑ G ∈ TR M n r, (Lbar M δ' G : ℝ) := by
    intro r
    rw [Bm, div_mul_cancel₀]
    exact Nat.cast_ne_zero.2 (card_TR_pos n hnM r).ne'
  have hterm : ∀ r : ZMod M, (Bm M n δ' r + Bm M n δ' (-r)) / 2 * (TR M n r).card =
      ((∑ G ∈ TR M n r, (Lbar M δ' G : ℝ)) + ∑ G ∈ TR M n (-r), (Lbar M δ' G : ℝ)) / 2 := by
    intro r
    rw [← hBc r, ← hBc (-r), card_TR_neg n hnM r]
    ring
  have hneg : ∑ r : ZMod M, ∑ G ∈ TR M n (-r), (Lbar M δ' G : ℝ) =
      ∑ r : ZMod M, ∑ G ∈ TR M n r, (Lbar M δ' G : ℝ) := by
    first
    | exact (Equiv.neg (ZMod M)).sum_comp (fun r => ∑ G ∈ TR M n r, (Lbar M δ' G : ℝ))
    | exact Fintype.sum_equiv (Equiv.neg (ZMod M)) _ _ (fun _ => rfl)
  rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.sum_div, Finset.sum_add_distrib, hneg,
    sum_TR_Lbar (isUnit_of_coprime hnM) hδ]
  ring

theorem tendsto_fpm_mean {n : ℤ} (hn0 : n ≠ 0) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, fpm M n δ' k) / (N : ℝ)) atTop
      (𝓝 ((∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * (6 / Real.pi ^ 2))) := by
  have hsum : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, fpm M n δ' k) / (N : ℝ) =
      ∑ r : ZMod M, (Bm M n δ' r + Bm M n δ' (-r)) / 2 *
        ((∑ k ∈ Icc 1 N, (if (k : ZMod M) = r then (Nk n k : ℝ) / k else 0)) / N) := by
    intro N
    have h : ∑ k ∈ Finset.Icc 1 N, fpm M n δ' k = ∑ r : ZMod M, (Bm M n δ' r + Bm M n δ' (-r)) / 2 *
        (∑ k ∈ Icc 1 N, (if (k : ZMod M) = r then (Nk n k : ℝ) / k else 0)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [fpm_eq hnM δ' (mem_Icc.1 hk).1]
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [mem_univ, if_true]
      ring
    rw [h, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_div_assoc]
  have hval : ∑ r : ZMod M, (Bm M n δ' r + Bm M n δ' (-r)) / 2 * Dm M n r =
      (∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * (6 / Real.pi ^ 2) := by
    rw [← sum_Dm hn0 hnM]
    have hD : ∀ r : ZMod M, Dm M n r = (TR M n r).card *
        ((∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * Cm M / M / ((M : ℝ) * M)) := by
      intro r
      rw [Dm, Am_eq_card hnM r]
      ring
    simp_rw [hD]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_W_card hnM hδ]
  have h1 := tendsto_finsetSum (univ : Finset (ZMod M)) fun r _ =>
    (tendsto_res hn0 hnM r).const_mul ((Bm M n δ' r + Bm M n δ' (-r)) / 2)
  rw [hval] at h1
  exact h1.congr fun N => (hsum N).symm

theorem tendsto_ZS_val {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => s * ZS M n δ' s y) (𝓝[>] 0)
      (𝓝 (3 * ∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h)) := by
  have h := tendsto_ZS hn δ' (tendsto_fpm_mean hn.ne' hnM hδ) hy
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  convert h using 2
  field_simp
  ring

end RamanujanPetersson.EllW2


