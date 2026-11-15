-- Prove2me | Definitions.Def_RPLib_S3_EllW2K4a
-- name    : RPLib_S3_EllW2K4a
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:59:46.347494+00:00
-- url     : https://prove2.me/theorems/1f584e78-63d9-4e01-b52b-3cce3305a5b9
-- title:
--   The Eichler-Selberg trace formula in weight two: the Euler product for the `c`-sum majorant
-- statement:
--   The Euler product for the `c`-sum majorant.
--
--   * `sum_range_fp_le`, `summable_fp`, `tsum_fp_le`: a generic Euler-product bound for `fp f`
--     (`f p 0 = 1`, `f ≥ 0`, per-prime sums bounded by `K` in every finite product).
--   * `fW N0 p e`: `(p^(-7/32))^e` for `p < N0`; `2 p^(-35/32)` (`e = 1`), `(2 p^(-31/32))^e` (`e ≥ 2`) for `p ≥ N0`.
--   * `tsum_fW_small` (`≤ C0`), `tsum_fW_large` (`≤ exp(10 p^(-35/32))`, needs `16 ≤ N0 ≤ p`).
--   * **`summable_fW`**, **`tsum_fW_le`**: `Σ_N fp (fW N0) N ≤ CW N0`;
--     **`summable_fW_int`**, **`tsum_fW_int_le`**: `Σ'_{c ∈ ℤ} fp (fW N0) |c| ≤ 2 CW N0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K3

/-!
# S3-ES-Wt2 (O6, file K4a): the Euler product for the `c`-sum majorant

* `sum_range_fp_le`, `summable_fp`, `tsum_fp_le`: a generic Euler-product bound for `fp f`
  (`f p 0 = 1`, `f ≥ 0`, per-prime sums bounded by `K` in every finite product).
* `fW N0 p e`: `(p^(-7/32))^e` for `p < N0`; `2 p^(-35/32)` (`e = 1`), `(2 p^(-31/32))^e` (`e ≥ 2`) for `p ≥ N0`.
* `tsum_fW_small` (`≤ C0`), `tsum_fW_large` (`≤ exp(10 p^(-35/32))`, needs `16 ≤ N0 ≤ p`).
* **`summable_fW`**, **`tsum_fW_le`**: `Σ_N fp (fW N0) N ≤ CW N0`;
  **`summable_fW_int`**, **`tsum_fW_int_le`**: `Σ'_{c ∈ ℤ} fp (fW N0) |c| ≤ 2 CW N0`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-! ### A generic Euler-product bound -/

section Generic

variable {f : ℕ → ℕ → ℝ}

lemma fp_nonneg_of (hf0 : ∀ p e, 0 ≤ f p e) (i : ℕ) : 0 ≤ KL.fp f i :=
  Finset.prod_nonneg (fun _ _ => hf0 _ _)

lemma fp_pp_of (hf1 : ∀ p, f p 0 = 1) {p : ℕ} (hp : p.Prime) (e : ℕ) : KL.fp f (p ^ e) = f p e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, KL.fp_one, hf1]
  · exact KL.fp_prime_pow f hp he.ne'

theorem sum_range_fp_le (hf0 : ∀ p e, 0 ≤ f p e) (hf1 : ∀ p, f p 0 = 1)
    (hs : ∀ p, p.Prime → Summable (fun e => f p e)) {K : ℝ}
    (hK : ∀ s : Finset ℕ, ∏ p ∈ s with p.Prime, ∑' e, f p e ≤ K) (n : ℕ) :
    ∑ i ∈ range n, KL.fp f i ≤ 1 + K := by
  have hsn : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖KL.fp f (p ^ e)‖) := by
    intro p hp
    exact ((hs p hp).congr (fun e => (fp_pp_of hf1 hp e).symm)).congr
      (fun e => (Real.norm_of_nonneg (fp_nonneg_of hf0 _)).symm)
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := KL.fp f) (KL.fp_one f) (fun hc => KL.fp_mul f hc) (fun hp => hsn hp) (range n)
  have hS' : HasSum (Set.indicator (Nat.factoredNumbers (range n)) (KL.fp f))
      (∏ p ∈ range n with p.Prime, ∑' e, KL.fp f (p ^ e)) :=
    hasSum_subtype_iff_indicator.mp hS
  have hle : ∑ i ∈ range n, Set.indicator (Nat.factoredNumbers (range n)) (KL.fp f) i ≤
      ∏ p ∈ range n with p.Prime, ∑' e, KL.fp f (p ^ e) :=
    sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => fp_nonneg_of hf0 j) i) hS'
  have hprod : ∏ p ∈ range n with p.Prime, ∑' e, KL.fp f (p ^ e) =
      ∏ p ∈ range n with p.Prime, ∑' e, f p e := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    exact tsum_congr (fun e => fp_pp_of hf1 (Finset.mem_filter.1 hp).2 e)
  have hpt : ∀ i ∈ range n, KL.fp f i ≤
      (if i = 0 then 1 else 0) + Set.indicator (Nat.factoredNumbers (range n)) (KL.fp f) i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have := Set.indicator_nonneg (fun j _ => fp_nonneg_of hf0 j) 0
        (s := Nat.factoredNumbers (range n))
      rw [if_pos rfl, KL.fp_zero]
      linarith
    · have hmem : i ∈ Nat.factoredNumbers (range n) := by
        rw [Nat.mem_factoredNumbers']
        intro p _ hpi
        exact Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_of_dvd hi0 hpi) (Finset.mem_range.1 hi))
      simp only [if_neg hi0.ne', zero_add, Set.indicator_of_mem hmem, le_refl]
  have hfirst : ∑ i ∈ range n, (if i = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  calc ∑ i ∈ range n, KL.fp f i
      ≤ ∑ i ∈ range n, ((if i = 0 then (1 : ℝ) else 0) +
          Set.indicator (Nat.factoredNumbers (range n)) (KL.fp f) i) := Finset.sum_le_sum hpt
    _ = (∑ i ∈ range n, (if i = 0 then (1 : ℝ) else 0)) +
          ∑ i ∈ range n, Set.indicator (Nat.factoredNumbers (range n)) (KL.fp f) i :=
        Finset.sum_add_distrib
    _ ≤ 1 + K := add_le_add hfirst (hle.trans (hprod.trans_le (hK (range n))))

theorem summable_fp (hf0 : ∀ p e, 0 ≤ f p e) (hf1 : ∀ p, f p 0 = 1)
    (hs : ∀ p, p.Prime → Summable (fun e => f p e)) {K : ℝ}
    (hK : ∀ s : Finset ℕ, ∏ p ∈ s with p.Prime, ∑' e, f p e ≤ K) : Summable (KL.fp f) :=
  summable_of_sum_range_le (fp_nonneg_of hf0) (sum_range_fp_le hf0 hf1 hs hK)

theorem tsum_fp_le (hf0 : ∀ p e, 0 ≤ f p e) (hf1 : ∀ p, f p 0 = 1)
    (hs : ∀ p, p.Prime → Summable (fun e => f p e)) {K : ℝ}
    (hK : ∀ s : Finset ℕ, ∏ p ∈ s with p.Prime, ∑' e, f p e ≤ K) : ∑' i, KL.fp f i ≤ 1 + K :=
  Real.tsum_le_of_sum_range_le (fp_nonneg_of hf0) (sum_range_fp_le hf0 hf1 hs hK)

end Generic

/-! ### The majorant `fW` -/

/-- Local factor of the `c`-sum majorant. -/
def fW (N0 p e : ℕ) : ℝ :=
  if e = 0 then 1 else if p < N0 then ((p : ℝ) ^ (-(7 / 32 : ℝ))) ^ e
  else if e = 1 then 2 * (p : ℝ) ^ (-(35 / 32 : ℝ)) else (2 * (p : ℝ) ^ (-(31 / 32 : ℝ))) ^ e

lemma fW_nonneg (N0 p e : ℕ) : 0 ≤ fW N0 p e := by unfold fW; split_ifs <;> positivity

lemma fW_zero (N0 p : ℕ) : fW N0 p 0 = 1 := by simp [fW]

/-- `(1 - 2^(-7/32))⁻¹`. -/
def C0 : ℝ := (1 - (2 : ℝ) ^ (-(7 / 32 : ℝ)))⁻¹

lemma r0_lt_one : (2 : ℝ) ^ (-(7 / 32 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma one_le_C0 : 1 ≤ C0 := by
  unfold C0
  have h0 : 0 ≤ (2 : ℝ) ^ (-(7 / 32 : ℝ)) := by positivity
  have h1 := r0_lt_one
  rw [one_le_inv₀ (by linarith)]
  linarith

lemma tsum_fW_small {N0 p : ℕ} (hp : p.Prime) (hpN : p < N0) :
    Summable (fun e => fW N0 p e) ∧ ∑' e, fW N0 p e ≤ C0 := by
  set r : ℝ := (p : ℝ) ^ (-(7 / 32 : ℝ)) with hr
  have hfr : ∀ e, fW N0 p e = r ^ e := by
    intro e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [fW]
    · simp only [fW, if_neg he.ne', if_pos hpN, hr]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hrr : r ≤ (2 : ℝ) ^ (-(7 / 32 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)
  have h20 := r0_lt_one
  refine ⟨(summable_geometric_of_lt_one hr0 hr1).congr (fun e => (hfr e).symm), ?_⟩
  rw [tsum_congr hfr, tsum_geometric_of_lt_one hr0 hr1]
  exact inv_anti₀ (by linarith) (by linarith)

/-- `10 p^(-35/32)`. -/
def xW (p : ℕ) : ℝ := 10 * (p : ℝ) ^ (-(35 / 32 : ℝ))

lemma xW_nonneg (p : ℕ) : 0 ≤ xW p := by unfold xW; positivity

lemma summable_xW : Summable xW :=
  (Real.summable_nat_rpow.2 (by norm_num : (-(35 / 32 : ℝ)) < -1)).mul_left 10

lemma tsum_fW_large {N0 p : ℕ} (h16 : 16 ≤ N0) (hp : p.Prime) (hpN : ¬ p < N0) :
    Summable (fun e => fW N0 p e) ∧ ∑' e, fW N0 p e ≤ Real.exp (xW p) := by
  have hp16 : (16 : ℝ) ≤ p := by exact_mod_cast (show 16 ≤ p by omega)
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set ρ : ℝ := 2 * (p : ℝ) ^ (-(31 / 32 : ℝ)) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hsq : ((p : ℝ) ^ (-(31 / 32 : ℝ))) ^ 2 = (p : ℝ) ^ (-(31 / 16 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
  have hsq1 : (p : ℝ) ^ (-(31 / 16 : ℝ)) ≤ (p : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hsq2 : (p : ℝ) ^ (-(31 / 16 : ℝ)) ≤ (p : ℝ) ^ (-(35 / 32 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hpinv : (p : ℝ)⁻¹ ≤ 1 / 16 := by
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp16
  have hρsq : ρ ^ 2 = 4 * (p : ℝ) ^ (-(31 / 16 : ℝ)) := by rw [hρ, mul_pow, hsq]; norm_num
  have hρ2 : ρ ≤ 1 / 2 := by nlinarith
  have hρ1 : ρ < 1 := by linarith
  have h2 : ∀ e : ℕ, fW N0 p (e + 1 + 1) = ρ ^ 2 * ρ ^ e := by
    intro e
    rw [fW, if_neg (by omega), if_neg hpN, if_neg (by omega), ← hρ, ← pow_add]
    congr 1; omega
  have hs2 : Summable (fun e => fW N0 p (e + 1 + 1)) :=
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (ρ ^ 2)).congr (fun e => (h2 e).symm)
  have hs : Summable (fun e => fW N0 p e) := (summable_nat_add_iff 1).1 ((summable_nat_add_iff 1).1 hs2)
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hs).tsum_eq_zero_add, tsum_congr h2,
    tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
  have h0 : fW N0 p 0 = 1 := fW_zero N0 p
  have h1 : fW N0 p (0 + 1) = 2 * (p : ℝ) ^ (-(35 / 32 : ℝ)) := by
    rw [zero_add, fW, if_neg one_ne_zero, if_neg hpN, if_pos rfl]
  rw [h0, h1]
  have hinv : (1 - ρ)⁻¹ ≤ 2 := by
    calc (1 - ρ)⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have htail : ρ ^ 2 * (1 - ρ)⁻¹ ≤ 8 * (p : ℝ) ^ (-(35 / 32 : ℝ)) := by
    have hq0 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    calc ρ ^ 2 * (1 - ρ)⁻¹ ≤ ρ ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv hq0
      _ ≤ 8 * (p : ℝ) ^ (-(35 / 32 : ℝ)) := by rw [hρsq]; linarith
  have hexp := Real.add_one_le_exp (xW p)
  unfold xW at hexp ⊢
  linarith

/-- Per-prime factor of the product bound. -/
def aW (N0 p : ℕ) : ℝ := if p < N0 then C0 else 1

lemma tsum_fW_le {N0 p : ℕ} (h16 : 16 ≤ N0) (hp : p.Prime) :
    Summable (fun e => fW N0 p e) ∧ ∑' e, fW N0 p e ≤ aW N0 p * Real.exp (xW p) := by
  have hE : 1 ≤ Real.exp (xW p) := Real.one_le_exp (xW_nonneg p)
  by_cases hpN : p < N0
  · obtain ⟨hs, ht⟩ := tsum_fW_small (N0 := N0) hp hpN
    refine ⟨hs, ?_⟩
    rw [aW, if_pos hpN]
    have := one_le_C0
    nlinarith
  · obtain ⟨hs, ht⟩ := tsum_fW_large h16 hp hpN
    refine ⟨hs, ?_⟩
    rw [aW, if_neg hpN, one_mul]
    exact ht

lemma prod_aW_le (N0 : ℕ) (s : Finset ℕ) : ∏ p ∈ s with p.Prime, aW N0 p ≤ C0 ^ N0 := by
  unfold aW
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  refine pow_le_pow_right₀ one_le_C0 ?_
  calc _ ≤ (Finset.range N0).card :=
        Finset.card_le_card (fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2)
    _ = N0 := Finset.card_range N0

lemma prod_fW_le {N0 : ℕ} (h16 : 16 ≤ N0) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, ∑' e, fW N0 p e ≤ C0 ^ N0 * Real.exp (∑' n, xW n) := by
  have hC0 := one_le_C0
  calc ∏ p ∈ s with p.Prime, ∑' e, fW N0 p e
      ≤ ∏ p ∈ s with p.Prime, (aW N0 p * Real.exp (xW p)) :=
        Finset.prod_le_prod (fun p _ => tsum_nonneg (fun e => fW_nonneg N0 p e))
          (fun p hp => (tsum_fW_le h16 (Finset.mem_filter.1 hp).2).2)
    _ = (∏ p ∈ s with p.Prime, aW N0 p) * ∏ p ∈ s with p.Prime, Real.exp (xW p) :=
        Finset.prod_mul_distrib
    _ ≤ C0 ^ N0 * Real.exp (∑' n, xW n) := by
        have hE : ∏ p ∈ s with p.Prime, Real.exp (xW p) ≤ Real.exp (∑' n, xW n) := by
          rw [← Real.exp_sum]
          exact Real.exp_le_exp.2 (Summable.sum_le_tsum _ (fun i _ => xW_nonneg i) summable_xW)
        have hA0 : 0 ≤ ∏ p ∈ s with p.Prime, aW N0 p :=
          Finset.prod_nonneg (fun p _ => by unfold aW; split_ifs <;> linarith)
        have hE0 : 0 ≤ ∏ p ∈ s with p.Prime, Real.exp (xW p) :=
          Finset.prod_nonneg (fun p _ => (Real.exp_pos _).le)
        exact mul_le_mul (prod_aW_le N0 s) hE hE0 (by positivity)

/-- The constant of the `c`-sum. -/
def CW (N0 : ℕ) : ℝ := 1 + C0 ^ N0 * Real.exp (∑' n, xW n)

theorem summable_fW {N0 : ℕ} (h16 : 16 ≤ N0) : Summable (KL.fp (fW N0)) :=
  summable_fp (fW_nonneg N0) (fW_zero N0) (fun p hp => (tsum_fW_le h16 hp).1) (prod_fW_le h16)

theorem tsum_fW_le' {N0 : ℕ} (h16 : 16 ≤ N0) : ∑' i, KL.fp (fW N0) i ≤ CW N0 :=
  tsum_fp_le (fW_nonneg N0) (fW_zero N0) (fun p hp => (tsum_fW_le h16 hp).1) (prod_fW_le h16)

lemma fp_fW_nonneg (N0 i : ℕ) : 0 ≤ KL.fp (fW N0) i := fp_nonneg_of (fW_nonneg N0) i

theorem summable_fW_int {N0 : ℕ} (h16 : 16 ≤ N0) :
    Summable (fun c : ℤ => KL.fp (fW N0) c.natAbs) := by
  have hN := summable_fW h16
  refine Summable.of_nat_of_neg_add_one (f := fun c : ℤ => KL.fp (fW N0) c.natAbs) ?_ ?_
  · exact hN.congr (fun n => by simp)
  · exact ((summable_nat_add_iff 1).2 hN).congr (fun n => by
      simp only [Int.natAbs_neg]; congr 1)

theorem tsum_fW_int_le {N0 : ℕ} (h16 : 16 ≤ N0) :
    ∑' c : ℤ, KL.fp (fW N0) c.natAbs ≤ 2 * CW N0 := by
  have hN := summable_fW h16
  have hN1 := (summable_nat_add_iff 1).2 hN
  have e1 : (fun n : ℕ => KL.fp (fW N0) ((n : ℤ)).natAbs) = KL.fp (fW N0) := by
    funext n; simp
  have e2 : (fun n : ℕ => KL.fp (fW N0) ((-((n : ℤ) + 1))).natAbs) =
      fun n : ℕ => KL.fp (fW N0) (n + 1) := by
    funext n; simp only [Int.natAbs_neg]; congr 1
  rw [tsum_of_nat_of_neg_add_one (f := fun c : ℤ => KL.fp (fW N0) c.natAbs)
    (by rw [e1]; exact hN) (by rw [e2]; exact hN1), e1, e2]
  have h1 : ∑' n : ℕ, KL.fp (fW N0) (n + 1) ≤ ∑' n : ℕ, KL.fp (fW N0) n := by
    rw [hN.tsum_eq_zero_add]
    linarith [fp_fW_nonneg N0 0]
  have h2 := tsum_fW_le' h16
  linarith

end RamanujanPetersson.EllW2


