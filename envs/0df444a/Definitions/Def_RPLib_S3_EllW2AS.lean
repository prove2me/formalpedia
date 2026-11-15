-- Prove2me | Definitions.Def_RPLib_S3_EllW2AS
-- name    : RPLib_S3_EllW2AS
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:27:06.168343+00:00
-- url     : https://prove2.me/theorems/3887659c-e937-4585-b7f8-1e900dd63f8f
-- title:
--   The Eichler-Selberg trace formula in weight two: Abel summation against periodic weights
-- statement:
--   Abel summation against periodic weights.
--
--   Generic tools for the zero-mode main terms `Σ_t W_c(t) Φ(t)`:
--   * `periodic_emod`, `psum` (partial sums of `f - μ`), `psum_succ`, `norm_psum_le`.
--   * **`norm_tsum_sub_mean_le`**: `‖Σ'_t (f t - μ) Φ t‖ ≤ B · Σ'_t ‖Φ (t+1) - Φ t‖` for `q`-periodic `f` with mean `μ`
--     and partial sums of `f - μ` bounded by `B`.
--   * **`norm_tsum_sub_integral_le`**: `‖Σ'_t Φ t - ∫ Φ‖ ≤ ∫ ‖Φ'‖`.
--   * `summable_diff`, `tsum_diff_le`: `Σ'_t ‖Φ (t+1) - Φ t‖ ≤ ∫ ‖Φ'‖`.
--   * **`norm_tsum_periodic_sub_le`**: `‖Σ'_t f t Φ t - μ ∫ Φ‖ ≤ (‖μ‖ + B) ∫ ‖Φ'‖`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib

/-!
# S3-ES-Wt2 (O6, file AS): Abel summation against periodic weights

Generic tools for the zero-mode main terms `Σ_t W_c(t) Φ(t)`:
* `periodic_emod`, `psum` (partial sums of `f - μ`), `psum_succ`, `norm_psum_le`.
* **`norm_tsum_sub_mean_le`**: `‖Σ'_t (f t - μ) Φ t‖ ≤ B · Σ'_t ‖Φ (t+1) - Φ t‖` for `q`-periodic `f` with mean `μ`
  and partial sums of `f - μ` bounded by `B`.
* **`norm_tsum_sub_integral_le`**: `‖Σ'_t Φ t - ∫ Φ‖ ≤ ∫ ‖Φ'‖`.
* `summable_diff`, `tsum_diff_le`: `Σ'_t ‖Φ (t+1) - Φ t‖ ≤ ∫ ‖Φ'‖`.
* **`norm_tsum_periodic_sub_le`**: `‖Σ'_t f t Φ t - μ ∫ Φ‖ ≤ (‖μ‖ + B) ∫ ‖Φ'‖`.
-/

open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

lemma periodic_emod {f : ℤ → ℂ} {q : ℤ} (hf : ∀ t, f (t + q) = f t) (t : ℤ) : f t = f (t % q) := by
  have key : ∀ (r k : ℤ), f (r + q * k) = f r := by
    intro r k
    refine Int.induction_on k (by simp) (fun i ih => ?_) (fun i ih => ?_)
    · rw [show r + q * ((i : ℤ) + 1) = (r + q * i) + q by ring, hf, ih]
    · have := hf (r + q * (-(i : ℤ) - 1))
      rw [show r + q * (-(i : ℤ) - 1) + q = r + q * (-(i : ℤ)) by ring, ih] at this
      exact this.symm
  have := key (t % q) (t / q)
  rwa [add_comm, Int.mul_ediv_add_emod] at this

/-- `S(t) = Σ_{0 ≤ u < t mod q} (f u - μ)`. -/
def psum (f : ℤ → ℂ) (μ : ℂ) (q : ℕ) (t : ℤ) : ℂ :=
  ∑ u ∈ Finset.range (t % (q : ℤ)).toNat, (f u - μ)

lemma psum_succ {f : ℤ → ℂ} {μ : ℂ} {q : ℕ} (hq : 0 < q) (hf : ∀ t, f (t + q) = f t)
    (hμ : ∑ u ∈ Finset.range q, f u = q * μ) (t : ℤ) :
    psum f μ q (t + 1) - psum f μ q t = f t - μ := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set r := t % (q : ℤ) with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hq'.ne'
  have hrq : r < q := Int.emod_lt_of_pos _ hq'
  have ht : t = r + q * (t / q) := by rw [hr, add_comm, Int.mul_ediv_add_emod]
  have hft : f t = f r := periodic_emod hf t
  unfold psum
  rw [← hr]
  have hrn : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
  by_cases hlt : r + 1 < q
  · have h1 : (t + 1) % (q : ℤ) = r + 1 := by
      rw [ht, show r + q * (t / q) + 1 = (r + 1) + q * (t / q) by ring, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) hlt
    rw [h1, show (r + 1).toNat = r.toNat + 1 by omega, Finset.sum_range_succ, hrn, hft]
    ring
  · have hq1 : r + 1 = q := by omega
    have h1 : (t + 1) % (q : ℤ) = 0 := by
      rw [ht, show r + q * (t / q) + 1 = 0 + q * (t / q + 1) by rw [← hq1]; ring,
        Int.add_mul_emod_self_left]
      simp
    rw [h1]
    have hsum : ∑ u ∈ Finset.range q, (f u - μ) = 0 := by
      rw [Finset.sum_sub_distrib, hμ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have hqn : q = r.toNat + 1 := by omega
    rw [hqn, Finset.sum_range_succ, hrn] at hsum
    rw [hft]
    simp only [Int.toNat_zero, Finset.range_zero, Finset.sum_empty, zero_sub]
    linear_combination (-1 : ℂ) * hsum

lemma norm_psum_le {f : ℤ → ℂ} {μ : ℂ} {q : ℕ} (hq : 0 < q) {B : ℝ}
    (hB : ∀ m : ℕ, m ≤ q → ‖∑ u ∈ Finset.range m, (f u - μ)‖ ≤ B) (t : ℤ) :
    ‖psum f μ q t‖ ≤ B := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have h1 := Int.emod_lt_of_pos t hq'
  have h0 := Int.emod_nonneg t hq'.ne'
  exact hB _ (by omega)

/-- **Abel summation against a periodic weight.** -/
theorem norm_tsum_sub_mean_le {f : ℤ → ℂ} {μ : ℂ} {q : ℕ} (hq : 0 < q) (hf : ∀ t, f (t + q) = f t)
    (hμ : ∑ u ∈ Finset.range q, f u = q * μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m : ℕ, m ≤ q → ‖∑ u ∈ Finset.range m, (f u - μ)‖ ≤ B)
    {Φ : ℤ → ℂ} (hΦ : Summable Φ) (hd : Summable fun t => ‖Φ (t + 1) - Φ t‖) :
    ‖∑' t, (f t - μ) * Φ t‖ ≤ B * ∑' t, ‖Φ (t + 1) - Φ t‖ := by
  set S := psum f μ q with hS
  have hSb : ∀ t, ‖S t‖ ≤ B := norm_psum_le hq hB
  have hΦ1 : Summable fun t : ℤ => Φ (t - 1) := hΦ.comp_injective (sub_left_injective)
  have hs1 : Summable fun t => S t * Φ t :=
    Summable.of_norm_bounded (hΦ.norm.mul_left B) fun t => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hSb t) (norm_nonneg _)
  have hs2 : Summable fun t => S t * Φ (t - 1) :=
    Summable.of_norm_bounded (hΦ1.norm.mul_left B) fun t => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hSb t) (norm_nonneg _)
  have e1 : ∑' t, (f t - μ) * Φ t = ∑' t, (S (t + 1) * Φ t - S t * Φ t) := by
    refine tsum_congr fun t => ?_
    rw [← psum_succ hq hf hμ t, sub_mul]
  have hs3 : Summable fun t => S (t + 1) * Φ t := by
    have := (Equiv.addRight (1 : ℤ)).summable_iff.2 hs2
    refine this.congr fun t => ?_
    simp
  have e2 : ∑' t, S (t + 1) * Φ t = ∑' t, S t * Φ (t - 1) := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun t => S t * Φ (t - 1))]
    refine tsum_congr fun t => ?_
    simp
  rw [e1, hs3.tsum_sub hs1, e2, ← hs2.tsum_sub hs1]
  have hg : HasSum (fun t : ℤ => B * ‖Φ (t - 1) - Φ t‖) (B * ∑' t, ‖Φ (t + 1) - Φ t‖) := by
    have h := (Equiv.subRight (1 : ℤ)).hasSum_iff.2 (hd.hasSum.mul_left B)
    refine h.congr_fun fun t => ?_
    simp [norm_sub_rev]
  refine tsum_of_norm_bounded hg fun t => ?_
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right (hSb t) (norm_nonneg _)

/-! ## Riemann sums against the integral -/

lemma norm_sub_le_intervalIntegral {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x)
    (hΦ' : Integrable Φ') {t x : ℝ} (htx : t ≤ x) (hx : x ≤ t + 1) :
    ‖Φ x - Φ t‖ ≤ ∫ u in t..t + 1, ‖Φ' u‖ := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hΦ'.intervalIntegrable)]
  refine (intervalIntegral.norm_integral_le_integral_norm htx).trans ?_
  exact intervalIntegral.integral_mono_interval le_rfl htx hx
    (Eventually.of_forall fun _ => norm_nonneg _) hΦ'.norm.intervalIntegrable

lemma hasSum_unit_norm {Φ' : ℝ → ℂ} (hΦ' : Integrable Φ') :
    HasSum (fun t : ℤ => ∫ u in (t : ℝ)..(t : ℝ) + 1, ‖Φ' u‖) (∫ u, ‖Φ' u‖) := by
  have h := hΦ'.norm.hasSum_intervalIntegral 0
  simpa only [zero_add] using h

/-- **Riemann sum against the integral.** -/
theorem norm_tsum_sub_integral_le {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x)
    (hΦ' : Integrable Φ') (hΦ : Integrable Φ) (hs : Summable fun t : ℤ => Φ t) :
    ‖∑' t : ℤ, Φ t - ∫ x, Φ x‖ ≤ ∫ x, ‖Φ' x‖ := by
  have hI := hΦ.hasSum_intervalIntegral 0
  simp only [zero_add] at hI
  have h2 := hs.hasSum.sub hI
  rw [← h2.tsum_eq]
  refine tsum_of_norm_bounded (hasSum_unit_norm hΦ') fun t => ?_
  show ‖Φ t - ∫ x in (t : ℝ)..(t : ℝ) + 1, Φ x‖ ≤ _
  have hc : IntervalIntegrable Φ volume (t : ℝ) ((t : ℝ) + 1) := hΦ.intervalIntegrable
  have e : Φ t - ∫ x in (t : ℝ)..(t : ℝ) + 1, Φ x = ∫ x in (t : ℝ)..(t : ℝ) + 1, (Φ t - Φ x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hc, intervalIntegral.integral_const]
    simp
  rw [e]
  have hb : ∀ x ∈ Set.uIoc (t : ℝ) ((t : ℝ) + 1), ‖Φ t - Φ x‖ ≤ ∫ u in (t : ℝ)..(t : ℝ) + 1, ‖Φ' u‖ := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    rw [norm_sub_rev]
    exact norm_sub_le_intervalIntegral hd hΦ' hx.1.le hx.2
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  simp

lemma norm_diff_le {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : Integrable Φ') (t : ℤ) :
    ‖Φ ((t + 1 : ℤ) : ℝ) - Φ t‖ ≤ ∫ u in (t : ℝ)..(t : ℝ) + 1, ‖Φ' u‖ := by
  push_cast
  exact norm_sub_le_intervalIntegral hd hΦ' (by linarith) le_rfl

lemma summable_diff {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : Integrable Φ') :
    Summable fun t : ℤ => ‖Φ ((t + 1 : ℤ) : ℝ) - Φ t‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_diff_le hd hΦ')
    (hasSum_unit_norm hΦ').summable

lemma tsum_diff_le {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : Integrable Φ') :
    ∑' t : ℤ, ‖Φ ((t + 1 : ℤ) : ℝ) - Φ t‖ ≤ ∫ u, ‖Φ' u‖ :=
  hasSum_le (norm_diff_le hd hΦ') (summable_diff hd hΦ').hasSum (hasSum_unit_norm hΦ')

/-- **Periodic weights against a smooth profile**: `Σ_t f(t) Φ(t) = μ ∫ Φ + O((‖μ‖ + B) ∫ ‖Φ'‖)`. -/
theorem norm_tsum_periodic_sub_le {f : ℤ → ℂ} {μ : ℂ} {q : ℕ} (hq : 0 < q)
    (hf : ∀ t, f (t + q) = f t) (hμ : ∑ u ∈ Finset.range q, f u = q * μ) {B F : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m : ℕ, m ≤ q → ‖∑ u ∈ Finset.range m, (f u - μ)‖ ≤ B) (hfb : ∀ t, ‖f t‖ ≤ F)
    {Φ Φ' : ℝ → ℂ} (hd : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ' : Integrable Φ') (hΦ : Integrable Φ)
    (hs : Summable fun t : ℤ => Φ t) :
    ‖∑' t : ℤ, f t * Φ t - μ * ∫ x, Φ x‖ ≤ (‖μ‖ + B) * ∫ x, ‖Φ' x‖ := by
  have hsf : Summable fun t : ℤ => f t * Φ t :=
    Summable.of_norm_bounded (hs.norm.mul_left F) fun t => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hfb t) (norm_nonneg _)
  have hsm : Summable fun t : ℤ => μ * Φ t := hs.mul_left μ
  have e : ∑' t : ℤ, f t * Φ t - μ * ∫ x, Φ x =
      ∑' t : ℤ, (f t - μ) * Φ t + μ * (∑' t : ℤ, Φ t - ∫ x, Φ x) := by
    have : ∑' t : ℤ, (f t - μ) * Φ t = ∑' t : ℤ, f t * Φ t - ∑' t : ℤ, μ * Φ t := by
      rw [← hsf.tsum_sub hsm]; exact tsum_congr fun t => by ring
    rw [this, tsum_mul_left]; ring
  rw [e]
  have hdΦ : Summable fun t : ℤ => ‖(fun t : ℤ => Φ t) (t + 1) - (fun t : ℤ => Φ t) t‖ :=
    summable_diff hd hΦ'
  have h1 := norm_tsum_sub_mean_le hq hf hμ hB0 hB hs hdΦ
  have h2 : ∑' t : ℤ, ‖(fun t : ℤ => Φ t) (t + 1) - (fun t : ℤ => Φ t) t‖ ≤ ∫ x, ‖Φ' x‖ :=
    tsum_diff_le hd hΦ'
  have h3 := norm_tsum_sub_integral_le hd hΦ' hΦ hs
  have h4 : ‖∑' t : ℤ, (f t - μ) * Φ t‖ ≤ B * ∫ x, ‖Φ' x‖ :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
  have h5 : ‖μ * (∑' t : ℤ, Φ t - ∫ x, Φ x)‖ ≤ ‖μ‖ * ∫ x, ‖Φ' x‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  exact (norm_add_le _ _).trans ((add_le_add h4 h5).trans (le_of_eq (by ring)))

end RamanujanPetersson.EllW2


