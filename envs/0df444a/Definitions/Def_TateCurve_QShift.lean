-- Prove2me | Definitions.Def_TateCurve_QShift
-- name    : TateCurve_QShift
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/847b532e-779b-57e5-96d1-51f6b9d8b5b9
-- title:
--   q-shift coefficients and descent for Tate-curve defect series
-- statement:
--   Throughout, $K$ is a nontrivially normed, ultrametric, complete field. For $u \in K$ and $M \in \mathbb{N}$ three coefficient functions are defined from the integers `lineCoeff`: `qshiftAlpha` is the finite sum of $(\mathrm{lineCoeff}\,p_1\,p_2)\,u^{p_2}$ over the pairs $(p_1,p_2)$ with $p_1+p_2=M$ and $1 \le p_2 \le p_1$; `qshiftBeta` is the infinite sum $\sum_{k \ge 1} (\mathrm{lineCoeff}\,(M+k)\,k)\,u^{-k}$ (written with an indicator on $k \ge 1$); `qshiftGamma` is $\sum_{k=1}^{M} -2\,(\mathrm{lineCoeff}\,M\,k)$. Accompanying estimates, valid for $\|u\| > 1$, give summability of the $\beta$-series together with $\|\beta_M\| \le 1$, $\|\alpha_M\| \le (M+1)\|u\|^M$ and $\|\gamma_M\| \le 2(M+1)$; they rest on the ultrametric bound $\|n\| \le 1$ for integer casts.
--
--   Four families of terms indexed by $\mathbb{N} \times \mathbb{N}$ are defined, all supported on $1 \le p_2 \le p_1$: `hubTerm` is $(\mathrm{lineCoeff}\,p_1\,p_2)\,\mathrm{Fz}(qu)(p_2)\,q^{p_1}$, `alphaTerm` is $(\mathrm{lineCoeff}\,p_1\,p_2)\,u^{p_2}q^{p_1+p_2}$, `betaTerm` is $(\mathrm{lineCoeff}\,p_1\,p_2)\,u^{-p_2}q^{p_1-p_2}$ (truncated subtraction), and `gammaTerm` is $-2(\mathrm{lineCoeff}\,p_1\,p_2)\,q^{p_1}$, with `hubTerm_eq` expressing the hub family as the sum of the other three for $q,u \ne 0$. The reindexing map `shiftPair`, $(a,b) \mapsto (a+b,b)$, is injective with range the pairs satisfying $p_2 \le p_1$, and is used to prove summability on the region $\|u\|>1$, $\|q\|\,\|u\|<1$ and to regroup the double sums into $q$-expansions $\sum_M \alpha_M q^M$, $\sum_M \beta_M q^M$, $\sum_M \gamma_M q^M$ and $\sum_N 4\,\mathrm{defectCoeff}(qu)(N)\,q^N$.
--
--   Further results: uniqueness of coefficients of convergent $q$-series (`coeff_eq_of_forall_tsum_eq`, via the one-step lemma `coeff_eq_zero_step`); the nodal identity $y(w)^2+x(w)y(w)=x(w)^3$ for $w \ne 1$ with its consequence $\mathrm{defectCoeff}\,u\,0 = 0$; lattice lemmas showing $q^n u \ne 1$ for all $n \in \mathbb{Z}$ and that $qu$, $qu^{-1}$ lie in the unit ball; and, over a field of characteristic zero, the descent theorem `lineCoeff_eq_zero_of_qshift`: if $4\,\mathrm{defectCoeff}\,v\,M = \alpha_M(v)+\beta_M(v)+\gamma_M$ for every $v$ with $\|v\|>1$ and every $M$, then $\mathrm{lineCoeff}\,N\,k = 0$ whenever $1 \le k \le N$, the individual coefficients being extracted in `lineCoeff_eq_zero_of_diamond` by evaluating at $v = x^{t+1}$ and letting $t \to \infty$.
--
--   **Relation to Mathlib.** The $q$-shift coefficients, the term families and the defect coefficients are project notions; Mathlib supplies the analytic infrastructure used (`Summable`/`tsum`, geometric and Cauchy-product summability, `Finset.HasAntidiagonal.antidiagonal` with its sigma equivalence, and ultrametric facts such as norm bounds on integer and natural casts).
--
--   **Where it is used.** The vanishing of the line coefficients obtained here is what forces all defect coefficients of the Tate parametrisation series to vanish, i.e. that the series $x$- and $y$-coordinates satisfy the Weierstrass equation of the Tate curve over a complete ultrametric field. That uniformisation is used in the local analysis of the Frey curve in the proof of Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_QShift.lean

import Mathlib
import Definitions.Def_TateCurve_DefectLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

section SeriesSummability

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

theorem norm_mul_growthBound_lt_one (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1)
    (hqu' : ‖q * u⁻¹‖₊ < 1) : ‖q‖ * growthBound u < 1 := by
  have h1 : ‖q‖ * ‖u‖ < 1 := by
    have h : ‖q * u‖ < 1 := hqu
    rwa [norm_mul] at h
  have h2 : ‖q‖ * ‖u⁻¹‖ < 1 := by
    have h : ‖q * u⁻¹‖ < 1 := hqu'
    rwa [norm_mul] at h
  have h3 : ‖q‖ < 1 := hq
  rw [growthBound, mul_max_of_nonneg _ _ (norm_nonneg q),
    mul_max_of_nonneg _ _ (norm_nonneg q), mul_one]
  exact max_lt (max_lt h1 h2) h3

theorem summable_norm_a₄Series (hq : ‖q‖₊ < 1) :
    Summable fun N => ‖a₄Coeff (K := K) N * q ^ N‖ := by
  refine summable_norm_qSeries (B := 1) (C := 1) zero_le_one (fun N => ?_)
    (by rw [mul_one]; exact_mod_cast hq)
  rw [one_mul, one_pow]
  exact norm_a₄Coeff_le N

theorem summable_norm_a₆Series (hq : ‖q‖₊ < 1) :
    Summable fun N => ‖a₆Coeff (K := K) N * q ^ N‖ := by
  refine summable_norm_qSeries (B := 1) (C := 1) zero_le_one (fun N => ?_)
    (by rw [mul_one]; exact_mod_cast hq)
  rw [one_mul, one_pow]
  exact norm_a₆Coeff_le N

theorem summable_norm_xSeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖xCoeffFull u N * q ^ N‖ :=
  summable_norm_qSeries (growthBound_nonneg u) (norm_xCoeffFull_le u)
    (norm_mul_growthBound_lt_one hq hqu hqu')

theorem summable_norm_ySeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖yCoeffFull u N * q ^ N‖ :=
  summable_norm_qSeries (growthBound_nonneg u) (norm_yCoeffFull_le u)
    (norm_mul_growthBound_lt_one hq hqu hqu')

theorem nodal_xfun_yfun' {w : K} (hw : w ≠ 1) : yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by
  have h1w : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  simp only [xfun, yfun]
  field_simp
  ring

theorem defectCoeff_zero' (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by
  have hnodal := nodal_xfun_yfun' (K := K) (w := u) hu1
  simp only [defectCoeff, cauchyMul_zero, xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero,
    a₆Coeff_zero, zero_mul, add_zero]
  linear_combination hnodal

end SeriesSummability

end TateCurve

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Region

variable {q u : K}

lemma ne_zero_of_one_lt_norm (hu : 1 < ‖u‖) : u ≠ 0 := by
  intro h
  rw [h, norm_zero] at hu
  linarith

lemma ne_one_of_one_lt_norm (hu : 1 < ‖u‖) : u ≠ 1 := by
  intro h
  rw [h, norm_one] at hu
  linarith

lemma norm_q_lt_one_of_qshift (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) : ‖q‖ < 1 := by
  nlinarith [norm_nonneg q, norm_nonneg u]

lemma qshift_lattice_ne_one (hq0 : q ≠ 0) (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ∀ n : ℤ, q ^ n * u ≠ 1 := by
  intro n h1
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  have hq0' : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hnorm : ‖q ^ n * u‖ = ‖q‖ ^ n * ‖u‖ := by
    rw [norm_mul, norm_zpow]
  rcases (by omega : n ≤ 0 ∨ 0 < n) with hn | hn
  · have h2 : (1 : ℝ) ≤ ‖q‖ ^ n := one_le_zpow_of_nonpos₀ hq0' (le_of_lt hq1) hn
    have h3 : ‖u‖ ≤ ‖q‖ ^ n * ‖u‖ := le_mul_of_one_le_left (norm_nonneg u) h2
    have h4 : (1 : ℝ) < ‖q ^ n * u‖ := by rw [hnorm]; linarith
    rw [h1, norm_one] at h4
    linarith
  · have h2 : ‖q‖ ^ n ≤ ‖q‖ ^ (1 : ℤ) :=
      zpow_le_zpow_right_of_le_one₀ hq0' (le_of_lt hq1) hn
    have h3 : ‖q‖ ^ n * ‖u‖ ≤ ‖q‖ * ‖u‖ := by
      rw [zpow_one] at h2
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg u)
    have h4 : ‖q ^ n * u‖ < 1 := by rw [hnorm]; linarith
    rw [h1, norm_one] at h4
    linarith

lemma qshift_lattice_ne_one_shifted (hq0 : q ≠ 0) (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ∀ n : ℤ, q ^ n * (q * u) ≠ 1 := by
  intro n
  have h := qshift_lattice_ne_one hq0 hu hqu (n + 1)
  rwa [zpow_add₀ hq0, zpow_one, mul_assoc] at h

private lemma nnnorm_lt_one_of_norm_lt_one {x : K} (h : ‖x‖ < 1) : ‖x‖₊ < 1 := by
  exact_mod_cast h

lemma qshift_annulus_at_u (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ‖q * u‖₊ < 1 ∧ ‖q * u⁻¹‖₊ < 1 := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  constructor
  · refine nnnorm_lt_one_of_norm_lt_one ?_
    rw [norm_mul]; exact hqu
  · refine nnnorm_lt_one_of_norm_lt_one ?_
    rw [norm_mul, norm_inv]
    have h1 : ‖u‖⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; linarith
    nlinarith [norm_nonneg q, inv_nonneg.mpr (norm_nonneg u)]

lemma qshift_annulus_at_shifted (hq0 : q ≠ 0) (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ‖q * (q * u)‖₊ < 1 ∧ ‖q * (q * u)⁻¹‖₊ < 1 := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  constructor
  · refine nnnorm_lt_one_of_norm_lt_one ?_
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg q, norm_nonneg u]
  · refine nnnorm_lt_one_of_norm_lt_one ?_
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul, norm_inv]
    rw [inv_lt_one_iff₀]
    right; exact hu

end Region

section Coefficients

variable (u : K)

noncomputable def qshiftAlpha (M : ℕ) : K :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1),
    ((lineCoeff p.1 p.2 : ℤ) : K) * u ^ p.2

noncomputable def qshiftBeta (M : ℕ) : K :=
  ∑' k : ℕ, if 1 ≤ k then ((lineCoeff (M + k) k : ℤ) : K) * u⁻¹ ^ k else 0

noncomputable def qshiftGamma (M : ℕ) : K :=
  ∑ k ∈ Finset.Icc 1 M, (-2 : K) * ((lineCoeff M k : ℤ) : K)

variable {u}

lemma norm_inv_lt_one_of_one_lt_norm (hu : 1 < ‖u‖) : ‖u⁻¹‖ < 1 := by
  rw [norm_inv, inv_lt_one_iff₀]; right; exact hu

lemma norm_inv_le_one_of_one_lt_norm (hu : 1 < ‖u‖) : ‖u⁻¹‖ ≤ 1 :=
  le_of_lt (norm_inv_lt_one_of_one_lt_norm hu)

lemma summable_qshiftBeta_term (hu : 1 < ‖u‖) (M : ℕ) :
    Summable fun k : ℕ => if 1 ≤ k then ((lineCoeff (M + k) k : ℤ) : K) * u⁻¹ ^ k else 0 := by
  refine Summable.of_norm ?_
  have hgeom : Summable fun k : ℕ => ‖u⁻¹‖ ^ k :=
    summable_geometric_of_lt_one (norm_nonneg _) (norm_inv_lt_one_of_one_lt_norm hu)
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hgeom
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, norm_mul, norm_pow]
    have h1 : ‖((lineCoeff (M + k) k : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
    have h2 : (0 : ℝ) ≤ ‖u⁻¹‖ ^ k := pow_nonneg (norm_nonneg _) k
    nlinarith
  · rw [if_neg hk]
    simp only [norm_zero]
    exact pow_nonneg (norm_nonneg _) k

lemma norm_qshiftBeta_le_one (hu : 1 < ‖u‖) (M : ℕ) : ‖qshiftBeta u M‖ ≤ 1 := by
  refine norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, norm_mul, norm_pow]
    have h1 : ‖((lineCoeff (M + k) k : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
    have h2 : ‖u⁻¹‖ ^ k ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_inv_le_one_of_one_lt_norm hu)
    nlinarith [norm_nonneg ((lineCoeff (M + k) k : ℤ) : K), pow_nonneg (norm_nonneg u⁻¹) k]
  · rw [if_neg hk, norm_zero]
    exact zero_le_one

lemma norm_qshiftAlpha_le (hu : 1 < ‖u‖) (M : ℕ) :
    ‖qshiftAlpha u M‖ ≤ (M + 1 : ℝ) * ‖u‖ ^ M := by
  have hu1 : (1 : ℝ) ≤ ‖u‖ := le_of_lt hu
  calc ‖qshiftAlpha u M‖
      ≤ ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1),
          ‖((lineCoeff p.1 p.2 : ℤ) : K) * u ^ p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1), ‖u‖ ^ M := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [norm_mul, norm_pow]
        have h1 : ‖((lineCoeff p.1 p.2 : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
        have hpmem := Finset.mem_filter.mp hp
        have hple : p.2 ≤ M := by
          have := Finset.HasAntidiagonal.mem_antidiagonal.mp hpmem.1
          omega
        have h2 : ‖u‖ ^ p.2 ≤ ‖u‖ ^ M := pow_le_pow_right₀ hu1 hple
        have h3 : (0 : ℝ) ≤ ‖u‖ ^ p.2 := pow_nonneg (norm_nonneg _) _
        nlinarith
    _ ≤ (M + 1 : ℝ) * ‖u‖ ^ M := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1)).card
            ≤ M + 1 := by
          calc ((Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1)).card
              ≤ (Finset.HasAntidiagonal.antidiagonal M).card := Finset.card_filter_le _ _
            _ = M + 1 := Finset.Nat.card_antidiagonal M
        have hpow : (0 : ℝ) ≤ ‖u‖ ^ M := pow_nonneg (norm_nonneg _) _
        have hcard' : (((Finset.HasAntidiagonal.antidiagonal M).filter
            (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1)).card : ℝ) ≤ (M + 1 : ℝ) := by
          exact_mod_cast hcard
        nlinarith

lemma norm_qshiftGamma_le (M : ℕ) : ‖(qshiftGamma M : K)‖ ≤ 2 * (M + 1 : ℝ) := by
  calc ‖(qshiftGamma M : K)‖
      ≤ ∑ k ∈ Finset.Icc 1 M, ‖(-2 : K) * ((lineCoeff M k : ℤ) : K)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 M, 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_neg]
        have h1 : ‖((lineCoeff M k : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
        have h2 : ‖(2 : K)‖ ≤ 2 := by
          have h3 : ‖((2 : ℕ) : K)‖ ≤ 1 := norm_natCast_le_one K 2
          have h4 : ((2 : ℕ) : K) = (2 : K) := by norm_num
          rw [h4] at h3
          linarith
        nlinarith [norm_nonneg ((lineCoeff M k : ℤ) : K), norm_nonneg (2 : K)]
    _ ≤ 2 * (M + 1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.Icc 1 M).card ≤ M + 1 := by
          rw [Nat.card_Icc]
          omega
        have hcard' : ((Finset.Icc 1 M).card : ℝ) ≤ (M + 1 : ℝ) := by exact_mod_cast hcard
        nlinarith

end Coefficients

section Descent

variable [CharZero K]

private lemma lineCoeff_eq_zero_of_diamond {M k₀ : ℕ} (hk₀1 : 1 ≤ k₀) (hk₀M : k₀ ≤ M)
    (hdiamond : ∀ v : K, 1 < ‖v‖ →
      ∑ k ∈ Finset.Icc 1 M, ((lineCoeff M k : ℤ) : K) * (v ^ k + v⁻¹ ^ k) = qshiftBeta v M)
    (hbig : ∀ k', k₀ < k' → k' ≤ M → lineCoeff M k' = 0) :
    lineCoeff M k₀ = 0 := by

  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := ne_zero_of_one_lt_norm hx
  have hxinv : ‖x⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hx
  set v : ℕ → K := fun t => x ^ (t + 1) with hv
  have hv0 : ∀ t, v t ≠ 0 := fun t => pow_ne_zero _ hx0
  have hvnorm : ∀ t, ‖v t‖ = ‖x‖ ^ (t + 1) := fun t => by rw [hv]; exact norm_pow x (t + 1)
  have hvbig : ∀ t, 1 < ‖v t‖ := by
    intro t
    rw [hvnorm t]
    exact one_lt_pow₀ hx (Nat.succ_ne_zero t)
  have hvinvnorm : ∀ t, ‖(v t)⁻¹‖ = ‖x⁻¹‖ ^ (t + 1) := by
    intro t
    rw [norm_inv, hvnorm t, norm_inv, inv_pow]

  set f : ℕ → K := fun t => qshiftBeta (v t) M * (v t)⁻¹ ^ k₀ with hf

  have hf0 : Tendsto f atTop (nhds 0) := by
    have hbound : ∀ t, ‖f t‖ ≤ (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
      intro t
      rw [hf]
      simp only []
      rw [norm_mul, norm_pow]
      have h1 : ‖qshiftBeta (v t) M‖ ≤ 1 := norm_qshiftBeta_le_one (hvbig t) M
      have h2 : ‖(v t)⁻¹‖ ^ k₀ = (‖x⁻¹‖ ^ (t + 1)) ^ k₀ := by rw [hvinvnorm t]
      have h3 : (‖x⁻¹‖ ^ (t + 1)) ^ k₀ = (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have h4 : (0 : ℝ) ≤ ‖(v t)⁻¹‖ ^ k₀ := pow_nonneg (norm_nonneg _) _
      calc ‖qshiftBeta (v t) M‖ * ‖(v t)⁻¹‖ ^ k₀ ≤ 1 * ‖(v t)⁻¹‖ ^ k₀ :=
            mul_le_mul_of_nonneg_right h1 h4
        _ = (‖x⁻¹‖ ^ k₀) ^ (t + 1) := by rw [one_mul, h2, h3]
    have hratio : ‖x⁻¹‖ ^ k₀ < 1 :=
      pow_lt_one₀ (norm_nonneg _) hxinv (by omega)
    have hgeo : Tendsto (fun t : ℕ => (‖x⁻¹‖ ^ k₀) ^ (t + 1)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (‖x⁻¹‖ ^ k₀) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (norm_nonneg _) _) hratio
      exact h1.comp (tendsto_add_atTop_nat 1)
    exact squeeze_zero_norm hbound hgeo

  have hflim : Tendsto f atTop (nhds ((lineCoeff M k₀ : ℤ) : K)) := by

    have hfeq : ∀ t, f t
        = ∑ k ∈ Finset.Icc 1 M,
            ((lineCoeff M k : ℤ) : K) * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀ := by
      intro t
      rw [hf]
      simp only []
      rw [← hdiamond (v t) (hvbig t), Finset.sum_mul]

    have hterm : ∀ k ∈ Finset.Icc 1 M,
        Tendsto (fun t => ((lineCoeff M k : ℤ) : K) * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
          atTop (nhds (if k = k₀ then ((lineCoeff M k₀ : ℤ) : K) else 0)) := by
      intro k hk
      have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1

      have hpt : ∀ t, ((lineCoeff M k : ℤ) : K) * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀
          = ((lineCoeff M k : ℤ) : K)
              * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) + ((x ^ (k + k₀))⁻¹) ^ (t + 1)) := by
        intro t
        rw [hv]
        simp only []
        have hxp : x ^ (t + 1) ≠ 0 := pow_ne_zero _ hx0
        field_simp
        ring
      rcases lt_trichotomy k k₀ with hlt | heq | hgt
      ·
        rw [if_neg (Nat.ne_of_lt hlt)]
        have hw : ‖x ^ k * (x ^ k₀)⁻¹‖ < 1 := by
          rw [norm_mul, norm_inv, norm_pow, norm_pow, ← div_eq_mul_inv]
          rw [div_lt_one (pow_pos (lt_trans one_pos hx) k₀)]
          exact pow_lt_pow_right₀ hx hlt
        have hz : ‖(x ^ (k + k₀))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hwlim : Tendsto (fun t : ℕ => (x ^ k * (x ^ k₀)⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw).comp (tendsto_add_atTop_nat 1)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k₀))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => ((lineCoeff M k : ℤ) : K)
            * ((x ^ k * (x ^ k₀)⁻¹) ^ (t + 1) + ((x ^ (k + k₀))⁻¹) ^ (t + 1)))
            atTop (nhds (((lineCoeff M k : ℤ) : K) * (0 + 0))) :=
          (hwlim.add hzlim).const_mul _
        rw [add_zero, mul_zero] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      ·
        subst heq
        rw [if_pos rfl]
        have hw1 : x ^ k * (x ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hx0)
        have hz : ‖(x ^ (k + k))⁻¹‖ < 1 := by
          rw [norm_inv, inv_lt_one_iff₀]
          right
          rw [norm_pow]
          exact one_lt_pow₀ hx (by omega)
        have hzlim : Tendsto (fun t : ℕ => ((x ^ (k + k))⁻¹) ^ (t + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).comp (tendsto_add_atTop_nat 1)
        have hlim : Tendsto (fun t => ((lineCoeff M k : ℤ) : K)
            * ((x ^ k * (x ^ k)⁻¹) ^ (t + 1) + ((x ^ (k + k))⁻¹) ^ (t + 1)))
            atTop (nhds (((lineCoeff M k : ℤ) : K) * (1 + 0))) := by
          have h1 : Tendsto (fun t : ℕ => (x ^ k * (x ^ k)⁻¹) ^ (t + 1)) atTop (nhds 1) := by
            simp only [hw1, one_pow]
            exact tendsto_const_nhds
          exact (h1.add hzlim).const_mul _
        rw [add_zero, mul_one] at hlim
        refine Tendsto.congr (fun t => (hpt t).symm) hlim
      ·
        rw [if_neg (by omega)]
        have hzero : lineCoeff M k = 0 := hbig k hgt hkM
        have hconst : ∀ t, ((lineCoeff M k : ℤ) : K) * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀
            = 0 := by
          intro t
          rw [hzero]
          simp
        refine Tendsto.congr (fun t => (hconst t).symm) tendsto_const_nhds

    have hsum : Tendsto (fun t => ∑ k ∈ Finset.Icc 1 M,
        ((lineCoeff M k : ℤ) : K) * ((v t) ^ k + (v t)⁻¹ ^ k) * (v t)⁻¹ ^ k₀)
        atTop (nhds (∑ k ∈ Finset.Icc 1 M,
          if k = k₀ then ((lineCoeff M k₀ : ℤ) : K) else 0)) :=
      tendsto_finsetSum _ hterm
    have hcollapse : (∑ k ∈ Finset.Icc 1 M,
        if k = k₀ then ((lineCoeff M k₀ : ℤ) : K) else 0) = ((lineCoeff M k₀ : ℤ) : K) := by
      rw [Finset.sum_ite_eq' (Finset.Icc 1 M) k₀ (fun _ => ((lineCoeff M k₀ : ℤ) : K))]
      rw [if_pos (Finset.mem_Icc.mpr ⟨hk₀1, hk₀M⟩)]
    rw [hcollapse] at hsum
    exact Tendsto.congr (fun t => (hfeq t).symm) hsum

  have hzero : ((lineCoeff M k₀ : ℤ) : K) = 0 := tendsto_nhds_unique hflim hf0
  exact_mod_cast hzero

theorem lineCoeff_eq_zero_of_qshift
    (hmaster : ∀ v : K, 1 < ‖v‖ → ∀ M : ℕ,
      (4 : K) * defectCoeff v M = qshiftAlpha v M + qshiftBeta v M + qshiftGamma M) :
    ∀ N k : ℕ, 1 ≤ k → k ≤ N → lineCoeff N k = 0 := by

  suffices h : ∀ B N k : ℕ, N ≤ B → 1 ≤ k → k ≤ N → lineCoeff N k = 0 by
    intro N k h1 h2
    exact h N N k le_rfl h1 h2
  intro B
  induction B with
  | zero =>
      intro N k hNB h1 h2
      omega
  | succ B ihB =>
      intro N k hNB h1 h2
      rcases Nat.lt_or_ge N (B + 1) with hN | hN
      · exact ihB N k (by omega) h1 h2

      have hNeq : N = B + 1 := by omega
      have hM0 : 0 < N := by omega

      have hdiamond : ∀ v : K, 1 < ‖v‖ →
          ∑ j ∈ Finset.Icc 1 N, ((lineCoeff N j : ℤ) : K) * (v ^ j + v⁻¹ ^ j)
            = qshiftBeta v N := by
        intro v hv
        have hv0 : v ≠ 0 := ne_zero_of_one_lt_norm hv
        have hv1 : v ≠ 1 := ne_one_of_one_lt_norm hv
        have h1 := hmaster v hv N
        rw [four_mul_defectCoeff_eq_sum_lines hv0 hv1 hM0] at h1

        have hα : qshiftAlpha v N = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hmem := Finset.mem_filter.mp hp
          have hanti := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
          have hp1 : 1 ≤ p.2 := hmem.2.1
          have hp2 : p.2 ≤ p.1 := hmem.2.2
          have hlow : lineCoeff p.1 p.2 = 0 := by
            refine ihB p.1 p.2 (by omega) hp1 hp2
          rw [hlow]
          simp
        rw [hα, zero_add] at h1

        calc ∑ j ∈ Finset.Icc 1 N, ((lineCoeff N j : ℤ) : K) * (v ^ j + v⁻¹ ^ j)
            = ∑ j ∈ Finset.Icc 1 N,
                (((lineCoeff N j : ℤ) : K) * Fz v (j : ℤ)
                  + (2 : K) * ((lineCoeff N j : ℤ) : K)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Fz_natCast]
              ring
          _ = (∑ j ∈ Finset.Icc 1 N, ((lineCoeff N j : ℤ) : K) * Fz v (j : ℤ))
                + ∑ j ∈ Finset.Icc 1 N, (2 : K) * ((lineCoeff N j : ℤ) : K) :=
              Finset.sum_add_distrib
          _ = (qshiftBeta v N + qshiftGamma N)
                + ∑ j ∈ Finset.Icc 1 N, (2 : K) * ((lineCoeff N j : ℤ) : K) := by
              rw [h1]
          _ = qshiftBeta v N
                + (∑ j ∈ Finset.Icc 1 N, (-2 : K) * ((lineCoeff N j : ℤ) : K)
                    + ∑ j ∈ Finset.Icc 1 N, (2 : K) * ((lineCoeff N j : ℤ) : K)) := by
              rw [qshiftGamma, add_assoc]
          _ = qshiftBeta v N := by
              rw [← Finset.sum_add_distrib]
              have hzero : ∑ j ∈ Finset.Icc 1 N,
                  ((-2 : K) * ((lineCoeff N j : ℤ) : K)
                    + (2 : K) * ((lineCoeff N j : ℤ) : K)) = 0 := by
                refine Finset.sum_eq_zero fun j _ => ?_
                ring
              rw [hzero, add_zero]

      have hcol : ∀ d j : ℕ, 1 ≤ j → j ≤ N → N ≤ j + d → lineCoeff N j = 0 := by
        intro d
        induction d with
        | zero =>
            intro j h1' h2' hd
            have hjN : j = N := by omega
            subst hjN
            exact lineCoeff_eq_zero_of_diamond h1' le_rfl hdiamond
              (fun k' hk' hk'' => absurd hk'' (by omega))
        | succ d ihd =>
            intro j h1' h2' hd
            rcases (by omega : N ≤ j + d ∨ j + d < N) with h | h
            · exact ihd j h1' h2' h
            · refine lineCoeff_eq_zero_of_diamond h1' h2' hdiamond fun k' hk' hk'' => ?_
              exact ihd k' (by omega) hk'' (by omega)
      exact hcol N k h1 (by omega) (by omega)

end Descent

end TateCurve

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Uniqueness

set_option maxHeartbeats 1000000 in

lemma coeff_eq_zero_step {c : ℕ → K} {q₀ : K} (hq₀0 : q₀ ≠ 0) (hq₀1 : ‖q₀‖ < 1)
    {B : ℝ} (hBle : ∀ N, ‖c N * q₀ ^ N‖ ≤ B)
    (hcsum : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => c N * q ^ N)
    (hczero : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ∑' N, c N * q ^ N = 0)
    (N₀ : ℕ) (hlow : ∀ j, j < N₀ → c j = 0) : c N₀ = 0 := by
  have hq₀norm : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀0
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBle 0)
  have hC0 : (0 : ℝ) ≤ B / ‖q₀‖ ^ (N₀ + 1) :=
    div_nonneg hB0 (le_of_lt (pow_pos hq₀norm _))

  have hA : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ‖c N₀‖ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ := by
    intro q hq hqle
    have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
    have hsum := hcsum q hq hqle

    have hsplit1 : (∑ i ∈ Finset.range N₀, c i * q ^ i) + ∑' i, c (i + N₀) * q ^ (i + N₀)
        = ∑' i, c i * q ^ i := hsum.sum_add_tsum_nat_add N₀
    have hhead : (∑ i ∈ Finset.range N₀, c i * q ^ i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hlow i (Finset.mem_range.mp hi), zero_mul]
    have hshift : Summable fun i => c (i + N₀) * q ^ (i + N₀) :=
      (summable_nat_add_iff N₀).mpr hsum
    have htail0 : ∑' i, c (i + N₀) * q ^ (i + N₀) = 0 := by
      have h0 := hczero q hq hqle
      rw [← hsplit1, hhead, zero_add] at h0
      exact h0

    have hsplit2 : ∑' i, c (i + N₀) * q ^ (i + N₀)
        = c N₀ * q ^ N₀ + ∑' i, c (i + 1 + N₀) * q ^ (i + 1 + N₀) := by
      rw [hshift.tsum_eq_zero_add]
      simp only [Nat.zero_add]
    have hkey : c N₀ * q ^ N₀ = - ∑' i, c (i + 1 + N₀) * q ^ (i + 1 + N₀) := by
      have h0 := htail0
      rw [hsplit2] at h0
      exact eq_neg_of_add_eq_zero_left h0

    have hratio0 : 0 ≤ ‖q‖ / ‖q₀‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hratio_le_one : ‖q‖ / ‖q₀‖ ≤ 1 := (div_le_one hq₀norm).mpr hqle
    have htermbound : ∀ i, ‖c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
        ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := by
      intro i
      have hq₀j : (0 : ℝ) < ‖q₀‖ ^ (i + 1 + N₀) := pow_pos hq₀norm _
      have h1 : ‖c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
          = ‖c (i + 1 + N₀) * q₀ ^ (i + 1 + N₀)‖ * (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, div_pow]
        field_simp
      have h2 : (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) ≤ (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := by
        have hsplit : (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀)
            = (‖q‖ / ‖q₀‖) ^ (N₀ + 1) * (‖q‖ / ‖q₀‖) ^ ((i + 1 + N₀) - (N₀ + 1)) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hsplit]
        have h3 : (‖q‖ / ‖q₀‖) ^ ((i + 1 + N₀) - (N₀ + 1)) ≤ 1 :=
          pow_le_one₀ hratio0 hratio_le_one
        have h4 : (0 : ℝ) ≤ (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := pow_nonneg hratio0 _
        nlinarith
      have h5 : B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) = B * (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := by
        rw [div_pow]
        field_simp
      calc ‖c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
          = ‖c (i + 1 + N₀) * q₀ ^ (i + 1 + N₀)‖ * (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) := h1
        _ ≤ B * (‖q‖ / ‖q₀‖) ^ (N₀ + 1) := by
            have h6 := hBle (i + 1 + N₀)
            have h7 : (0 : ℝ) ≤ (‖q‖ / ‖q₀‖) ^ (i + 1 + N₀) := pow_nonneg hratio0 _
            nlinarith [norm_nonneg (c (i + 1 + N₀) * q₀ ^ (i + 1 + N₀))]
        _ = B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := h5.symm

    have htail_le : ‖∑' i, c (i + 1 + N₀) * q ^ (i + 1 + N₀)‖
        ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) :=
      norm_tsum_le_of_forall_le_of_nonneg
        (mul_nonneg hC0 (pow_nonneg (norm_nonneg _) _)) htermbound
    have h8 : ‖c N₀‖ * ‖q‖ ^ N₀ ≤ (B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖) * ‖q‖ ^ N₀ := by
      have h9 : ‖c N₀ * q ^ N₀‖ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := by
        rw [hkey, norm_neg]
        exact htail_le
      rw [norm_mul, norm_pow] at h9
      calc ‖c N₀‖ * ‖q‖ ^ N₀ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖ ^ (N₀ + 1) := h9
        _ = (B / ‖q₀‖ ^ (N₀ + 1) * ‖q‖) * ‖q‖ ^ N₀ := by rw [pow_succ]; ring
    exact le_of_mul_le_mul_right h8 (pow_pos hqnorm N₀)

  have hbound : ∀ t : ℕ, ‖c N₀‖ ≤ B / ‖q₀‖ ^ (N₀ + 1) * ‖q₀‖ ^ (t + 1) := by
    intro t
    have hqt0 : q₀ ^ (t + 1) ≠ 0 := pow_ne_zero _ hq₀0
    have hqtle : ‖q₀ ^ (t + 1)‖ ≤ ‖q₀‖ := by
      rw [norm_pow]
      have h1 : ‖q₀‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg q₀) (le_of_lt hq₀1)
      calc ‖q₀‖ ^ (t + 1) = ‖q₀‖ ^ t * ‖q₀‖ := by rw [pow_succ]
        _ ≤ 1 * ‖q₀‖ := by nlinarith [norm_nonneg q₀]
        _ = ‖q₀‖ := one_mul _
    have h2 := hA (q₀ ^ (t + 1)) hqt0 hqtle
    rwa [norm_pow] at h2
  have hgeo : Tendsto (fun t : ℕ => B / ‖q₀‖ ^ (N₀ + 1) * ‖q₀‖ ^ (t + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℕ => ‖q₀‖ ^ t) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq₀1
    have h2 : Tendsto (fun t : ℕ => ‖q₀‖ ^ (t + 1)) atTop (nhds 0) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have h3 := h2.const_mul (B / ‖q₀‖ ^ (N₀ + 1))
    simpa using h3
  have hzero : Tendsto (fun _ : ℕ => c N₀) atTop (nhds 0) := squeeze_zero_norm hbound hgeo
  exact tendsto_nhds_unique tendsto_const_nhds hzero

set_option maxHeartbeats 1000000 in

lemma coeff_eq_of_forall_tsum_eq {a b : ℕ → K} {q₀ : K} (hq₀0 : q₀ ≠ 0)
    (hq₀1 : ‖q₀‖ < 1)
    (ha : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => a N * q ^ N)
    (hb : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => b N * q ^ N)
    (heq : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ∑' N, a N * q ^ N = ∑' N, b N * q ^ N) :
    ∀ N, a N = b N := by

  have hcsum : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → Summable fun N => (a N - b N) * q ^ N := by
    intro q hq hqle
    exact ((ha q hq hqle).sub (hb q hq hqle)).congr fun N => by ring
  have hczero : ∀ q : K, q ≠ 0 → ‖q‖ ≤ ‖q₀‖ → ∑' N, (a N - b N) * q ^ N = 0 := by
    intro q hq hqle
    have h1 : ∑' N, (a N - b N) * q ^ N = (∑' N, a N * q ^ N) - ∑' N, b N * q ^ N := by
      rw [← (ha q hq hqle).tsum_sub (hb q hq hqle)]
      exact tsum_congr fun N => by ring
    rw [h1, heq q hq hqle, sub_self]

  have hterms : Tendsto (fun N => ‖(a N - b N) * q₀ ^ N‖) atTop (nhds 0) := by
    have h1 := (hcsum q₀ hq₀0 le_rfl).tendsto_atTop_zero
    have h2 := (continuous_norm.tendsto (0 : K)).comp h1
    simpa [Function.comp_def] using h2
  obtain ⟨B, hBmem⟩ := hterms.bddAbove_range
  have hBle : ∀ N, ‖(a N - b N) * q₀ ^ N‖ ≤ B := fun N => hBmem ⟨N, rfl⟩

  have hall : ∀ Bnd N, N ≤ Bnd → a N - b N = 0 := by
    intro Bnd
    induction Bnd with
    | zero =>
        intro N hN
        have hN0 : N = 0 := by omega
        subst hN0
        exact coeff_eq_zero_step hq₀0 hq₀1 hBle hcsum hczero 0
          fun j hj => absurd hj (by omega)
    | succ Bnd ihB =>
        intro N hN
        rcases Nat.lt_or_ge N (Bnd + 1) with h | h
        · exact ihB N (by omega)
        · have hNeq : N = Bnd + 1 := by omega
          subst hNeq
          exact coeff_eq_zero_step hq₀0 hq₀1 hBle hcsum hczero (Bnd + 1)
            fun j hj => ihB j (by omega)
  intro N
  exact sub_eq_zero.mp (hall N N le_rfl)

end Uniqueness

section Reindex

def shiftPair : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)

lemma shiftPair_injective : Function.Injective shiftPair := by
  intro p p' h
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only [shiftPair, Prod.mk.injEq] at h ⊢
  omega

lemma mem_range_shiftPair {p : ℕ × ℕ} (h : p.2 ≤ p.1) : p ∈ Set.range shiftPair :=
  ⟨(p.1 - p.2, p.2), by
    simp only [shiftPair]
    exact Prod.ext (by omega) rfl⟩

lemma tsum_prod_eq_tsum_sum_antidiagonal {f : ℕ × ℕ → K} (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p = ∑' M : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal M, f p := by
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq f
  rw [← he]
  have hsum : Summable fun x : Σ M : ℕ, (Finset.HasAntidiagonal.antidiagonal M : Finset (ℕ × ℕ)) =>
      f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd x) := by
    have h1 := (Equiv.summable_iff (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))).mpr hf
    simpa [Function.comp_def] using h1
  rw [hsum.tsum_sigma]
  refine tsum_congr fun M => ?_
  rw [tsum_fintype, ← Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal M) f]
  exact Finset.sum_congr rfl fun c _ => rfl

end Reindex

section Families

variable (u q : K)

noncomputable def hubTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    ((lineCoeff p.1 p.2 : ℤ) : K) * Fz (q * u) (p.2 : ℤ) * q ^ p.1 else 0

noncomputable def alphaTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    ((lineCoeff p.1 p.2 : ℤ) : K) * u ^ p.2 * q ^ (p.1 + p.2) else 0

noncomputable def betaTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    ((lineCoeff p.1 p.2 : ℤ) : K) * u⁻¹ ^ p.2 * q ^ (p.1 - p.2) else 0

noncomputable def gammaTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    (-2 : K) * ((lineCoeff p.1 p.2 : ℤ) : K) * q ^ p.1 else 0

variable {u q}

lemma hubTerm_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (p : ℕ × ℕ) :
    hubTerm u q p = alphaTerm u q p + betaTerm u q p + gammaTerm q p := by
  simp only [hubTerm, alphaTerm, betaTerm, gammaTerm]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, if_pos hg, if_pos hg]
    obtain ⟨j, hj⟩ : ∃ j, p.1 = j + p.2 := ⟨p.1 - p.2, by omega⟩
    rw [Fz_natCast, hj]
    have hqp : q ^ p.2 ≠ 0 := pow_ne_zero _ hq0
    have hup : u ^ p.2 ≠ 0 := pow_ne_zero _ hu0
    have h1 : (j + p.2) - p.2 = j := by omega
    rw [h1, mul_pow, pow_add, pow_add, inv_pow, inv_pow]
    field_simp
    ring
  · rw [if_neg hg, if_neg hg, if_neg hg, if_neg hg]
    ring

lemma summable_of_shift_bound {f : ℕ × ℕ → K} {s ρ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hvanish : ∀ p : ℕ × ℕ, ¬ p.2 ≤ p.1 → f p = 0)
    (hbound : ∀ p : ℕ × ℕ, ‖f (shiftPair p)‖ ≤ s ^ p.1 * ρ ^ p.2) :
    Summable f := by
  have hgeom : Summable fun p : ℕ × ℕ => s ^ p.1 * ρ ^ p.2 :=
    (summable_geometric_of_lt_one hs0 hs1).mul_of_nonneg
      (summable_geometric_of_lt_one hρ0 hρ1)
      (fun _ => pow_nonneg hs0 _) (fun _ => pow_nonneg hρ0 _)
  have hcomp : Summable fun p : ℕ × ℕ => f (shiftPair p) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hgeom)
  have hsupport : ∀ x ∉ Set.range shiftPair, f x = 0 := by
    intro x hx
    refine hvanish x fun hle => hx (mem_range_shiftPair hle)
  have hcomp' : Summable (f ∘ shiftPair) := by exact hcomp
  exact (shiftPair_injective.summable_iff hsupport).mp hcomp'

set_option maxHeartbeats 1000000 in
lemma summable_alphaTerm (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    Summable (alphaTerm u q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  refine summable_of_shift_bound (norm_nonneg q) hq1
    (mul_nonneg (norm_nonneg q) (norm_nonneg u)) hqu ?_ ?_
  · intro p hp
    simp only [alphaTerm]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [alphaTerm, shiftPair]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
      have h2 : ‖q‖ ^ (p.1 + p.2 + p.2) = ‖q‖ ^ p.1 * ‖q‖ ^ p.2 * ‖q‖ ^ p.2 := by
        rw [← pow_add, ← pow_add]
      have h3 : ‖q‖ ^ p.2 ≤ 1 := pow_le_one₀ (norm_nonneg q) (le_of_lt hq1)
      calc ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖ * ‖u‖ ^ p.2 * ‖q‖ ^ (p.1 + p.2 + p.2)
          = ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖
              * (‖q‖ ^ p.1 * (‖q‖ * ‖u‖) ^ p.2 * ‖q‖ ^ p.2) := by
            rw [h2, mul_pow]
            ring
        _ ≤ 1 * (‖q‖ ^ p.1 * (‖q‖ * ‖u‖) ^ p.2 * 1) := by
            refine mul_le_mul h1 ?_ (by positivity) zero_le_one
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ‖q‖ ^ p.1 * (‖q‖ * ‖u‖) ^ p.2 := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 1000000 in
lemma summable_betaTerm (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    Summable (betaTerm u q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  have hρ : ‖u⁻¹‖ < 1 := norm_inv_lt_one_of_one_lt_norm hu
  refine summable_of_shift_bound (norm_nonneg q) hq1 (norm_nonneg u⁻¹) hρ ?_ ?_
  · intro p hp
    simp only [betaTerm]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [betaTerm, shiftPair]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      have h0 : p.1 + p.2 - p.2 = p.1 := by omega
      rw [h0, norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
      calc ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖ * ‖u⁻¹‖ ^ p.2 * ‖q‖ ^ p.1
          ≤ 1 * ‖u⁻¹‖ ^ p.2 * ‖q‖ ^ p.1 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ‖q‖ ^ p.1 * ‖u⁻¹‖ ^ p.2 := by ring
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 1000000 in
lemma summable_gammaTerm (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    Summable (gammaTerm q) := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  refine summable_of_shift_bound (norm_nonneg q) hq1 (norm_nonneg q) hq1 ?_ ?_
  · intro p hp
    simp only [gammaTerm]
    exact if_neg fun hg => hp hg.2
  · intro p
    simp only [gammaTerm, shiftPair]
    by_cases hg : 1 ≤ p.2
    · rw [if_pos ⟨hg, by omega⟩]
      rw [norm_mul, norm_mul, norm_pow]
      have h1 : ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖ ≤ 1 := norm_intCast_le_one K _
      have h2 : ‖(-2 : K)‖ ≤ 1 := by
        rw [norm_neg]
        have h3 : ((2 : ℕ) : K) = (2 : K) := by norm_num
        have h4 := norm_natCast_le_one K 2
        rwa [h3] at h4
      calc ‖(-2 : K)‖ * ‖((lineCoeff (p.1 + p.2) p.2 : ℤ) : K)‖ * ‖q‖ ^ (p.1 + p.2)
          ≤ 1 * 1 * ‖q‖ ^ (p.1 + p.2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = ‖q‖ ^ p.1 * ‖q‖ ^ p.2 := by rw [one_mul, one_mul, ← pow_add]
    · rw [if_neg fun hcon => hg hcon.1, norm_zero]
      positivity

set_option maxHeartbeats 1000000 in
lemma summable_hubTerm (hu : 1 < ‖u‖) (hq0 : q ≠ 0) (hqu : ‖q‖ * ‖u‖ < 1) :
    Summable (hubTerm u q) := by
  have hu0 : u ≠ 0 := ne_zero_of_one_lt_norm hu
  exact (((summable_alphaTerm hu hqu).add (summable_betaTerm hu hqu)).add
    (summable_gammaTerm hu hqu)).congr fun p => (hubTerm_eq hq0 hu0 p).symm

end Families

section Regroup

variable {u q : K}

set_option maxHeartbeats 1000000 in
lemma tsum_alphaTerm (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ∑' p : ℕ × ℕ, alphaTerm u q p = ∑' M : ℕ, qshiftAlpha u M * q ^ M := by
  rw [tsum_prod_eq_tsum_sum_antidiagonal (summable_alphaTerm hu hqu)]
  refine tsum_congr fun M => ?_
  simp only [qshiftAlpha]
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpM : p.1 + p.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [alphaTerm]
  by_cases hg : 1 ≤ p.2 ∧ p.2 ≤ p.1
  · rw [if_pos hg, if_pos hg, hpM]
  · rw [if_neg hg, if_neg hg, zero_mul]

set_option maxHeartbeats 1000000 in
lemma tsum_betaTerm (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ∑' p : ℕ × ℕ, betaTerm u q p = ∑' M : ℕ, qshiftBeta u M * q ^ M := by
  have hsupport : Function.support (betaTerm u q) ⊆ Set.range shiftPair := by
    intro p hp
    by_contra hcon
    refine hp ?_
    simp only [betaTerm]
    refine if_neg fun hg => hcon (mem_range_shiftPair hg.2)
  rw [← shiftPair_injective.tsum_eq hsupport]
  have hcomp : Summable fun p : ℕ × ℕ => betaTerm u q (shiftPair p) :=
    (summable_betaTerm hu hqu).comp_injective shiftPair_injective
  rw [hcomp.tsum_prod]
  refine tsum_congr fun M => ?_
  simp only [qshiftBeta]
  rw [← tsum_mul_right]
  refine tsum_congr fun k => ?_
  simp only [betaTerm, shiftPair]
  by_cases hk : 1 ≤ k
  · rw [if_pos ⟨hk, by omega⟩, if_pos hk]
    have h0 : M + k - k = M := by omega
    rw [h0]
  · rw [if_neg fun hcon => hk hcon.1, if_neg hk, zero_mul]

set_option maxHeartbeats 1000000 in
lemma tsum_gammaTerm (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    ∑' p : ℕ × ℕ, gammaTerm q p = ∑' M : ℕ, qshiftGamma M * q ^ M := by
  rw [(summable_gammaTerm hu hqu).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, gammaTerm q (N, k) = 0 := by
    intro k hk
    simp only [gammaTerm]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish]
  simp only [qshiftGamma]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  simp only [gammaTerm]
  rw [if_pos ⟨hk'.1, hk'.2⟩]

set_option maxHeartbeats 1000000 in
lemma tsum_hubTerm [CharZero K] (hu : 1 < ‖u‖) (hq0 : q ≠ 0) (hqu : ‖q‖ * ‖u‖ < 1) :
    ∑' p : ℕ × ℕ, hubTerm u q p = ∑' N : ℕ, (4 * defectCoeff (q * u) N) * q ^ N := by
  have hu0 : u ≠ 0 := ne_zero_of_one_lt_norm hu
  have hqu0 : q * u ≠ 0 := mul_ne_zero hq0 hu0
  have hqu1 : q * u ≠ 1 := by
    have h1 := qshift_lattice_ne_one hq0 hu hqu 1
    rwa [zpow_one] at h1
  rw [(summable_hubTerm hu hq0 hqu).tsum_prod]
  refine tsum_congr fun N => ?_
  have hvanish : ∀ k ∉ Finset.Icc 1 N, hubTerm u q (N, k) = 0 := by
    intro k hk
    simp only [hubTerm]
    refine if_neg fun hg => hk (Finset.mem_Icc.mpr ⟨hg.1, hg.2⟩)
  rw [tsum_eq_sum hvanish]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, defectCoeff_zero' hqu1, mul_zero, zero_mul]
  · rw [four_mul_defectCoeff_eq_sum_lines hqu0 hqu1 hN, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    simp only [hubTerm]
    rw [if_pos ⟨hk'.1, hk'.2⟩]

end Regroup

section SeriesSummable

variable {u q : K}

set_option maxHeartbeats 1000000 in
lemma summable_defect_series (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    Summable fun N => (4 * defectCoeff u N) * q ^ N := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  have hq1' : ‖q‖₊ < 1 := by exact_mod_cast hq1
  have hann := qshift_annulus_at_u (q := q) hu hqu
  have hXn := summable_norm_xSeries (u := u) hq1' hann.1 hann.2
  have hYn := summable_norm_ySeries (u := u) hq1' hann.1 hann.2
  have hA4n := summable_norm_a₄Series (K := K) hq1'
  have hA6n := summable_norm_a₆Series (K := K) hq1'
  have hXXn := summable_norm_cauchyMul hXn hXn
  have sYY : Summable fun N => cauchyMul (yCoeffFull u) (yCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hYn hYn).of_norm
  have sXY : Summable fun N => cauchyMul (xCoeffFull u) (yCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hXn hYn).of_norm
  have sX3 : Summable fun N =>
      cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N * q ^ N :=
    (summable_norm_cauchyMul hXn hXXn).of_norm
  have sA4X : Summable fun N => cauchyMul a₄Coeff (xCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hA4n hXn).of_norm
  have sA6 : Summable fun N => a₆Coeff (K := K) N * q ^ N := hA6n.of_norm
  have hD : Summable fun N => defectCoeff u N * q ^ N := by
    refine (((sYY.add sXY).sub ((sX3.add sA4X).add sA6)).congr fun N => ?_)
    rw [defectCoeff]
    ring
  exact (hD.mul_left 4).congr fun N => by ring

set_option maxHeartbeats 1000000 in
lemma summable_qshift_series (hu : 1 < ‖u‖) (hqu : ‖q‖ * ‖u‖ < 1) :
    Summable fun M => (qshiftAlpha u M + qshiftBeta u M + qshiftGamma M) * q ^ M := by
  have hq1 : ‖q‖ < 1 := norm_q_lt_one_of_qshift hu hqu
  have hq0' : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hr0 : (0 : ℝ) ≤ ‖q‖ * ‖u‖ := mul_nonneg (norm_nonneg q) (norm_nonneg u)

  have hgeom_r : Summable fun M : ℕ => ((M : ℝ) + 1) * (‖q‖ * ‖u‖) ^ M := by
    have h1 : Summable fun M : ℕ => (M : ℝ) * (‖q‖ * ‖u‖) ^ M := by
      have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := ‖q‖ * ‖u‖) (by rwa [Real.norm_of_nonneg hr0])
      exact h2.congr fun M => by rw [pow_one]
    have h3 : Summable fun M : ℕ => (‖q‖ * ‖u‖) ^ M := summable_geometric_of_lt_one hr0 hqu
    exact (h1.add h3).congr fun M => by ring
  have hgeom_s : Summable fun M : ℕ => ‖q‖ ^ M := summable_geometric_of_lt_one hq0' hq1
  have hgeom_s2 : Summable fun M : ℕ => 2 * ((M : ℝ) + 1) * ‖q‖ ^ M := by
    have h1 : Summable fun M : ℕ => (M : ℝ) * ‖q‖ ^ M := by
      have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := ‖q‖) (by rwa [Real.norm_of_nonneg hq0'])
      exact h2.congr fun M => by rw [pow_one]
    exact ((h1.add hgeom_s).mul_left 2).congr fun M => by ring
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_)
    ((hgeom_r.add hgeom_s).add hgeom_s2))
  have hα := norm_qshiftAlpha_le (u := u) hu M
  have hβ := norm_qshiftBeta_le_one (u := u) hu M
  have hγ := norm_qshiftGamma_le (K := K) M
  have htriangle : ‖qshiftAlpha u M + qshiftBeta u M + qshiftGamma M‖
      ≤ ‖qshiftAlpha u M‖ + ‖qshiftBeta u M‖ + ‖(qshiftGamma M : K)‖ := by
    calc ‖qshiftAlpha u M + qshiftBeta u M + qshiftGamma M‖
        ≤ ‖qshiftAlpha u M + qshiftBeta u M‖ + ‖(qshiftGamma M : K)‖ := norm_add_le _ _
      _ ≤ ‖qshiftAlpha u M‖ + ‖qshiftBeta u M‖ + ‖(qshiftGamma M : K)‖ := by
          have := norm_add_le (qshiftAlpha u M) (qshiftBeta u M)
          linarith
  have hqM : (0 : ℝ) ≤ ‖q‖ ^ M := pow_nonneg (norm_nonneg q) _
  have huM : ‖u‖ ^ M * ‖q‖ ^ M = (‖q‖ * ‖u‖) ^ M := by rw [← mul_pow]; ring_nf
  rw [norm_mul, norm_pow]
  calc ‖qshiftAlpha u M + qshiftBeta u M + qshiftGamma M‖ * ‖q‖ ^ M
      ≤ (‖qshiftAlpha u M‖ + ‖qshiftBeta u M‖ + ‖(qshiftGamma M : K)‖) * ‖q‖ ^ M := by
        nlinarith [norm_nonneg (qshiftAlpha u M + qshiftBeta u M + qshiftGamma M)]

    _ ≤ (((M : ℝ) + 1) * ‖u‖ ^ M + 1 + 2 * ((M : ℝ) + 1)) * ‖q‖ ^ M := by
        have h1 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
        nlinarith [norm_nonneg (qshiftAlpha u M), norm_nonneg (qshiftBeta u M),
          norm_nonneg ((qshiftGamma M : K)), pow_nonneg (norm_nonneg u) M]
    _ = ((M : ℝ) + 1) * (‖q‖ * ‖u‖) ^ M + ‖q‖ ^ M + 2 * ((M : ℝ) + 1) * ‖q‖ ^ M := by
        rw [← huM]
        ring

end SeriesSummable

end TateCurve


