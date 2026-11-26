-- Prove2me | Definitions.Def_RHHeight1000_20261117_P03_v3
-- name    : RHHeight1000_20261117_P03_v3
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:11:38.120881+00:00
-- url     : https://prove2.me/theorems/aed51128-0991-4e22-bc8f-2b6f273509b5
-- title:
--   Zeta analytic counting dependencies 03 (ordinary proofs)
-- statement:
--   Complete analytic proof dependencies for zeta counting, without custom metaprogramming declarations. No numeric zero-certification assumptions. Source attribution and Apache-2.0 headers retained.
-- source:
--   smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe; reduced height and Lean 4.33.1 packaging by Desenvolvimento RH. AXLE full source d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Definitions.Def_RHHeight1000_20261117_P02_v3
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort34
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Filter Topology
open scoped Nat
namespace Complex
theorem eulerMaclaurinRemainderIoi_cpow_eq (s : ℂ) (p N : ℕ) :
    Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = -(ascPochhammer ℂ p).eval s / (p ! : ℂ)
          * ∫ x in Set.Ioi (N : ℝ),
              (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)) := by
  rw [Complex.eulerMaclaurinRemainderIoi]
  have step1 : (∫ x in Set.Ioi (N : ℝ),
        (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x)
      = ∫ x in Set.Ioi (N : ℝ), ((-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s)
          * ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg N) (Set.mem_Ioi.mp hx)
    dsimp only
    rw [Complex.iteratedDeriv_cpow_ofReal_neg s p hx0]
    ring
  rw [step1, integral_const_mul]
  have h2 : (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ p = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨p, by ring⟩
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  field_simp
  linear_combination ((ascPochhammer ℂ p).eval s *
    ∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) * h2
theorem differentiableOn_eulerMaclaurinRemainderIoi_cpow (p N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
      {s : ℂ | (1 : ℝ) - p < s.re} := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hker := Complex.measurable_bernoulliFun_fract p
  have hcpowmeas := Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N)
  simp only [eulerMaclaurinRemainderIoi_cpow_eq]
  refine (((ascPochhammer ℂ p).differentiable.neg.div_const (p ! : ℂ)).differentiableOn).mul
    fun s₀ hs₀ ↦ ?_
  rw [Set.mem_ofPred_eq] at hs₀
  obtain ⟨σ₁, hσlo, hσhi⟩ : ∃ σ₁ : ℝ, (1 : ℝ) - p < σ₁ ∧ σ₁ < s₀.re :=
    ⟨((1 - p) + s₀.re) / 2, by linarith, by linarith⟩
  set ε : ℝ := (σ₁ + p - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hexp : (1 : ℝ) < σ₁ + p - ε := by rw [hεdef]; linarith
  obtain ⟨C, hC0, hC⟩ := Complex.exists_norm_bernoulliFun_fract_le p
  have happ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (N : ℝ)))
    (F := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))
    (F' := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ)
      * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1)))
    (x₀ := s₀) (bound := fun x ↦ C / ε * x ^ (-(σ₁ + p - ε)))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσhi)
    (Filter.Eventually.of_forall fun s ↦ hker.aestronglyMeasurable.mul (hcpowmeas _))
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN
      (by rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith))
    (hker.aestronglyMeasurable.mul
      (((hcpowmeas _).mul
        (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable).mul
          aestronglyMeasurable_const))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      have hx1 : (1 : ℝ) ≤ x :=
        le_of_lt (lt_of_le_of_lt (by exact_mod_cast hN) (Set.mem_Ioi.mp hx))
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
      have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
      rw [show ‖(bernoulliFun p (Int.fract x) : ℂ)
                * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1))‖
              = ‖(bernoulliFun p (Int.fract x) : ℂ)‖ * x ^ (-s.re - p) * Real.log x from by
            rw [← Complex.ofReal_log hx0.le]
            simp only [norm_mul, norm_neg, norm_one, mul_one,
              Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
              Complex.sub_re, Complex.neg_re, Complex.natCast_re, abs_of_nonneg hlog]
            ring,
        show C / ε * x ^ (-(σ₁ + p - ε)) = C * x ^ (-σ₁ - p) * (x ^ ε / ε) from by
          rw [show -(σ₁ + p - ε) = -σ₁ - p + ε from by ring, Real.rpow_add hx0]; ring]
      exact mul_le_mul (mul_le_mul (hC x) (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
          (Real.rpow_nonneg hx0.le _) hC0) (Real.log_le_rpow_div hx0.le hεpos) hlog
        (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _)))
    ((integrableOn_Ioi_rpow_of_lt (a := -(σ₁ + p - ε)) (by linarith) hN0).const_mul (C / ε))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
      have hbase : (x : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le).ne'
      exact HasDerivAt.const_mul _
        ((Complex.hasStrictDerivAt_const_cpow (Or.inl hbase)).hasDerivAt.comp s
          (by simpa using (hasDerivAt_id s).neg.sub_const (p : ℂ))))
  exact happ.2.differentiableAt.differentiableWithinAt
private theorem eulerMaclaurinRemainder_cpow_succ (s : ℂ) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (R : ℝ)
              - iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
        + eulerMaclaurinRemainder (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
            (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hderiv : ∀ q, q < 2 * M + 2 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
    fun q _ x hx ↦ Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q hx
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have hint : ∀ q, 0 < q → q ≤ 2 * M + 2 →
      IntervalIntegrable (iteratedDeriv q f) volume ((N : ℤ) : ℝ)
        (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) :=
    fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q
        (hpos hx)).continuousAt.continuousWithinAt
  have h1 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by lia)
    (fun q _ x hx ↦ hderiv q (by lia) x (hpos hx)) (fun q hq0 hq ↦ hint q hq0 (by lia))
  have h2 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 2) (by lia)
    (fun q hq x hx ↦ hderiv q hq x (hpos hx)) hint
  rw [hRN, hNa, show (2 * M + 1) / 2 + 1 = M + 1 from by lia] at h1
  rw [hRN, hNa, show (2 * M + 2) / 2 + 1 = M + 1 + 1 from by lia,
    Finset.sum_Ico_succ_top (show (1 : ℕ) ≤ M + 1 by lia)] at h2
  simp only [show 2 * (M + 1) = 2 * M + 2 from by ring,
    show 2 * M + 2 - 1 = 2 * M + 1 from by lia] at h2
  linear_combination h2 - h1
theorem eulerMaclaurinRemainderIoi_succ_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M : ℝ) < s.re) :
    Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * M + 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  set c : ℂ := -s - ((2 * M + 1 : ℕ) : ℂ) with hc
  set B : ℂ := ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
  set P : ℂ := (ascPochhammer ℂ (2 * M + 1)).eval s with hP
  have hcre : c.re < 0 := by
    rw [hc, Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; linarith
  have hrem : ∀ q : ℕ, 1 < s.re + (q : ℝ) →
      Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder q f (N : ℝ) (R : ℝ)) atTop
        (𝓝 (Complex.eulerMaclaurinRemainderIoi q f (N : ℝ))) := fun q hq ↦ by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s q N hN hq)
      tendsto_natCast_atTop_atTop).const_mul _
  have hcf : ∀ R : ℕ, 1 ≤ R → iteratedDeriv (2 * M + 1) f (R : ℝ) = -P * (R : ℂ) ^ c := by
    intro R hR
    rw [hf, Complex.iteratedDeriv_cpow_ofReal_neg s (2 * M + 1)
        (by exact_mod_cast hR : (0 : ℝ) < R),
      Odd.neg_one_pow ⟨M, by ring⟩, hc, hP]
    push_cast; ring
  have hbdy : Tendsto (fun R : ℕ ↦ B * (iteratedDeriv (2 * M + 1) f (R : ℝ)
        - iteratedDeriv (2 * M + 1) f (N : ℝ))) atTop (𝓝 (B * P * (N : ℂ) ^ c)) := by
    have hbase := (((tendsto_natCast_cpow_nhds_zero hcre).const_mul (-P)).sub_const
      (-P * (N : ℂ) ^ c)).const_mul B
    rw [show B * (-P * 0 - -P * (N : ℂ) ^ c) = B * P * (N : ℂ) ^ c from by ring] at hbase
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [hcf R (le_trans hN hR), hcf N hN]
  refine tendsto_nhds_unique (Tendsto.congr' ?_ (hrem (2 * M + 1) (by push_cast; linarith)))
    (hbdy.add (hrem (2 * M + 2) (by push_cast; linarith)))
  filter_upwards [eventually_ge_atTop N] with R hR
  exact eulerMaclaurinRemainder_cpow_succ s M N R hN hR
theorem norm_eulerMaclaurinRemainderIoi_one_ofReal_le {x : ℝ} (hx0 : 0 < x) :
    ‖Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-(x : ℂ))) 1‖ ≤ 1 / 2 := by
  have h := eulerMaclaurinRemainderIoi_cpow_eq (x : ℂ) 1 1
  simp only [Nat.cast_one, ascPochhammer_one, Polynomial.eval_X, Nat.factorial_one, div_one] at h
  have hb := norm_integral_le_of_norm_le
    (f := fun y : ℝ ↦ (bernoulliFun 1 (Int.fract y) : ℂ) * (y : ℂ) ^ (-(x : ℂ) - 1))
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    ((integrableOn_Ioi_rpow_of_lt (show -x - 1 < -1 by linarith) one_pos).const_mul (1 / 2)) ?_
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -x - 1 + 1 = -x from by ring, neg_div_neg_eq] at hb
    rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    refine (mul_le_mul_of_nonneg_left hb hx0.le).trans_eq ?_
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := one_pos.trans hy
    have hre : (-(x : ℂ) - 1).re = -x - 1 := by simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      hre, bernoulliFun_one]
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [Int.fract_nonneg y], ?_⟩)
      (Real.rpow_nonneg hy0.le _)
    linarith [Int.fract_lt_one y]
end Complex
noncomputable def zetaEMExpansion (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
    + ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
noncomputable abbrev zetaApproximant (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
noncomputable abbrev zetaRemainder (s : ℂ) (M N : ℕ) : ℂ :=
  ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
      * (ascPochhammer ℂ (2 * M + 1)).eval s
      * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
theorem zetaEMExpansion_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) :
    zetaEMExpansion s M N = zetaApproximant s M N + zetaRemainder s M N := by
  rw [zetaEMExpansion, zetaApproximant, zetaRemainder]; ring
theorem analyticOnNhd_zetaEMExpansion (M N : ℕ) (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ zetaEMExpansion s M N)
      ({s : ℂ | (-(2 * M + 1 : ℝ)) < s.re} \ {1}) := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
  refine DifferentiableOn.analyticOnNhd ?_
    ((isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton)
  simp only [zetaEMExpansion]
  refine DifferentiableOn.add (DifferentiableOn.add (DifferentiableOn.add
    (DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_) ?_) ?_) ?_
  ·
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun n hn ↦ ?_)
    have : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Ico] at hn; exact_mod_cast Nat.one_le_iff_ne_zero.mp hn.1
    exact differentiable_id.neg.const_cpow (Or.inl this)
  ·
    apply DifferentiableOn.div
    · exact (((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow
        (Or.inl hNne)).differentiableOn
    · exact (differentiable_id.sub_const 1).differentiableOn
    · intro s hs; exact sub_ne_zero.mpr hs.2
  ·
    exact ((differentiable_id.neg.const_cpow (Or.inl hNne)).div_const 2).differentiableOn
  ·
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun k _ ↦ ?_)
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * k - 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  ·
    refine Differentiable.differentiableOn ?_
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * M + 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  ·
    refine (Complex.differentiableOn_eulerMaclaurinRemainderIoi_cpow (2 * M + 2) N hN).mono
      fun s hs ↦ ?_
    have hs1 : (-(2 * M + 1 : ℝ)) < s.re := hs.1
    rw [Set.mem_ofPred_eq]
    push_cast
    linarith
theorem riemannZeta_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = zetaEMExpansion s M N := by
  set H : Set ℂ := {z : ℂ | (-(2 * M + 1 : ℝ)) < z.re} with hHdef
  set U : Set ℂ := H \ {1} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hζ : AnalyticOnNhd ℂ riemannZeta U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hUopen
  have hE : AnalyticOnNhd ℂ (fun z ↦ zetaEMExpansion z M N) U :=
    analyticOnNhd_zetaEMExpansion M N hN
  have hP : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  have hcH : Convex ℝ H := convex_halfSpace_re_gt _
  have hmH : ∀ z : ℂ, 0 ≤ z.re → z ∈ H := fun z hz ↦ by
    simp only [hHdef, Set.mem_ofPred_eq]; linarith [hP]
  have hA : IsPreconnected ({z : ℂ | 0 < z.im} ∩ H) :=
    ((convex_halfSpace_im_gt 0).inter hcH).isPreconnected
  have hB : IsPreconnected ({z : ℂ | z.im < 0} ∩ H) :=
    ((convex_halfSpace_im_lt 0).inter hcH).isPreconnected
  have hC : IsPreconnected ({z : ℂ | z.re < 1} ∩ H) :=
    ((convex_halfSpace_re_lt 1).inter hcH).isPreconnected
  have hD : IsPreconnected ({z : ℂ | 1 < z.re} ∩ H) :=
    ((convex_halfSpace_re_gt 1).inter hcH).isPreconnected
  have hUconn : IsPreconnected U := by
    have hUV : U = (({z : ℂ | 0 < z.im} ∩ H) ∪ ({z : ℂ | z.re < 1} ∩ H)
          ∪ ({z : ℂ | z.im < 0} ∩ H)) ∪ ({z : ℂ | 1 < z.re} ∩ H) := by
      ext z
      simp only [hUdef, hHdef, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hre, hne⟩
        rcases lt_trichotomy z.im 0 with him | him | him
        · exact .inl (.inr ⟨him, hre⟩)
        · rcases lt_trichotomy z.re 1 with hlt | heq | hgt
          · exact .inl (.inl (.inr ⟨hlt, hre⟩))
          · exact absurd (Complex.ext (heq.trans Complex.one_re.symm)
              (him.trans Complex.one_im.symm)) hne
          · exact .inr ⟨hgt, hre⟩
        · exact .inl (.inl (.inl ⟨him, hre⟩))
      · rintro (((⟨h, hre⟩ | ⟨h, hre⟩) | ⟨h, hre⟩) | ⟨h, hre⟩) <;>
          exact ⟨hre, by rintro rfl; simp only [Complex.one_im, Complex.one_re] at h; linarith⟩
    have mem : ∀ z : ℂ, ∀ S : Set ℂ, z ∈ S → 0 ≤ z.re → z ∈ S ∩ H := fun _ _ h hz ↦ ⟨h, hmH _ hz⟩
    rw [hUV]
    exact ((hA.union Complex.I (mem _ _ (by simp) (by simp)) (mem _ _ (by simp) (by simp))
        hC).union (-Complex.I) (.inr (mem _ _ (by simp) (by simp)))
        (mem _ _ (by simp) (by simp)) hB).union
      (2 + Complex.I) (.inl (.inl (mem _ _ (by simp) (by simp))))
      (mem _ _ (by simp) (by simp)) hD
  have hagree : riemannZeta =ᶠ[𝓝 (2 : ℂ)] (fun z ↦ zetaEMExpansion z M N) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    have hz1 : 1 < z.re := hz
    rw [riemannZeta_eq_of_one_lt_re z hz1 M N hN]
    simp only [zetaEMExpansion]
    rw [Complex.eulerMaclaurinRemainderIoi_succ_eq z M N hN (by linarith : -(2 * M : ℝ) < z.re)]
    ring
  exact hζ.eqOn_of_preconnected_of_eventuallyEq hE hUconn ⟨hmH _ (by simp), by simp⟩ hagree
    ⟨hs, hs1⟩
theorem riemannZeta_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaApproximant s M N + zetaRemainder s M N := by
  rw [riemannZeta_eq s M N hN hs hs1, zetaEMExpansion_eq_approximant_add_remainder]
theorem riemannZeta_eq_order_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2
      + Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (1 : ℝ) := by
  have h2 := Complex.eulerMaclaurinRemainderIoi_succ_eq s 0 1 le_rfl (by push_cast; linarith)
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow] at h2
  rw [riemannZeta_eq s 0 1 le_rfl (by push_cast; linarith) hs1, zetaEMExpansion]
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow, Finset.Ico_self,
    Finset.sum_empty, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by lia)]
  linear_combination -h2
theorem riemannZeta_ofReal_re_neg_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs1 : (x : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  rw [riemannZeta_eq_order_one (by simpa using hx0) hs1, Complex.add_re, Complex.add_re,
    show (1 / ((x : ℂ) - 1)).re = 1 / (x - 1) from by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_one,
        ← Complex.ofReal_div, Complex.ofReal_re],
    show ((1 : ℂ) / 2).re = 1 / 2 from by norm_num]
  have hRre := (Complex.re_le_norm _).trans
    (Complex.norm_eulerMaclaurinRemainderIoi_one_ofReal_le hx0)
  have hlt : 1 / (x - 1) < -1 := by
    rw [div_lt_iff_of_neg (show x - 1 < 0 by linarith)]; linarith
  linarith
end
end CertificatePort34
section CertificatePort35
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Set
theorem riemannZeta_ofReal_neg_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    (riemannZeta (σ : ℂ)).im = 0 ∧ (riemannZeta (σ : ℂ)).re < 0 :=
  ⟨Complex.conj_eq_iff_im.mp (by simpa using (riemannZeta_conj (σ : ℂ)).symm),
    riemannZeta_ofReal_re_neg_of_mem_Ioo hσ⟩
private theorem riemannXi_ofReal_ne_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    riemannXi (σ : ℂ) ≠ 0 := by
  have hσ0 : (σ : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; linarith
  have hσ1 : (σ : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  have hΓ : Gammaℝ (σ : ℂ) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; linarith)
  rw [riemannXi_eq_prefactor_mul hσ0 hσ1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hσ0 hσ1 hΓ)
    (riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith))
theorem riemannXi_ofReal_ne_zero_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    riemannXi (σ : ℂ) ≠ 0 := by
  obtain ⟨hlo, hhi⟩ := hσ
  rcases lt_trichotomy σ 0 with hneg | rfl | hpos
  ·
    rw [show ((σ : ℂ)) = 1 - ((1 - σ : ℝ) : ℂ) from by push_cast; ring, riemannXi_one_sub]
    exact riemannXi_ofReal_ne_zero_of_one_lt (by linarith)
  · rw [Complex.ofReal_zero, riemannXi_zero]; norm_num
  · rcases lt_trichotomy σ 1 with h1 | rfl | h1
    ·
      exact fun h ↦ (riemannZeta_ofReal_neg_of_mem_Ioo ⟨hpos, h1⟩).2.ne
        (by rw [(riemannXi_eq_zero_iff (by simpa using hpos) (by simpa using h1)).mp h,
          Complex.zero_re])
    · rw [Complex.ofReal_one, riemannXi_one]; norm_num
    · exact riemannXi_ofReal_ne_zero_of_one_lt h1
end
end CertificatePort35
section CertificatePort36
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Set
variable {a b : ℝ}
theorem argVariation_conj (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b (fun u => starRingEnd ℂ (φ u)) = - argVariation a b φ := by
  obtain ⟨g, hg, -⟩ :=
    exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  have hg' : IsContLog a b (fun u => starRingEnd ℂ (φ u)) (fun u => starRingEnd ℂ (g u)) := by
    refine ⟨Complex.continuous_conj.comp_continuousOn hg.1, fun u hu => ?_⟩
    change Complex.exp (starRingEnd ℂ (g u)) = starRingEnd ℂ (φ u)
    rw [Complex.exp_conj, hg.2 u hu]
  rw [argVariation_eq_of_isContLog hab hg', argVariation_eq_of_isContLog hab hg]
  simp only [Complex.conj_im]
  ring
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp only [Complex.one_re] at hs; linarith
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hs0 hs1 hΓ) hζ
theorem riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0)
    (hζ : riemannZeta s ≠ 0) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at him
  have hs1 : s ≠ 1 := by rintro rfl; simp at him
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero him
  rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hs0 hs1 hΓ) hζ
private theorem riemannXi_ofReal_im_eq_zero (σ : ℝ) : (riemannXi (σ : ℂ)).im = 0 := by
  have hc := riemannXi_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at hc
  have := congrArg Complex.im hc
  rw [Complex.conj_im] at this
  linarith
theorem riemannXi_pos_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    0 < (riemannXi (σ : ℂ)).re ∧ (riemannXi (σ : ℂ)).im = 0 := by
  refine ⟨?_, riemannXi_ofReal_im_eq_zero σ⟩
  by_contra hcon
  rw [not_lt] at hcon
  set g : ℝ → ℝ := fun x => (riemannXi (x : ℂ)).re with hg
  have hgcont : ContinuousOn g (Set.uIcc 0 σ) :=
    (Complex.continuous_re.comp
      (differentiable_riemannXi.continuous.comp Complex.continuous_ofReal)).continuousOn
  have hg0 : g 0 = 1 / 2 := by simp [hg, Complex.ofReal_zero, riemannXi_zero]
  have hmem : (0 : ℝ) ∈ Set.uIcc (g 0) (g σ) :=
    Set.mem_uIcc.mpr (Or.inr ⟨hcon, by rw [hg0]; norm_num⟩)
  obtain ⟨c, hc, hgc⟩ := intermediate_value_uIcc hgcont hmem
  have hsub : Set.uIcc 0 σ ⊆ Icc (-1 : ℝ) 2 :=
    Set.uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hσ
  have hcIcc : c ∈ Icc (-1 : ℝ) 2 := hsub hc
  have hzero : riemannXi (c : ℂ) = 0 :=
    Complex.ext (by simpa [hg] using hgc) (riemannXi_ofReal_im_eq_zero c)
  exact riemannXi_ofReal_ne_zero_of_mem_Icc hcIcc hzero
private theorem riemannXi_lineSeg_continuousOn (z₀ z₁ : ℂ) :
    ContinuousOn (fun u => riemannXi (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
  (differentiable_riemannXi.continuous.comp (continuous_lineSeg z₀ z₁)).continuousOn
private theorem riemannXi_lineSeg_ne_zero_of_re_eq_two {z₀ z₁ : ℂ} (h0 : z₀.re = 2)
    (h1 : z₁.re = 2) : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0 := by
  intro u _
  refine riemannXi_ne_zero_of_one_lt_re ?_
  rw [lineSeg_re, h0, h1]; norm_num
private theorem riemannXi_lineSeg_ne_zero_of_im_eq_T {T : ℝ} (hT : T ≠ 0)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {z₀ z₁ : ℂ} (h0 : z₀.im = T) (h1 : z₁.im = T) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0 := by
  intro u _
  have him : (lineSeg z₀ z₁ u).im = T := by rw [lineSeg_im, h0, h1]; ring
  exact riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero (by rw [him]; exact hT) (hT' _ him)
private theorem argVariation_lineSeg_split {f : ℂ → ℂ} (z₀ z₁ : ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hcont : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u))
        + argVariation 0 1 (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
  have hmap1 : Set.MapsTo (fun v : ℝ => t * v) (Set.Icc 0 1) (Set.Icc 0 t) := by
    intro v hv; refine ⟨?_, ?_⟩ <;> nlinarith [hv.1, hv.2, ht0, ht1]
  have hmap2 : Set.MapsTo (fun v : ℝ => t + (1 - t) * v) (Set.Icc 0 1) (Set.Icc t 1) := by
    intro v hv; refine ⟨?_, ?_⟩ <;> nlinarith [hv.1, hv.2, ht0, ht1]
  have hcont1 : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 t) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl ht1)
  have hne1 : ∀ u ∈ Set.Icc (0 : ℝ) t, f (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu => hne u ⟨hu.1, hu.2.trans ht1⟩
  have hcont2 : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc t 1) :=
    hcont.mono (Set.Icc_subset_Icc ht0 le_rfl)
  have hne2 : ∀ u ∈ Set.Icc t (1 : ℝ), f (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu => hne u ⟨ht0.trans hu.1, hu.2⟩
  have e1 : (fun v : ℝ => f (lineSeg z₀ z₁ (t * v)))
      = (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u)) := by
    funext v; congr 1; simp only [lineSeg]; push_cast; ring
  have e2 : (fun v : ℝ => f (lineSeg z₀ z₁ (t + (1 - t) * v)))
      = (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
    funext v; congr 1; simp only [lineSeg]; push_cast; ring
  have h1 : argVariation 0 t (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u)) := by
    rw [← e1]
    exact (argVariation_comp ht0 zero_le_one (by fun_prop) hmap1
      (by show t * 0 = 0; ring) (by show t * 1 = t; ring) hcont1 hne1).symm
  have h2 : argVariation t 1 (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
    rw [← e2]
    exact (argVariation_comp ht1 zero_le_one (by fun_prop) hmap2
      (by show t + (1 - t) * 0 = t; ring) (by show t + (1 - t) * 1 = 1; ring) hcont2 hne2).symm
  rw [argVariation_trans ht0 ht1 hcont hne, h1, h2]
private theorem argVariation_lineSeg_swap {f : ℂ → ℂ} (z₀ z₁ : ℂ)
    (hcont : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u => f (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u => f (lineSeg z₀ z₁ u)) := by
  rw [← argVariation_reverse zero_le_one hcont hne]
  congr 1; funext u
  show f (lineSeg z₁ z₀ u) = f (lineSeg z₀ z₁ (0 + 1 - u))
  congr 1
  simp only [lineSeg]; push_cast; ring
private theorem riemannXi_reflect (s : ℂ) :
    riemannXi (1 - starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  rw [riemannXi_one_sub, riemannXi_conj]
private theorem argVariation_lineSeg_reflect {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u => riemannXi (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1
        (fun u => riemannXi (lineSeg (1 - starRingEnd ℂ z₀) (1 - starRingEnd ℂ z₁) u))
      = - argVariation 0 1 (fun u => riemannXi (lineSeg z₀ z₁ u)) := by
  rw [← argVariation_conj zero_le_one hcont hne]
  congr 1; funext u
  show riemannXi (lineSeg (1 - starRingEnd ℂ z₀) (1 - starRingEnd ℂ z₁) u)
      = starRingEnd ℂ (riemannXi (lineSeg z₀ z₁ u))
  rw [← riemannXi_reflect]
  congr 1
  simp only [lineSeg, map_add, map_sub, map_mul, Complex.conj_ofReal]
  ring
private theorem argVariation_riemannXi_real_eq_zero {z₀ z₁ : ℂ}
    (hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ Icc (-1 : ℝ) 2, lineSeg z₀ z₁ u = (x : ℂ)) :
    argVariation 0 1 (fun u => riemannXi (lineSeg z₀ z₁ u)) = 0 := by
  have hsp : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ∈ Complex.slitPlane := by
    intro u hu
    obtain ⟨x, hx, hxe⟩ := hpt u hu
    rw [hxe, Complex.mem_slitPlane_iff]; left
    exact (riemannXi_pos_of_mem_Icc hx).1
  have harg : ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 2 → (riemannXi (x : ℂ)).arg = 0 := by
    intro x hx
    rw [Complex.arg_eq_zero_iff]
    exact ⟨(riemannXi_pos_of_mem_Icc hx).1.le, (riemannXi_pos_of_mem_Icc hx).2⟩
  obtain ⟨x0, hx0, hx0e⟩ := hpt 0 (by norm_num)
  obtain ⟨x1, hx1, hx1e⟩ := hpt 1 (by norm_num)
  rw [lineSeg_zero] at hx0e
  rw [lineSeg_one] at hx1e
  rw [argVariation_eq_arg_sub_arg zero_le_one (riemannXi_lineSeg_continuousOn z₀ z₁) hsp]
  simp only [lineSeg_one, lineSeg_zero]
  rw [hx0e, hx1e, harg hx0, harg hx1]
  ring
theorem argVariation_riemannXi_rectangle_eq_two_mul {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ))
      = 2 * argVariationContourL riemannXi T := by
  have c0 : ((↑(-1 : ℂ).re : ℂ) + ↑(-1 : ℂ).im * I) = (-1 : ℂ) := Complex.re_add_im _
  have c1 : ((↑(2 + I * (T : ℂ)).re : ℂ) + ↑(-1 : ℂ).im * I) = 2 := by apply Complex.ext <;> simp
  have c2 : ((↑(2 + I * (T : ℂ)).re : ℂ) + ↑(2 + I * (T : ℂ)).im * I) = 2 + I * (T : ℂ) :=
    Complex.re_add_im _
  have c3 : ((↑(-1 : ℂ).re : ℂ) + ↑(2 + I * (T : ℂ)).im * I) = -1 + I * (T : ℂ) := by
    apply Complex.ext <;> simp
  have hne_right : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg 2 (2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_re_eq_two (by simp) (by simp)
  have hne_right' : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg (2 + I * (T : ℂ)) 2 u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_re_eq_two (by simp) (by simp)
  have hne_s2 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_s2' : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_top : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_bot : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg (-1) 2 u) ≠ 0 := by
    intro u hu
    have hpt : lineSeg (-1 : ℂ) 2 u = ((-1 + u * 3 : ℝ) : ℂ) := by
      simp only [lineSeg]; push_cast; ring
    rw [hpt]; intro h
    have hmem : (-1 + u * 3 : ℝ) ∈ Icc (-1 : ℝ) 2 := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    have := (riemannXi_pos_of_mem_Icc hmem).1
    rw [h] at this; simp at this
  have hsplit_bot : argVariation 0 1 (fun u => riemannXi (lineSeg (-1) 2 u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (-1) (1 / 2) u))
        + argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2) 2 u)) := by
    have h := argVariation_lineSeg_split (f := riemannXi) (-1) 2 (t := 1 / 2)
      (by norm_num) (by norm_num) (riemannXi_lineSeg_continuousOn _ _) hne_bot
    rw [show lineSeg (-1 : ℂ) 2 (1 / 2) = (1 / 2 : ℂ) from by
      simp only [lineSeg]; push_cast; ring] at h
    exact h
  have hsplit_top :
      argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u))
        + argVariation 0 1
            (fun u => riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u)) := by
    have h := argVariation_lineSeg_split (f := riemannXi) (2 + I * (T : ℂ)) (-1 + I * (T : ℂ))
      (t := 1 / 2) (by norm_num) (by norm_num) (riemannXi_lineSeg_continuousOn _ _) hne_top
    rw [show lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) (1 / 2) = (1 / 2 + I * (T : ℂ)) from by
      simp only [lineSeg]; push_cast; ring] at h
    exact h
  have hbot1 : argVariation 0 1 (fun u => riemannXi (lineSeg (-1) (1 / 2) u)) = 0 :=
    argVariation_riemannXi_real_eq_zero fun u hu =>
      ⟨-1 + u * (3 / 2), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, by
        simp only [lineSeg]; push_cast; ring⟩
  have hbot2 : argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2) 2 u)) = 0 :=
    argVariation_riemannXi_real_eq_zero fun u hu =>
      ⟨1 / 2 + u * (3 / 2), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, by
        simp only [lineSeg]; push_cast; ring⟩
  have hleft : argVariation 0 1 (fun u => riemannXi (lineSeg (-1 + I * (T : ℂ)) (-1) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg 2 (2 + I * (T : ℂ)) u)) := by
    have hreflect := argVariation_lineSeg_reflect (z₀ := 2 + I * (T : ℂ)) (z₁ := 2)
      (riemannXi_lineSeg_continuousOn _ _) hne_right'
    have hswap := argVariation_lineSeg_swap (f := riemannXi) 2 (2 + I * (T : ℂ))
      (riemannXi_lineSeg_continuousOn _ _) hne_right
    rw [show (1 - starRingEnd ℂ (2 + I * (T : ℂ))) = -1 + I * (T : ℂ) from by
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring,
        show (1 - starRingEnd ℂ (2 : ℂ)) = (-1 : ℂ) from by
          simp only [map_ofNat]; norm_num] at hreflect
    rw [hreflect, hswap]; ring
  have hs2' :
      argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u))
      := by
    have hreflect := argVariation_lineSeg_reflect (z₀ := 1 / 2 + I * (T : ℂ))
      (z₁ := 2 + I * (T : ℂ)) (riemannXi_lineSeg_continuousOn _ _) hne_s2'
    have hswap := argVariation_lineSeg_swap (f := riemannXi) (2 + I * (T : ℂ))
      (1 / 2 + I * (T : ℂ)) (riemannXi_lineSeg_continuousOn _ _) hne_s2
    rw [show (1 - starRingEnd ℂ (1 / 2 + I * (T : ℂ))) = 1 / 2 + I * (T : ℂ) from by
          simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
            map_ofNat]; ring,
        show (1 - starRingEnd ℂ (2 + I * (T : ℂ))) = -1 + I * (T : ℂ) from by
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat];
          ring] at hreflect
    rw [hreflect, hswap]; ring
  rw [rectangleArgVariation, c0, c1, c2, c3]
  simp only [argVariationContourL]
  rw [hsplit_bot, hsplit_top, hbot1, hbot2, hleft, hs2']
  ring
end
end CertificatePort36
section CertificatePort37
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev
noncomputable abbrev nth_prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
noncomputable abbrev nth_prime' (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)
noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x
noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)
noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ :=
  nth_prime (n + 1) - nth_prime n
def prime_gap_record (p g : ℕ) : Prop :=
  ∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧
    ∀ k, nth_prime k < p → nth_prime_gap k < g
open Classical in
noncomputable def first_gap (g : ℕ) : ℕ :=
  if h : ∃ n, nth_prime_gap n = g then
    nth_prime (Nat.find h)
  else 0
def first_gap_record (g P : ℕ) : Prop :=
  first_gap g = P ∧
    ∀ g' ∈ Finset.Ico 1 g,
      Even g' ∨ g' = 1 → first_gap g' ∈ Set.Ico 1 P
def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h
def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k + 1 : ℝ))) / (k + 1 : ℝ)
noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x
noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x
def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε
def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eψ.bound (ε x₀) x₀
noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)
noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x
def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ ε x₀
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x
def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε
def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ.bound (ε x₀) x₀
def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))
def Eπ_star.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ admissible_bound A B C R x
def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε
def Eπ_star.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ_star.bound (ε x₀) x₀
def Eπ_star.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))
lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]
end
end CertificatePort37
section CertificatePort38
section
open Real
noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}
noncomputable def riemannZeta.zeroes_rect (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zeroes}
lemma riemannZeta.zeroes_rect_eq (I J : Set ℝ) :
    zeroes_rect I J = (Complex.re ⁻¹' I ∩ Complex.im ⁻¹' J) ∩ zeroes := by
  ext x; simp only [zeroes_rect, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_preimage, and_assoc]
section
lemma riemannZeta_differentiableOn_compl_one :
    DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt
lemma riemannZeta_analyticOn_compl_one :
    AnalyticOnNhd ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  riemannZeta_differentiableOn_compl_one.analyticOnNhd isOpen_compl_singleton
lemma riemannZeta.zeroes_codiscreteWithin_compl_one :
    zeroesᶜ ∈ Filter.codiscreteWithin ({1} : Set ℂ)ᶜ := by
  refine riemannZeta_analyticOn_compl_one.preimage_zero_mem_codiscreteWithin
    ?_ ?_ ?_ (x := 2)
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact Set.mem_compl_singleton_iff.2 (OfNat.one_ne_ofNat 2).symm
  · refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
lemma riemannZeta.zeroes_on_Compact_finite {S : Set ℂ} (hS1 : IsCompact S) (hS2 : 1 ∉ S) :
    (S ∩ zeroes : Set ℂ).Finite := by
  have sub := Set.subset_compl_singleton_iff.mpr hS2
  refine IsCompact.finite ?_ ?_
  · have := riemannZeta_analyticOn_compl_one.continuousOn.mono sub
      |>.preimage_isClosed_of_isClosed (t := {0}) hS1.isClosed isClosed_singleton
    exact hS1.of_isClosed_subset this Set.inter_subset_left
  · rw [Set.inter_comm]
    exact IsDiscrete.mono (isDiscrete_of_codiscreteWithin zeroes_codiscreteWithin_compl_one)
      <| Set.inter_subset_inter_right zeroes sub
open Topology in
lemma riemannZeta_eventually_ne_zero :
    ∀ᶠ s in 𝓝[≠] 1, riemannZeta s ≠ 0 := by
  filter_upwards [riemannZeta_residue_one.eventually_ne (zero_ne_one' ℂ).symm,
    eventually_nhdsWithin_of_forall (fun _ hs ↦ hs)] with s hmul hne
  intro hzero
  rw [hzero, mul_zero] at hmul
  exact false_of_ne hmul
lemma riemannZeta_no_zeroes_near_one : ∃ ε, ε > 0 ∧ ∀ s,
    s ∈ Metric.ball 1 ε → riemannZeta s ≠ 0 := by
  obtain ⟨ε, hε_pos, hball⟩ := Metric.eventually_nhds_iff.1 <|
      eventually_nhdsWithin_iff.1 riemannZeta_eventually_ne_zero
  refine ⟨ε, hε_pos, fun s hs hzero ↦ ?_⟩
  by_cases h : s = 1
  · exact riemannZeta_one_ne_zero (h ▸ hzero)
  · exact hball (Metric.mem_ball.1 hs) (Set.mem_compl_singleton_iff.2 h) hzero
lemma riemannZeta.zeroes_on_Compact_finite' {S : Set ℂ} (hS1 : IsCompact S) :
    (S ∩ zeroes : Set ℂ).Finite := by
  obtain ⟨ε, hε, hball⟩ := riemannZeta_no_zeroes_near_one
  have : S ∩ zeroes ⊆ (S ∩ (Metric.ball 1 ε)ᶜ) ∩ zeroes :=
    fun s ⟨hs, hz⟩ ↦ ⟨⟨hs, fun hmem ↦ hball s hmem hz⟩, hz⟩
  refine Set.Finite.subset (zeroes_on_Compact_finite ?_ ?_) this
  · exact hS1.inter_right Metric.isOpen_ball.isClosed_compl
  · exact fun ⟨_, h⟩ ↦ h (Metric.mem_ball_self hε)
end
noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).untopD 0
noncomputable def riemannZeta.zeroes_sum {α : Type*} [RCLike α]
    (I J : Set ℝ) (f : ℂ → α) : α :=
  ∑' ρ : riemannZeta.zeroes_rect I J, (f ρ) * (riemannZeta.order ρ)
noncomputable def riemannZeta.RH_up_to (T : ℝ) : Prop :=
  IsEmpty (riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Icc 0 T))
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) :=
  ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 - 1 / (R * log t) →
  riemannZeta (σ + t * Complex.I) ≠ 0
noncomputable def riemannZeta.N (T : ℝ) : ℝ := zeroes_sum Set.univ (Set.Ioo 0 T) (fun _ ↦ 1)
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1
noncomputable def riemannZeta.RvM (b₁ b₂ b₃ T : ℝ) : ℝ :=
  b₁ * log T + b₂ * log (log T) + b₃
def riemannZeta.Riemann_vonMangoldt_bound (b₁ b₂ b₃ : ℝ) : Prop :=
  ∀ T ≥ 2, |riemannZeta.N T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
    RvM b₁ b₂ b₃ T
structure zero_density_bound where
  T₀ : ℝ
  σ_range : Set ℝ
  c₁ : ℝ → ℝ
  c₂ : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  bound : ∀ T ≥ T₀, ∀ σ ∈ σ_range,
      riemannZeta.N' σ T ≤ (c₁ σ) * T ^ (p σ) * (log T) ^ (q σ) + (c₂ σ) * (log T) ^ 2
noncomputable def zero_density_bound.N {ZDB : zero_density_bound} (σ T : ℝ) : ℝ :=
  (ZDB.c₁ σ) * T ^ (ZDB.p σ) * (log T) ^ (ZDB.q σ) + (ZDB.c₂ σ) * (log T) ^ 2
end
end CertificatePort38
section CertificatePort39
public section
open scoped Complex ComplexConjugate
set_option backward.isDefEq.respectTransparency false in
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
end
end CertificatePort39
section CertificatePort40
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
public section
open scoped BigOperators
namespace Real
lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring
end Real
namespace Complex
open scoped BigOperators in
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]
noncomputable
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)
@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum, logTaylor_succ, logTaylor_zero]
@[simp]
lemma partialLogSum_at_zero (m : ℕ) : partialLogSum m 0 = 0 := by
  simp [partialLogSum, logTaylor_at_zero]
lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel
lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf
lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)
lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)
lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt
noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)
lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [logTail]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]
lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)
lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf
end Complex
end
end CertificatePort40
section CertificatePort41
public section
noncomputable section
namespace Complex
variable {z : ℂ}
@[bound]
theorem neg_norm_le_re (z : ℂ) : -‖z‖ ≤ z.re :=
  neg_le_of_abs_le (abs_re_le_norm z)
end Complex
end
end
end CertificatePort41
section CertificatePort42
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
public section
noncomputable section
open scoped BigOperators
open Set
namespace Complex
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)
@[simp]
lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]
@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]
@[simp]
lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]
lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))
lemma hasDerivAt_weierstrassFactor_at_one (m : ℕ) :
    HasDerivAt (weierstrassFactor m) (-Complex.exp (partialLogSum m 1)) 1 := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa using! (hasDerivAt_const (1 : ℂ) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (partialLogSum m z))
        ((∑ j ∈ Finset.range m, (1 : ℂ) ^ j) * Complex.exp (partialLogSum m 1)) 1 := by
    simpa [mul_comm] using!
      (Complex.hasDerivAt_exp (partialLogSum m 1)).comp 1 (hasDerivAt_partialLogSum m 1)
  simpa [weierstrassFactor] using! hsub.mul hexp
@[simp]
lemma deriv_weierstrassFactor_at_one (m : ℕ) :
    deriv (weierstrassFactor m) 1 = -Complex.exp (partialLogSum m 1) :=
  (hasDerivAt_weierstrassFactor_at_one m).deriv
lemma hasDerivAt_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ weierstrassFactor m (z / a))
      ((-Complex.exp (partialLogSum m 1)) / a) a := by
  have hcomp :
      HasDerivAt ((weierstrassFactor m) ∘ fun z : ℂ ↦ z / a)
        ((-Complex.exp (partialLogSum m 1)) * (1 / a)) a :=
    HasDerivAt.comp (x := a) (h := fun z : ℂ ↦ z / a) (h₂ := weierstrassFactor m)
      (by simpa [ha] using hasDerivAt_weierstrassFactor_at_one m)
      ((hasDerivAt_id a).div_const a)
  simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using! hcomp
@[simp]
lemma deriv_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a =
      (-Complex.exp (partialLogSum m 1)) / a :=
  (hasDerivAt_weierstrassFactor_div_at_self m ha).deriv
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring
private lemma eventually_le_norm_div_two_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hεpos : 0 < (1 / (2 * R) : ℝ) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by positivity
      exact one_div_pos.mpr this
    exact pow_pos this _
  filter_upwards [htend.eventually (eventually_lt_nhds hεpos)] with n hn
  by_contra h
  have hlt : ‖a n‖ / 2 < R := lt_of_not_ge h
  have hle : ‖a n‖ ≤ 2 * R := by nlinarith
  have hanorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hanorm_pos hle)
  have hpow :
      (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  exact (not_lt_of_ge hpow) hn
private lemma summable_scaled_bound_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) :
    ∀ R ≥ 0, Summable (fun n : ℕ => 4 * R ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
  intro R _hR
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
    h_sum.mul_left (4 * R ^ (m + 1))
lemma continuousOn_weierstrassFactor_div (m : ℕ) (a : ℂ) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ ↦ weierstrassFactor m (z / a)) s := by
  simpa using! (differentiable_weierstrassFactor m).continuous.continuousOn.comp
    (continuous_id.div_const a).continuousOn (mapsTo_univ (fun z : ℂ ↦ z / a) s)
lemma norm_weierstrassFactor_div_sub_one_le_pow_div (m : ℕ) {a z : ℂ}
    (hza : ‖z‖ ≤ ‖a‖ / 2) :
    ‖weierstrassFactor m (z / a) - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by
  by_cases ha : a = 0
  · have hz : z = 0 := by
      apply norm_eq_zero.mp
      rw [ha] at hza
      simpa using hza
    subst z
    simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hza' : ‖z / a‖ ≤ 1 / 2 := by
      rw [Complex.norm_div, div_le_iff₀ ha']
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hza
    have hbase := weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a) hza'
    calc
      ‖weierstrassFactor m (z / a) - 1‖ ≤ ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) * 4 := by
        simpa [Complex.norm_div, div_pow, mul_comm, mul_left_comm, mul_assoc] using hbase
      _ = 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by ring
lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    refine (norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) ?_).trans ?_
    · exact (hR z hz).trans hn
    · have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    exact (continuousOn_weierstrassFactor_div (m n) (a n) K).fun_sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts
lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)
lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero)
      (summable_scaled_bound_of_summable_inv_pow h_sum)
end Complex
end
end
end CertificatePort42
section CertificatePort43
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
noncomputable section
open Filter Topology
namespace Complex
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)
@[simp] theorem canonicalProduct_def (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl
theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using!
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero
theorem multipliableLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliableLocallyUniformlyOn
@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    canonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) Filter.atTop
        (𝓝 (canonicalProduct m a (a n))) := by
    simpa [f, canonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[Filter.atTop] fun _ ↦ (0 : ℂ) := by
    refine Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero
end Complex
end
end
end CertificatePort43
section CertificatePort44
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Filter Topology Set
namespace MeromorphicOn
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub
end MeromorphicOn
end
end CertificatePort44
section CertificatePort45
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Set
namespace Complex.Hadamard
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1
@[simp]
lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2
@[simp]
lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
    simp [hdiv]
  exact hn this
noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  simp [divisorCanonicalProduct]
end Complex.Hadamard
end
end CertificatePort45
section CertificatePort46
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
namespace Complex
section UniformMul
end UniformMul
end Complex
end
end CertificatePort46
section CertificatePort47
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀_val p.1, by
        have hball : divisorZeroIndex₀_val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀_val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀_val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : divisorZeroIndex₀_val p.1 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2
lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀_val p‖ ≤ B}
  have : Finite (↥s) :=
    finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU
  exact Set.toFinite s
end Complex.Hadamard
end
end CertificatePort47
section CertificatePort48
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end CertificatePort48
section CertificatePort49
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
noncomputable section
open Set
open scoped Topology BigOperators
namespace Complex.Hadamard
theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub
def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset
@[simp]
lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  simp [divisorZeroIndex₀_fiberFinset]
end Complex.Hadamard
end
end
end CertificatePort49
section CertificatePort50
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
    else weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
theorem divisorComplementFactor_eq_one_of_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z = 1 := by
  classical
  simp [divisorComplementFactor, hp]
@[simp]
theorem divisorComplementFactor_eq_weierstrassFactor_of_not_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z =
      weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  simp [divisorComplementFactor, hp]
noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
lemma divisorPartialProduct_def (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorPartialProduct m f s z = ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
  rfl
noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, divisorComplementFactor m f z₀ p z
@[simp]
lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s, if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  simp [divisorComplementPartialProduct, divisorComplementFactor,
    mem_divisorZeroIndex₀_fiberFinset]
noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), divisorComplementFactor m f z₀ p z
end Complex.Hadamard
end
end CertificatePort50
section CertificatePort51
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
noncomputable section
open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end
end CertificatePort51
section CertificatePort52
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
open Filter
end Complex.Hadamard
end
end CertificatePort52
section CertificatePort53
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end CertificatePort53
section CertificatePort54
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
namespace Complex.Hadamard
open scoped Topology
open Set
end Hadamard
end Complex
end
end CertificatePort54
section CertificatePort55
/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
section
open Set
open scoped ENNReal
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
def annulusIoo (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioo r R
def annulusIoc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioc r R
def annulusIco (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ico r R
def annulusIcc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Icc r R
def annulusIoi (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioi r
def annulusIci (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ici r
variable {x : X} {r R : ℝ}
@[simp] lemma annulusIoo_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoo x r R = ∅ := by
  simp [annulusIoo, Ioo_eq_empty_of_le h]
@[simp] lemma annulusIoc_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoc x r R = ∅ := by
  simp [annulusIoc, Ioc_eq_empty_of_le h]
@[simp] lemma annulusIco_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIco x r R = ∅ := by
  simp [annulusIco, Ico_eq_empty_of_le h]
@[simp] lemma annulusIcc_eq_empty {x : X} {r R : ℝ} (h : R < r) : annulusIcc x r R = ∅ := by
  simp [annulusIcc, Icc_eq_empty_of_lt h]
@[gcongr]
lemma annulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoo x r₁ R₁ ⊆ annulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma annulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoc x r₁ R₁ ⊆ annulusIoc x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩
@[gcongr]
lemma annulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIco x r₁ R₁ ⊆ annulusIco x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma annulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIcc x r₁ R₁ ⊆ annulusIcc x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, hy.2.trans hR⟩
@[simp]
lemma annulusIoc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIoc x r r' ∪ annulusIoo x r' R = annulusIoo x r R := by
  simpa [annulusIoc, annulusIoo, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioo_eq_Ioo h₁ h₂)
@[simp]
lemma annulusIoc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIoc x r r' ∪ annulusIoc x r' R = annulusIoc x r R := by
  simpa [annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioc_eq_Ioc h₁ h₂)
@[simp]
lemma annulusIoo_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIco x r' R = annulusIoo x r R := by
  simpa [annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ico_eq_Ioo h₁ h₂)
@[simp]
lemma annulusIoo_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIcc x r' R = annulusIoc x r R := by
  simpa [annulusIoo, annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Icc_eq_Ioc h₁ h₂)
@[simp]
lemma annulusIcc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIcc x r r' ∪ annulusIoo x r' R = annulusIco x r R := by
  simpa [annulusIcc, annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioo_eq_Ico h₁ h₂)
@[simp]
lemma annulusIcc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIcc x r r' ∪ annulusIoc x r' R = annulusIcc x r R := by
  simpa [annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioc_eq_Icc h₁ h₂)
@[simp]
lemma annulusIco_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIco x r' R = annulusIco x r R := by
  simpa [annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ico_eq_Ico h₁ h₂)
@[simp]
lemma annulusIco_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIcc x r' R = annulusIcc x r R := by
  simpa [annulusIco, annulusIcc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Icc_eq_Icc h₁ h₂)
@[simp]
lemma annulusIoc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIoc x r R ∪ annulusIoi x R = annulusIoi x r := by
  simpa [annulusIoc, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioi_eq_Ioi h)
@[simp]
lemma annulusIoo_union_annulusIci {x : X} {r R : ℝ} (h : r < R) :
    annulusIoo x r R ∪ annulusIci x R = annulusIoi x r := by
  simpa [annulusIoo, annulusIci, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ici_eq_Ioi h)
@[simp]
lemma annulusIcc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIcc x r R ∪ annulusIoi x R = annulusIci x r := by
  simpa [annulusIcc, annulusIoi, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioi_eq_Ici h)
@[simp]
lemma annulusIco_union_annulusIci {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIco x r R ∪ annulusIci x R = annulusIci x r := by
  simpa [annulusIco, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ici_eq_Ici h)
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
def eannulusIoo (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioo r R
def eannulusIoc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioc r R
def eannulusIco (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ico r R
def eannulusIcc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Icc r R
def eannulusIoi (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioi r
def eannulusIci (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ici r
@[simp] lemma eannulusIoo_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoo x r R = (fun y : X ↦ edist y x) ⁻¹' Ioo r R := rfl
@[simp] lemma eannulusIoc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoc x r R = (fun y : X ↦ edist y x) ⁻¹' Ioc r R := rfl
@[simp] lemma eannulusIco_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIco x r R = (fun y : X ↦ edist y x) ⁻¹' Ico r R := rfl
@[simp] lemma eannulusIcc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIcc x r R = (fun y : X ↦ edist y x) ⁻¹' Icc r R := rfl
@[simp] lemma eannulusIoi_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIoi x r = (fun y : X ↦ edist y x) ⁻¹' Ioi r := rfl
@[simp] lemma eannulusIci_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIci x r = (fun y : X ↦ edist y x) ⁻¹' Ici r := rfl
@[gcongr]
lemma eannulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoo x r₁ R₁ ⊆ eannulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma eannulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoc x r₁ R₁ ⊆ eannulusIoc x r₂ R₂ := by
  intro y hy; exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩
@[gcongr]
lemma eannulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIco x r₁ R₁ ⊆ eannulusIco x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma eannulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIcc x r₁ R₁ ⊆ eannulusIcc x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, hy.2.trans hR⟩
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}
end Metric
end
end CertificatePort55
section CertificatePort56
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
namespace Complex.Hadamard
open Filter Topology Set Complex
open scoped BigOperators Topology
noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z
noncomputable def centeredHadamardDenom (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - c) ^ (analyticOrderNatAt f c) *
    divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c)
noncomputable def centeredHadamardQuotient (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / centeredHadamardDenom m c f z
@[simp]
theorem centeredHadamardDenom_center_eq_one {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c = 0) :
    centeredHadamardDenom m c f c = 1 := by
  simp [centeredHadamardDenom, h, sub_self, divisorCanonicalProduct_zero, pow_zero]
@[simp]
theorem centeredHadamardDenom_center_eq_zero {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c ≠ 0) : centeredHadamardDenom m c f c = 0 := by
  have hn : 0 < analyticOrderNatAt f c := by
    exact Nat.pos_of_ne_zero h
  simp [centeredHadamardDenom, sub_self, zero_pow hn.ne']
end Complex.Hadamard
end
end CertificatePort56
section CertificatePort57
/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Matteo Cipollina
-/
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
end Function.locallyFinsuppWithin
end
end CertificatePort57
section CertificatePort58
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
namespace Real
end Real
end
end CertificatePort58
section CertificatePort59
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
namespace Real
end Real
end
end CertificatePort59
section CertificatePort60
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
variable {F : Type*} [NormedAddCommGroup F]
open Metric Complex
end Real
end
end CertificatePort60
section CertificatePort61
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
end Function.locallyFinsuppWithin
end
end CertificatePort61
section CertificatePort62
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
end CertificatePort62
section CertificatePort63
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
noncomputable section
open scoped BigOperators
open Filter
namespace Real
end Real
end
end
end CertificatePort63
section CertificatePort64
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
section
noncomputable section
open Filter Topology Set Complex
open scoped BigOperators Topology
namespace Complex.Hadamard
open scoped Real
noncomputable def divisorMassClosedBall₀ (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.massClosedBall₀ (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
open scoped BigOperators
end Complex.Hadamard
end
end
end CertificatePort64
section CertificatePort65
/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
section
open Real Complex Function
namespace Backlund
noncomputable def zetaSurrogate (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s
end Backlund
end
end CertificatePort65
section CertificatePort66
section
noncomputable section
namespace Kadiri
open Complex Filter
abbrev NontrivialZeros : Set ℂ :=
  riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)
def riemannZetaConjZeroSource : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → riemannZeta ((starRingEnd ℂ) z) = 0
def positiveHeightNontrivialZeroEquivZeroesRect (T : ℝ) :
    {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < T} ≃
      riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T) where
  toFun rho :=
    ⟨(rho : ℂ),
      rho.1.property.1,
      by exact ⟨rho.2.1, rho.2.2⟩,
      rho.1.property.2.2⟩
  invFun rho :=
    ⟨⟨(rho : ℂ),
        rho.property.1,
        Set.mem_univ _,
        rho.property.2.2⟩,
      by exact ⟨rho.property.2.1.1, rho.property.2.1.2⟩⟩
  left_inv rho := by
    ext
    rfl
  right_inv rho := by
    ext
    rfl
lemma zeroes_rect_Ioo_critical_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (0 : ℝ) T)
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩, hzeta⟩
lemma positiveHeightZero_ne_one {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ) ≠ 1 := by
  intro h
  have him : (rho : ℂ).im ∈ Set.Ioo (0 : ℝ) T := rho.property.2.1
  rw [h] at him
  norm_num at him
lemma riemannZeta_analyticAt_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) := by
  exact riemannZeta_analyticOn_compl_one (rho : ℂ)
    (by simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho)
lemma riemannZeta_positiveHeightZero_zero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    riemannZeta (rho : ℂ) = 0 := by
  exact rho.property.2.2
lemma riemannZeta_eventually_ne_zero_punctured_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : (rho : ℂ) ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho
  have hdisj : Disjoint (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (𝓟 (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      (rho : ℂ) hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩
lemma riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    meromorphicOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (riemannZeta_eventually_ne_zero_punctured_positiveHeightZero rho)
lemma riemannZeta_order_pos_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    0 < riemannZeta.order (rho : ℂ) := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  have hzero := riemannZeta_positiveHeightZero_zero rho
  have horder_ne_top := riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero rho
  have hanOrder_ne_zero : analyticOrderAt riemannZeta (rho : ℂ) ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_natCast, WithTop.untopD_coe]
      exact_mod_cast hn_pos
lemma riemannZeta_one_le_order_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (1 : ℤ) ≤ riemannZeta.order (rho : ℂ) := by
  exact_mod_cast riemannZeta_order_pos_positiveHeightZero rho
lemma riemannZeta_one_sub_ne_zero_of_one_le_re {w : ℂ}
    (hw_re : 1 ≤ w.re) (hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0) :
    riemannZeta (1 - w) ≠ 0 := by
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre' : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre'] at hw_re; linarith
  have hw_ne_one : w ≠ 1 := by
    rintro rfl
    refine hcos ?_
    have h2 : (↑Real.pi * (1 : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_neg_nat
  have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos) hzeta_w
lemma riemannZeta_ne_zero_of_re_nonpos_im_ne_zero {z : ℂ}
    (hre : z.re ≤ 0) (him : z.im ≠ 0) : riemannZeta z ≠ 0 := by
  set w : ℂ := 1 - z with hw
  have hw_im : w.im ≠ 0 := by rw [hw]; simp [him]
  have hw_re : 1 ≤ w.re := by rw [hw]; simp; linarith
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hleft : (↑Real.pi * w / 2).im ≠ 0 := by
      rw [show (↑Real.pi * w / 2).im = Real.pi * w.im / 2 by
        simp [div_eq_mul_inv, mul_assoc]]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hw_im) two_ne_zero
    have hright : (((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im) = 0 := by
      simp [div_eq_mul_inv, mul_assoc]
    exact hleft (by rw [hk, hright])
  have hres := riemannZeta_one_sub_ne_zero_of_one_le_re hw_re hcos
  rwa [show (1 : ℂ) - w = z by rw [hw]; ring] at hres
lemma positiveHeightZero_re_mem_Ioo {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := by
  have him_pos : 0 < (rho : ℂ).im := rho.property.2.1.1
  have hzeta : riemannZeta (rho : ℂ) = 0 := rho.property.2.2
  have hnot_re_nonpos : ¬ (rho : ℂ).re ≤ 0 := by
    intro hre
    exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hre him_pos.ne') hzeta
  have hre_pos : 0 < (rho : ℂ).re := lt_of_not_ge hnot_re_nonpos
  have hnot_re_one_le : ¬ 1 ≤ (rho : ℂ).re := by
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
  have hre_lt_one : (rho : ℂ).re < 1 := lt_of_not_ge hnot_re_one_le
  exact ⟨hre_pos, hre_lt_one⟩
lemma zeroes_rect_univ_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).Finite := by
  have hsub :
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) ⊆
        riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo 0 T) := by
    intro z hz
    exact ⟨positiveHeightZero_re_mem_Ioo ⟨z, hz⟩, hz.2.1, hz.2.2⟩
  exact (zeroes_rect_Ioo_critical_positive_height_finite T).subset hsub
abbrev ZeroHeightNontrivialZeros : Type :=
  {rho : NontrivialZeros // (rho : ℂ).im = 0}
def zeroHeightNontrivialZeroEquivZeroesRectZero :
    ZeroHeightNontrivialZeros ≃
      riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc 0 0) where
  toFun rho :=
    ⟨(rho : ℂ),
      rho.1.property.1,
      by simp [rho.2],
      rho.1.property.2.2⟩
  invFun rho :=
    ⟨⟨(rho : ℂ),
        rho.property.1,
        Set.mem_univ _,
        rho.property.2.2⟩,
      by exact le_antisymm rho.property.2.1.2 rho.property.2.1.1⟩
  left_inv rho := by
    ext
    rfl
  right_inv rho := by
    ext
    rfl
def zeroSquareTail (a : ℂ) (rho : NontrivialZeros) : ℝ :=
  (‖a - (rho : ℂ)‖)⁻¹ ^ (2 : ℕ)
def zeroSquareTailSummable (a : ℂ) : Prop :=
  Summable (fun rho : NontrivialZeros ↦ zeroSquareTail a rho)
def zeroImagSquareTail (rho : NontrivialZeros) : ℝ :=
  |(rho : ℂ).im|⁻¹ ^ (2 : ℕ)
def zeroImagSquareTailSummable : Prop :=
  Summable (fun rho : NontrivialZeros ↦ zeroImagSquareTail rho)
def zeroHeightDyadicShell (k : ℕ) (rho : NontrivialZeros) : Prop :=
  (2 : ℝ) ^ k ≤ |(rho : ℂ).im| ∧ |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)
def zeroImagDyadicShellSummableSource : Prop :=
  Summable
    (fun p : Sigma (fun k : ℕ =>
        {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) =>
      zeroImagSquareTail p.2.1)
def zeroHeightDyadicShellMass (k : ℕ) : ℝ :=
  ∑' rho : {rho : NontrivialZeros // zeroHeightDyadicShell k rho},
    zeroImagSquareTail rho.1
def zeroImagDyadicShellCountBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros // zeroHeightDyadicShell k rho} : ℝ) ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zeroImagDyadicCumulativeCountBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zetaCountingMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
def zetaCountingBacklundMajorant (b₁ b₂ b₃ T : ℝ) : ℝ :=
  |zetaCountingMainTerm T| + riemannZeta.RvM b₁ b₂ b₃ T
def zetaCountingDyadicMajorant (b₁ b₂ b₃ : ℝ) (k : ℕ) : ℝ :=
  zetaCountingBacklundMajorant b₁ b₂ b₃ ((2 : ℝ) ^ (k + 1))
def zetaCountingMainTermDyadicGrowthSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    |zetaCountingMainTerm ((2 : ℝ) ^ (k + 1))| ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zetaCountingDyadicMajorantGrowthSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    zetaCountingDyadicMajorant 0.137 0.443 6.1 k ≤
      C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
def zeroImagDyadicCumulativeCountByNSource : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))|
def zeroImagDyadicCumulativeCountByNWithZeroHeightSource : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D
def zeroImagDyadicAbsToPositiveCountSource : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ)
def zeroImagDyadicAbsToPositiveCountWithZeroHeightSource : Prop :=
  ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ,
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
      A * (Nat.card {rho : NontrivialZeros //
        0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) + D
def zeroImagDyadicNPrimeToNSource : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
    |riemannZeta.N' 0 ((2 : ℝ) ^ (k + 1))| ≤
      B * |riemannZeta.N ((2 : ℝ) ^ (k + 1))|
def zeroImagDyadicNOrderSummableSource : Prop :=
  ∀ k : ℕ,
    Summable (fun rho : riemannZeta.zeroes_rect (.univ : Set ℝ)
        (.Ioo 0 ((2 : ℝ) ^ (k + 1))) =>
      (riemannZeta.order (rho : ℂ) : ℝ))
def zeroImagDyadicShellMassBoundSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
    zeroHeightDyadicShellMass k ≤ C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k
def highZeroToDyadicShell (rho : {rho : NontrivialZeros // 1 ≤ |(rho : ℂ).im|}) :
    Sigma (fun k : ℕ => {rho : NontrivialZeros // zeroHeightDyadicShell k rho}) :=
  let hnear := exists_nat_pow_near
    (x := |((rho.1 : ℂ).im)|) (y := (2 : ℝ)) rho.2 (by norm_num)
  ⟨hnear.choose, ⟨rho.1, hnear.choose_spec⟩⟩
def dyadicShellToCumulative (k : ℕ) :
    {rho : NontrivialZeros // zeroHeightDyadicShell k rho} →
      {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} :=
  fun rho => ⟨rho.1, rho.2.2⟩
noncomputable def weightedZeroHeightBucket : ℝ :=
  ∑' ρ : ZeroHeightNontrivialZeros,
    ((riemannZeta.order ((ρ : NontrivialZeros) : ℂ) : ℤ) : ℝ)
end Kadiri
end
end
end CertificatePort66
section CertificatePort67
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex
theorem riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero {s : ℂ}
    (hz : riemannZeta s = 0) (him : s.im ≠ 0) : s.re ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨not_le.mp fun h ↦ Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero h him hz,
    not_le.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
theorem riemannZeta.N_eq_tsum_riemannXi_order (T : ℝ) :
    riemannZeta.N T =
      ∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
        (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
  have hset : riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T) =
      {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    constructor
    · rintro ⟨-, hzim, hzero⟩
      have hre := riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne'
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨(riemannXi_eq_zero_iff hre0 hre1).mpr hzero, hre, hzim⟩
    · rintro ⟨hxi, hre, hzim⟩
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨Set.mem_univ _, hzim, (riemannXi_eq_zero_iff hre0 hre1).mp hxi⟩
  calc riemannZeta.N T
      = ∑' ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)),
          (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
        simp only [riemannZeta.N, riemannZeta.zeroes_sum]
        refine tsum_congr fun ρ ↦ ?_
        obtain ⟨-, hzim, hzero⟩ := ρ.property
        obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp
          (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne')
        simp only [one_mul, riemannZeta.order,
          meromorphicOrderAt_riemannXi_eq_riemannZeta hre0 hre1]
    _ = _ := (Equiv.setCongr hset).tsum_eq
        (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
private theorem eq_ofReal_re_add_I_mul {T : ℝ} {z : ℂ} (hz : z.im = T) :
    z = (↑z.re : ℂ) + Complex.I * (T : ℂ) := by
  apply Complex.ext <;> simp [hz]
theorem riemannZeta_ne_zero_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0 := by
  intro s hs hz0
  have him : s.im ≠ 0 := by rw [hs]; exact hT.ne'
  obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hz0 him)
  have hxi : riemannXi s = 0 := (riemannXi_eq_zero_iff hre0 hre1).mpr hz0
  rcases le_or_gt (1 / 2 : ℝ) s.re with hge | hlt
  ·
    apply h s.re ⟨hge, hre1⟩
    rw [← eq_ofReal_re_add_I_mul hs]; exact hz0
  ·
    set w : ℂ := 1 - starRingEnd ℂ s with hw
    have hxi_w : riemannXi w = 0 := by
      rw [hw, riemannXi_one_sub, riemannXi_conj, hxi, map_zero]
    have hw_re : w.re = 1 - s.re := by simp [hw]
    have hw_im : w.im = T := by rw [hw]; simp [hs]
    apply h w.re ⟨by rw [hw_re]; linarith, by rw [hw_re]; linarith⟩
    rw [← eq_ofReal_re_add_I_mul hw_im]
    exact (riemannXi_eq_zero_iff (by rw [hw_re]; linarith) (by rw [hw_re]; linarith)).mp hxi_w
end
end CertificatePort67
section CertificatePort68
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Set
theorem riemannXi_re_mem_Ioo_of_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hge : ∀ z : ℂ, 1 ≤ z.re → riemannXi z ≠ 0 := by
    intro z hz hzero
    have hz0 : z ≠ 0 := by rintro rfl; rw [Complex.zero_re] at hz; norm_num at hz
    have hz1 : z ≠ 1 := by rintro rfl; rw [riemannXi_one] at hzero; norm_num at hzero
    have hΓ : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ] at hzero
    exact mul_ne_zero (prefactor_ne_zero_of hz0 hz1 hΓ)
      (riemannZeta_ne_zero_of_one_le_re hz) hzero
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    have h1 : 1 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact hge (1 - s) h1 (by rw [riemannXi_one_sub]; exact hs)
  · by_contra h
    rw [not_lt] at h
    exact hge s h hs
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    riemannZeta s = 0 :=
  have h := riemannXi_re_mem_Ioo_of_eq_zero hs
  (riemannXi_eq_zero_iff h.1 h.2).mp hs
theorem riemannXi_ne_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : riemannXi z ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  have hz' : z = (↑z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [hz'] at hξ
  exact riemannXi_ofReal_ne_zero_of_mem_Icc ⟨by linarith, by linarith⟩ hξ
private theorem argVariation_riemannXi_seg (z₀ z₁ : ℂ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u).re)
    (hne1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 1)
    (hζ : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      = argVariation 0 1
          (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        + argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hsne : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 := by
    intro u hu heq; simpa [heq] using hre u hu
  have hPcont : ContinuousOn
      (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1))) (Set.Icc 0 1) :=
    (continuous_const.mul ((continuous_lineSeg z₀ z₁).mul
      ((continuous_lineSeg z₀ z₁).sub continuous_const))).continuousOn
  have hGcont : ContinuousOn (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.Gammaℝ) (f := lineSeg z₀ z₁)
      (Complex.analyticAt_Gammaℝ (hre u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hZcont : ContinuousOn (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := riemannZeta) (f := lineSeg z₀ z₁)
      (differentiableAt_riemannZeta (hne1 u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hPne : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)) ≠ 0 := fun u hu ↦
    mul_ne_zero (one_div_ne_zero two_ne_zero)
      (mul_ne_zero (hsne u hu) (sub_ne_zero.mpr (hne1 u hu)))
  have hGne : ∀ u ∈ Set.Icc (0 : ℝ) 1, Complex.Gammaℝ (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu ↦ Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu)
  have hEq : Set.EqOn (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      (((fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        * (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)))
        * (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))) (Set.Icc 0 1) := by
    intro u hu
    change riemannXi (lineSeg z₀ z₁ u) = _
    rw [riemannXi_eq_prefactor_mul (hsne u hu) (hne1 u hu)
      (Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu))]
    simp only [Pi.mul_apply]
  rw [argVariation_congr zero_le_one hEq,
    argVariation_mul zero_le_one (hPcont.mul hGcont)
      (fun u hu ↦ mul_ne_zero (hPne u hu) (hGne u hu)) hZcont hζ,
    argVariation_mul zero_le_one hPcont hPne hGcont hGne]
private theorem rectangle_corner_eq (T : ℝ) :
    (2 + I * (T : ℂ)).re = 2 ∧ (2 + I * (T : ℂ)).im = T
      ∧ (-1 : ℂ).re = -1 ∧ (-1 : ℂ).im = 0 :=
  ⟨by simp, by simp, by norm_num, by norm_num⟩
private theorem riemannXi_ne_zero_of_mem_rectangleBorder {T : ℝ}
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ RectangleBorder (-1) (2 + I * (T : ℂ))) : riemannXi ρ ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    hwre, hwim, hm1re, hm1im] at hρ
  rcases hρ with ((⟨_, him⟩ | ⟨hre, _⟩) | ⟨_, him⟩) | ⟨hre, _⟩
  ·
    exact riemannXi_ne_zero_of_im_eq_zero him hξ
  ·
    rw [hre] at hr0; norm_num at hr0
  ·
    exact hT' ρ him (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  ·
    rw [hre] at hr1; norm_num at hr1
theorem riemannZeta.N_eq {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  have hle_re : (-1 : ℂ).re ≤ (2 + I * (T : ℂ)).re := by rw [hm1re, hwre]; norm_num
  have hle_im : (-1 : ℂ).im ≤ (2 + I * (T : ℂ)).im := by rw [hm1im, hwim]; exact hT.le
  have hRS : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0})
      = {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
          ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzR, hξ⟩
      obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim] at hzR
      obtain ⟨_, _, hzim0, hzimT⟩ := hzR
      exact ⟨hξ, ⟨hr0, hr1⟩,
        hzim0.lt_of_ne fun heq ↦ riemannXi_ne_zero_of_im_eq_zero heq.symm hξ,
        hzimT.lt_of_ne fun heq ↦ hT' z heq (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)⟩
    · rintro ⟨hξ, ⟨hr0, hr1⟩, hi0, hiT⟩
      refine ⟨?_, hξ⟩
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim]
      exact ⟨by linarith, by linarith, hi0.le, hiT.le⟩
  have hfin : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0}).Finite := by
    have hcompact : IsCompact (Rectangle (-1) (2 + I * (T : ℂ))) :=
      isCompact_uIcc.reProdIm isCompact_uIcc
    refine (riemannZeta.zeroes_on_Compact_finite' hcompact).subset ?_
    rintro z ⟨hzR, hξ⟩
    exact ⟨hzR, riemannZeta_eq_zero_of_riemannXi_eq_zero hξ⟩
  have hap : (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ))
      = 1 / (2 * Real.pi) * rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ)) := by
    refine rectangle_zero_count_eq_argVariation (z := (-1 : ℂ)) (w := 2 + I * (T : ℂ))
      (z₀ := (2 : ℂ)) analyticOnNhd_riemannXi
      isConnected_univ (Set.mem_univ _) ?_ (Set.subset_univ _) hle_re hle_im
      (fun ρ hρ ↦ riemannXi_ne_zero_of_mem_rectangleBorder hT' hρ) hfin
    have h2 := riemannXi_ofReal_ne_zero_of_mem_Icc (σ := 2) ⟨by norm_num, le_refl _⟩
    simpa using h2
  have hbridge : (∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
        ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
      (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
      = ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ) := by
    rw [← Finset.tsum_subtype' hfin.toFinset
        (fun ρ ↦ (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ)), hfin.coe_toFinset]
    exact (Equiv.setCongr hRS.symm).tsum_eq
      (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
  have hhalf := argVariation_riemannXi_rectangle_eq_two_mul hT hT'
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have hc2re : (1 / 2 + I * (T : ℂ)).re = 1 / 2 := by simp
  have hc2im : (1 / 2 + I * (T : ℂ)).im = T := by simp
  have hcontour : argVariationContourL riemannXi T
      = argVariationContourL (fun s ↦ (1 / 2 : ℂ) * (s * (s - 1))) T
        + argVariationContourL Complex.Gammaℝ T + argVariationContourL riemannZeta T := by
    have hseg1 := argVariation_riemannXi_seg 2 (2 + I * (T : ℂ))
      (fun u _ ↦ by rw [lineSeg_re, h2re, hwre]; norm_num)
      (fun u _ heq ↦ by
        have := congrArg Complex.re heq
        rw [lineSeg_re, h2re, hwre, Complex.one_re] at this; norm_num at this)
      (fun u _ ↦ riemannZeta_ne_zero_of_one_le_re (by rw [lineSeg_re, h2re, hwre]; norm_num))
    have hseg2 := argVariation_riemannXi_seg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ))
      (fun u hu ↦ by rw [lineSeg_re, hwre, hc2re]; nlinarith [hu.1, hu.2])
      (fun u _ heq ↦ by
        have := congrArg Complex.im heq
        rw [lineSeg_im, hwim, hc2im, Complex.one_im] at this
        simp only [sub_self, mul_zero, add_zero] at this; exact hT.ne' this)
      (fun u _ ↦ hT' _ (by rw [lineSeg_im, hwim, hc2im]; ring))
    simp only [argVariationContourL]
    rw [hseg1, hseg2]; ring
  rw [argVariation_poly_L hT, argVariation_GammaPi_L hT] at hcontour
  have hZval : argVariationContourL riemannZeta T = Real.pi * argZeta T := by
    rw [argZeta]; field_simp
  rw [riemannZeta.N_eq_tsum_riemannXi_order, hbridge, hap, hhalf, hcontour, hZval]
  field_simp
  ring
theorem riemannZeta.N_eq_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T :=
  riemannZeta.N_eq hT (riemannZeta_ne_zero_of_forall_re_mem_Ico hT h)
end
end CertificatePort68
section CertificatePort69
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Function Set
open Complex.Stirling
open scoped Real
instance : Countable RiemannXiZerosIndex := by
  have : Countable ↥(MeromorphicOn.divisor riemannXi ⊤).support :=
    ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (MeromorphicOn.divisor riemannXi ⊤).discreteSupport).to_subtype
  infer_instance
theorem AnalyticAt.conj_conj {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g (starRingEnd ℂ u)) :
    AnalyticAt ℂ (fun w ↦ starRingEnd ℂ (g (starRingEnd ℂ w))) u := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Complex.continuous_conj.continuousAt.eventually
    (hg.eventually_analyticAt.mono fun y hy ↦ hy.differentiableAt)] with w hw
  simpa [Function.comp_def] using hw.conj_conj
private theorem analyticAt_riemannXi (w : ℂ) : AnalyticAt ℂ riemannXi w :=
  differentiable_riemannXi.analyticAt w
private theorem analyticOrderAt_riemannXi_ne_top (w : ℂ) :
    analyticOrderAt riemannXi w ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w analyticAt_riemannXi]
  intro h
  simpa [riemannXi_zero] using congrFun h 0
theorem analyticOrderAt_riemannXi_conj (z : ℂ) :
    analyticOrderAt riemannXi (starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  set N := analyticOrderNatAt riemannXi z
  obtain ⟨g, hg, hg0, hfac⟩ :=
    (analyticAt_riemannXi z).analyticOrderAt_ne_top.mp (analyticOrderAt_riemannXi_ne_top z)
  have hgconj : AnalyticAt ℂ (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) :=
    AnalyticAt.conj_conj (u := starRingEnd ℂ z) (by rw [Complex.conj_conj]; exact hg)
  have hval : (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) ≠ 0 := by
    simp only [Complex.conj_conj]
    exact fun h ↦ hg0 (by simpa using congrArg (starRingEnd ℂ) h)
  have hfac2 : riemannXi =ᶠ[𝓝 (starRingEnd ℂ z)]
      fun u ↦ (u - starRingEnd ℂ z) ^ N • (starRingEnd ℂ (g (starRingEnd ℂ u))) := by
    have hc : ContinuousAt (starRingEnd ℂ) (starRingEnd ℂ z) :=
      Complex.continuous_conj.continuousAt
    have hpull : ∀ᶠ u in 𝓝 (starRingEnd ℂ z),
        riemannXi (starRingEnd ℂ u) = (starRingEnd ℂ u - z) ^ N • g (starRingEnd ℂ u) := by
      have hbase : ∀ᶠ y in 𝓝 (starRingEnd ℂ (starRingEnd ℂ z)),
          riemannXi y = (y - z) ^ N • g y := by rw [Complex.conj_conj]; exact hfac
      exact hc.eventually hbase
    filter_upwards [hpull] with u hu
    have h2 := congrArg (starRingEnd ℂ) hu
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, riemannXi_conj, Complex.conj_conj] at h2
    simpa only [smul_eq_mul] using h2
  have hcz : analyticOrderNatAt riemannXi (starRingEnd ℂ z) = N := by
    rw [(analyticAt_riemannXi (starRingEnd ℂ z)).analyticOrderNatAt_eq_iff
      (analyticOrderAt_riemannXi_ne_top _)]
    exact ⟨_, hgconj, hval, hfac2⟩
  rw [← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top (starRingEnd ℂ z)),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top z), hcz]
theorem analyticOrderAt_riemannXi_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have hcomp : analyticOrderAt (riemannXi ∘ fun w ↦ 1 - w) z
      = analyticOrderAt riemannXi ((fun w ↦ 1 - w) z) := by
    refine analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_const.sub analyticAt_id) ?_
    have hd : deriv (fun w : ℂ ↦ 1 - w) z = -1 := ((hasDerivAt_id z).const_sub (1 : ℂ)).deriv
    rw [hd]; exact neg_ne_zero.mpr one_ne_zero
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext w; simp only [comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  exact hcomp.symm
theorem analyticOrderAt_riemannXi_one_sub_conj (z : ℂ) :
    analyticOrderAt riemannXi (1 - starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  rw [analyticOrderAt_riemannXi_one_sub, analyticOrderAt_riemannXi_conj]
theorem divisor_riemannXi_one_sub_conj (z : ℂ) :
    MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ z)
      = MeromorphicOn.divisor riemannXi ⊤ z := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  rw [divisor_eq_analyticOrderNatAt hf, divisor_eq_analyticOrderNatAt hf]
  simp only [analyticOrderNatAt, analyticOrderAt_riemannXi_one_sub_conj]
theorem exists_equiv_riemannXiZeros_one_sub_conj :
    ∃ e : RiemannXiZerosIndex ≃ RiemannXiZerosIndex,
      ∀ i, riemannXiZeros (e i) = 1 - starRingEnd ℂ (riemannXiZeros i) := by
  let F : (MeromorphicOn.divisor riemannXi ⊤).support →
      (MeromorphicOn.divisor riemannXi ⊤).support :=
    fun a ↦ ⟨1 - starRingEnd ℂ (a : ℂ), by
      rw [mem_support, divisor_riemannXi_one_sub_conj]
      exact mem_support.mp a.2⟩
  have hFinv : Involutive F := by
    intro a
    apply Subtype.ext
    change 1 - starRingEnd ℂ (1 - starRingEnd ℂ (a : ℂ)) = (a : ℂ)
    simp only [map_sub, map_one, Complex.conj_conj]; ring
  let eSupp := hFinv.toPerm F
  have hfib : ∀ a : (MeromorphicOn.divisor riemannXi ⊤).support,
      (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
        = (MeromorphicOn.divisor riemannXi ⊤ (eSupp a : ℂ)).toNat := by
    intro a
    change (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
      = (MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ (a : ℂ))).toNat
    rw [divisor_riemannXi_one_sub_conj]
  refine ⟨Equiv.sigmaCongr eSupp (fun a ↦ finCongr (hfib a)), ?_⟩
  rintro ⟨a, k⟩
  rfl
theorem tsum_riemannXiZeros_one_sub_conj {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    ∑' i, g (riemannXiZeros i) = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  calc ∑' i, g (riemannXiZeros i)
      = ∑' i, g (riemannXiZeros (e i)) := (e.tsum_eq (fun i ↦ g (riemannXiZeros i))).symm
    _ = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by simp_rw [hval]
theorem summable_riemannXiZeros_one_sub_conj_iff {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    Summable (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      ↔ Summable (fun i ↦ g (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  have hcomp : (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      = (fun j ↦ g (riemannXiZeros j)) ∘ e := by
    ext i; simp only [Function.comp_apply, hval i]
  rw [hcomp, Equiv.summable_iff]
theorem riemannXi_riemannXiZeros_eq_zero (i : RiemannXiZerosIndex) :
    riemannXi (riemannXiZeros i) = 0 := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (riemannXiZeros i) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [divisor_eq_analyticOrderNatAt hf] at hmem
  have hnat : analyticOrderNatAt riemannXi (riemannXiZeros i) ≠ 0 := by
    intro h; rw [h] at hmem; simp at hmem
  have hAt : AnalyticAt ℂ riemannXi (riemannXiZeros i) := differentiable_riemannXi.analyticAt _
  rw [← hAt.analyticOrderAt_ne_zero]
  intro hz
  exact hnat (by simp [analyticOrderNatAt, hz])
theorem riemannXiZeros_re_pos (i : RiemannXiZerosIndex) : 0 < (riemannXiZeros i).re :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).1
theorem riemannXiZeros_re_lt_one (i : RiemannXiZerosIndex) : (riemannXiZeros i).re < 1 :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).2
private lemma abs_re_inv_le_norm_sq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    |(ρ⁻¹).re| ≤ ‖ρ⁻¹‖ ^ 2 := by
  have hne : ρ ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hne
  have hsq : ‖ρ⁻¹‖ ^ 2 = (Complex.normSq ρ)⁻¹ := by rw [norm_inv, inv_pow, Complex.sq_norm]
  rw [Complex.inv_re, hsq, abs_div, abs_of_pos h0, abs_of_pos hns, div_le_iff₀ hns,
    inv_mul_cancel₀ (ne_of_gt hns)]
  exact h1.le
theorem summable_re_inv_riemannXiZeros :
    Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := by
  refine Summable.of_norm_bounded summable_inv_norm_sq_riemannXiZeros (fun i ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_re_inv_le_norm_sq (riemannXiZeros_re_pos i) (riemannXiZeros_re_lt_one i)
private lemma log_norm_one_sub_div {ρ : ℂ} (hρ : ρ ≠ 0) {w : ℂ} (hw : w ≠ ρ) :
    Real.log ‖1 - w / ρ‖ = Real.log ‖w - ρ‖ - Real.log ‖ρ‖ := by
  have hh : (1 : ℂ) - w / ρ = (ρ - w) / ρ := by rw [sub_div, div_self hρ]
  rw [hh, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
    (norm_ne_zero_iff.mpr hρ), norm_sub_rev]
noncomputable def shiftLogIntegrand (t d : ℝ) (ρ : ℂ) (x : ℝ) : ℝ :=
    Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ‖
      - Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ‖
noncomputable def shiftLogIntegral (t d : ℝ) (ρ : ℂ) : ℝ :=
    ∫ x in (0 : ℝ)..d, shiftLogIntegrand t d ρ x
private lemma abs_log_norm_one_sub_add_re_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖1 - z‖ + z.re| ≤ ‖z‖ ^ 2 := by
  have h : Real.log ‖1 - z‖ + z.re = (Complex.log (1 - z) + z).re := by
    rw [Complex.add_re, Complex.log_re]
  rw [h]
  exact (Complex.abs_re_le_norm _).trans (Complex.norm_log_one_sub_add_self_le hz)
private lemma abs_log_norm_one_sub_div_add_re_le {z ρ : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C)
    (hsmall : C * ‖ρ⁻¹‖ ≤ 1 / 2) :
    |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by
  have hle : ‖z / ρ‖ ≤ C * ‖ρ⁻¹‖ := by
    rw [norm_div, norm_inv, div_eq_mul_inv]; gcongr
  calc |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ ‖z / ρ‖ ^ 2 :=
        abs_log_norm_one_sub_add_re_le (hle.trans hsmall)
    _ ≤ (C * ‖ρ⁻¹‖) ^ 2 := by gcongr
    _ = C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by ring
private lemma sub_ne_zero_of_im_eq {z c : ℂ} {t : ℝ} (hz : z.im = t) (hc : c.im ≠ t) :
    z - c ≠ 0 := fun h ↦ hc (by
  have := congrArg Complex.im h
  rw [Complex.sub_im, hz, Complex.zero_im, sub_eq_zero] at this
  exact this.symm)
private lemma complex_line_im (a b : ℝ) : ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).im = b := by
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
private lemma complex_line_re (a b : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).re = 1 / 2 + a := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
private lemma complex_line_add_im (a b c : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I + (c : ℂ)).im = b := by
  rw [Complex.add_im, complex_line_im, Complex.ofReal_im, add_zero]
private lemma shiftLogIntegrand_eq {ρ : ℂ} (hρ : ρ ≠ 0) (t d x : ℝ)
    (h1 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ)
    (h2 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ) :
    shiftLogIntegrand t d ρ x
      = ((Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re)
          - (Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re))
        - d * (ρ⁻¹).re := by
  have ere : (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re
      - (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re = d * (ρ⁻¹).re := by
    rw [← Complex.sub_re,
      show ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ
          - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ = (d : ℂ) * ρ⁻¹ by
        rw [div_sub_div_same,
          show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
              - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) = (d : ℂ) by ring,
          div_eq_mul_inv],
      Complex.re_ofReal_mul]
  unfold shiftLogIntegrand
  rw [log_norm_one_sub_div hρ h1, log_norm_one_sub_div hρ h2]
  linear_combination -ere
private lemma continuous_shiftLogIntegrand {ρ : ℂ} (t d : ℝ) (hρt : ρ.im ≠ t) :
    Continuous (shiftLogIntegrand t d ρ) := by
  unfold shiftLogIntegrand
  refine Continuous.sub (Continuous.log (by fun_prop) (fun x ↦ ?_))
    (Continuous.log (by fun_prop) (fun x ↦ ?_))
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))
      (complex_line_add_im x t d) hρt
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)
      (complex_line_im x t) hρt
private lemma bookerIntegrand_eq_shiftLog (ρ : ℂ) (t d x : ℝ) (hρt : ρ.im ≠ t) :
    Real.log ‖((x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))
        / (((x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
            * ((x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))))‖
      = shiftLogIntegrand t d ρ x + shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ) x := by
  have hc1 : (x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ)
        ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc2 : (x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ) := by
    apply Complex.ext <;> simp; ring
  have hc3 : (x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc4 : (x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ) := by
    apply Complex.ext <;> simp; ring
  have him : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I).im = t := complex_line_im x t
  have himd : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)).im = t := complex_line_add_im x t d
  have hρstar : (1 - (starRingEnd ℂ) ρ).im ≠ t := by
    simpa [Complex.sub_im, Complex.one_im, Complex.conj_im] using hρt
  have hA1 := sub_ne_zero_of_im_eq himd hρstar
  have hA2 := sub_ne_zero_of_im_eq himd hρt
  have hA3 := sub_ne_zero_of_im_eq him hρstar
  have hA4 := sub_ne_zero_of_im_eq him hρt
  rw [norm_div, norm_mul, norm_mul, hc1, hc2, hc3, hc4, Complex.norm_conj, Complex.norm_conj,
    Complex.norm_conj, Complex.norm_conj,
    Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2))
      (mul_ne_zero (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)),
    Real.log_mul (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2),
    Real.log_mul (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)]
  unfold shiftLogIntegrand
  ring
private lemma shiftLogIntegral_add_le_of {ρ : ℂ} (t : ℝ) {d : ℝ} (hd : 1 / 2 < d)
    (hρt : ρ.im ≠ t) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {c : ℝ} (hc : 2 ≤ c) :
    shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ)
      ≤ c * d ^ 2 * ((((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re) := by
  have hwre : |(ρ - (1 / 2 + (t : ℂ) * I)).re| ≤ 1 / 2 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).re = ρ.re - 1 / 2 by simp]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwim : (ρ - (1 / 2 + (t : ℂ) * I)).im ≠ 0 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).im = ρ.im - t by simp]
    exact sub_ne_zero.mpr hρt
  have hbk := bookerPairIntegral_le_of hd hwre hwim hc
  have hresPlus : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    have hc : (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hresMinus : (1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re := by
    have hc : (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ) := by
      apply Complex.ext <;> simp; ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hI1 : IntervalIntegrable (shiftLogIntegrand t d ρ) MeasureTheory.volume 0 d :=
    (continuous_shiftLogIntegrand t d hρt).intervalIntegrable 0 d
  have hI2 : IntervalIntegrable (shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ))
      MeasureTheory.volume 0 d := by
    refine (continuous_shiftLogIntegrand t d ?_).intervalIntegrable 0 d
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
    exact hρt
  have hLHS : bookerPairIntegral d (ρ - (1 / 2 + (t : ℂ) * I))
      = shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ) := by
    rw [bookerPairIntegral, shiftLogIntegral, shiftLogIntegral,
      ← intervalIntegral.integral_add hI1 hI2]
    exact intervalIntegral.integral_congr (fun x _ ↦ bookerIntegrand_eq_shiftLog ρ t d x hρt)
  have hRHS : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        + 1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    rw [Complex.add_re, hresPlus, hresMinus]; ring
  rw [hLHS, hRHS] at hbk
  exact hbk
lemma Complex.norm_complex_line_le (a b : ℝ) :
    ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖ ≤ 1 / 2 + |a| + |b| := by
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  calc ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖
      ≤ ‖(1 / 2 : ℂ) + (a : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ ≤ (‖(1 / 2 : ℂ)‖ + ‖(a : ℂ)‖) + ‖(b : ℂ) * I‖ := by gcongr; exact norm_add_le _ _
    _ = 1 / 2 + |a| + |b| := by
        rw [h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
theorem summable_re_inv_riemannXiZeros_sub {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re) := by
  have h2 : Summable (fun i ↦ (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i).re) :=
    (summable_partial_fraction hs).map (Complex.reCLM : ℂ →L[ℝ] ℝ).toAddMonoidHom
      Complex.continuous_re
  refine (h2.sub summable_re_inv_riemannXiZeros).congr (fun i ↦ ?_)
  rw [Complex.add_re, one_div, one_div, add_sub_cancel_right]
theorem exists_forall_riemannXiZeros_im_ne :
    ∃ t₀ : ℝ, ∀ i, (riemannXiZeros i).im ≠ t₀ := by
  have hcount : (Set.range (fun i ↦ (riemannXiZeros i).im)).Countable := Set.countable_range _
  have hne : Set.range (fun i ↦ (riemannXiZeros i).im) ≠ Set.univ := fun h ↦
    Cardinal.not_countable_real (h ▸ hcount)
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_compl.mpr hne
  exact ⟨t₀, fun i h ↦ ht₀ ⟨i, h⟩⟩
theorem tsum_re_inv_riemannXiZeros_sub_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re = 0 := by
  have hgpt : ∀ z : ℂ, ((s₀ - (1 - starRingEnd ℂ z))⁻¹).re = -((s₀ - z)⁻¹).re := by
    intro z
    have hid : s₀ - (1 - starRingEnd ℂ z) = -(starRingEnd ℂ (s₀ - z)) := by
      rw [map_sub, hconj]; ring
    rw [hid, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
  have hcalc : (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
      = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re :=
    calc (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
        = ∑' i, ((s₀ - (1 - starRingEnd ℂ (riemannXiZeros i)))⁻¹).re :=
          tsum_riemannXiZeros_one_sub_conj (fun z ↦ ((s₀ - z)⁻¹).re)
      _ = ∑' i, (-((s₀ - riemannXiZeros i)⁻¹).re) := by simp_rw [hgpt]
      _ = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re := tsum_neg
  linarith
private lemma deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannXi s) := by
  have hsym : starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have h : starRingEnd ℂ ∘ deriv riemannXi ∘ starRingEnd ℂ = deriv riemannXi := by
    rw [← deriv_conj_conj, hsym]
  simpa using congrArg (starRingEnd ℂ) (congrFun h s)
private lemma deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = - deriv riemannXi s := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (riemannXi ∘ fun w ↦ 1 - w) (deriv riemannXi (1 - s) * (-1)) s :=
    ((differentiable_riemannXi (1 - s)).hasDerivAt).comp s hu
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  have hd : HasDerivAt riemannXi (deriv riemannXi s) s := (differentiable_riemannXi s).hasDerivAt
  linear_combination -(hcomp.unique hd)
theorem re_logDeriv_riemannXi_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    (logDeriv riemannXi s₀).re = 0 := by
  have ha : logDeriv riemannXi (starRingEnd ℂ s₀) = starRingEnd ℂ (logDeriv riemannXi s₀) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]
  have hb : logDeriv riemannXi (1 - s₀) = - logDeriv riemannXi s₀ := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]
  have hcomb : starRingEnd ℂ (logDeriv riemannXi s₀) = - logDeriv riemannXi s₀ := by
    rw [← ha, hconj, hb]
  have := congrArg Complex.re hcomb
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith
private lemma re_tsum_partialFraction_add {s : ℂ} (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable fun i ↦ ((s - riemannXiZeros i)⁻¹).re) :
    (∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i)).re
      = ∑' i, ((s - riemannXiZeros i)⁻¹).re + ∑' i, ((riemannXiZeros i)⁻¹).re := by
  rw [Complex.re_tsum (summable_partial_fraction hsne),
    tsum_congr (fun i ↦ by rw [Complex.add_re, one_div, one_div]),
    hPair.tsum_add summable_re_inv_riemannXiZeros]
theorem hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero :
    (logDeriv riemannXi 0).re + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
  obtain ⟨t₀, ht₀⟩ := exists_forall_riemannXiZeros_im_ne
  set s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℂ) * I with hs₀
  have hs0im : s₀.im = t₀ := by rw [hs₀]; simp
  have hsne : ∀ i, s₀ ≠ riemannXiZeros i := fun i h ↦ ht₀ i (by rw [← h, hs0im])
  have hconj : starRingEnd ℂ s₀ = 1 - s₀ := by
    rw [hs₀]; apply Complex.ext <;> simp; ring
  have hkey := congrArg Complex.re (logDeriv_riemannXi_eq hsne)
  rw [Complex.add_re,
    re_tsum_partialFraction_add hsne (summable_re_inv_riemannXiZeros_sub hsne),
    re_logDeriv_riemannXi_critical_eq_zero hconj,
    tsum_re_inv_riemannXiZeros_sub_critical_eq_zero hconj, zero_add] at hkey
  linarith
theorem tsum_re_inv_riemannXiZeros_sub_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re)) :
    ∑' i, ((s - riemannXiZeros i)⁻¹).re
      = (logDeriv riemannZeta s).re + (1 / s).re + (1 / (s - 1)).re
        - 1 / 2 * Real.log π + 1 / 2 * (Complex.digamma (s / 2)).re := by
  have hkey := logDeriv_riemannZeta_eq hre hs1 hsne
  have hκ := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hlogpi_re : ((1 / 2 : ℂ) * (Real.log π : ℂ)).re = 1 / 2 * Real.log π := by
    rw [hhalf, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpsi_re : ((1 / 2 : ℂ) * Complex.digamma (s / 2)).re
      = 1 / 2 * (Complex.digamma (s / 2)).re := by rw [hhalf, Complex.re_ofReal_mul]
  have hexp := congrArg Complex.re hkey
  simp only [Complex.add_re, Complex.sub_re, hlogpi_re, hpsi_re] at hexp
  rw [re_tsum_partialFraction_add hsne hPair] at hexp
  linarith [hexp, hκ]
lemma summable_pairDensity {t d : ℝ} (hd : 1 / 2 < d) :
    Summable (fun i ↦ (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re) :=
  summable_re_inv_riemannXiZeros_sub fun i h ↦ by
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, complex_line_re d t] at hlt; linarith
lemma Real.log_add_le {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    Real.log (u + t) ≤ Real.log t + u / t := by
  have hdiv : Real.log ((t + u) / t) ≤ u / t := by
    calc Real.log ((t + u) / t)
        ≤ (t + u) / t - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) ht)
      _ = u / t := by field_simp; ring
  rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < t + u)) ht.ne'] at hdiv
  rw [add_comm u t]
  linarith
lemma Complex.re_one_div_le_norm_inv (w : ℂ) : (1 / w).re ≤ ‖w‖⁻¹ := by
  rw [one_div]; exact (Complex.re_le_norm _).trans_eq (norm_inv w)
lemma shiftedLine_setup {d t : ℝ} (hdlt : 1 / 2 < d) (ht0 : 0 < t) :
    ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d ∧
      ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t ∧
      0 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      1 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ 1 ∧
      (∀ i, (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ riemannXiZeros i) ∧
      1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      0 < ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ≤ (1 / 2 + d) + t := by
  have hsre : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d := complex_line_re d t
  have hsim : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t := complex_line_im d t
  have hsnorm_lb : 1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ := by
    rw [← hsre]; exact Complex.re_le_norm _
  refine ⟨hsre, hsim, ?_, ?_, ?_, ?_, hsnorm_lb, lt_of_lt_of_le (by linarith) hsnorm_lb, ?_⟩
  · rw [hsre]; linarith
  · rw [hsre]; linarith
  · intro h; rw [h] at hsim; simp at hsim; linarith
  · intro i h
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, hsre] at hlt; linarith
  · have h := Complex.norm_complex_line_le d t
    rw [abs_of_pos (by linarith : (0 : ℝ) < d), abs_of_pos ht0] at h
    linarith
private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, le_abs_self b, le_abs_self c],
              by linarith [le_abs_self a, neg_abs_le b, neg_abs_le c]⟩
private lemma exists_eventually_forall_norm_shiftLogIntegrand_le {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in Filter.cofinite, ∀ x ∈ Set.uIoc (0 : ℝ) d,
      ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
  have hd0 : (0 : ℝ) < d := by linarith
  set C0 : ℝ := 1 / 2 + 2 * d + |t| with hC0
  have hC0pos : 0 ≤ C0 := by rw [hC0]; positivity
  have hsum2 := summable_inv_norm_sq_riemannXiZeros
  have htail : ∀ᶠ i in Filter.cofinite, ‖(riemannXiZeros i)⁻¹‖ ≤ 1 / (2 * (C0 + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (C0 + 1))) ^ 2 := by positivity
    filter_upwards [hsum2.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine ⟨2 * C0 ^ 2 + d, by positivity, ?_⟩
  filter_upwards [htail] with i hi
  set ρ := riemannXiZeros i with hρ
  have hρ0 : ρ ≠ 0 := riemannXiZeros_ne_zero i
  have hρre0 : 0 < ρ.re := riemannXiZeros_re_pos i
  have hρre1 : ρ.re < 1 := riemannXiZeros_re_lt_one i
  have hsmall : C0 * ‖ρ⁻¹‖ ≤ 1 / 2 := by
    have hstep : C0 * ‖ρ⁻¹‖ ≤ C0 * (1 / (2 * (C0 + 1))) := mul_le_mul_of_nonneg_left hi hC0pos
    have : C0 * (1 / (2 * (C0 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hE3 : d * |(ρ⁻¹).re| ≤ d * ‖ρ⁻¹‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (abs_re_inv_le_norm_sq hρre0 hρre1) hd0.le
  intro x hx
  rw [Set.uIoc_of_le hd0.le] at hx
  have hxabs : |x| ≤ d := by rw [abs_of_nonneg hx.1.le]; exact hx.2
  have hs_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I‖ ≤ C0 := by
    have := Complex.norm_complex_line_le x t; rw [hC0]; linarith
  have hsd_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)‖ ≤ C0 := by
    have h1 := norm_add_le ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) (d : ℂ)
    have h2 : ‖(d : ℂ)‖ = d := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    have := Complex.norm_complex_line_le x t
    rw [hC0]; rw [h2] at h1; linarith
  have h2ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_im x t])
  have h1ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_add_im x t d])
  rw [Real.norm_eq_abs, shiftLogIntegrand_eq hρ0 t d x h1ne h2ne]
  refine (abs_sub_sub_le _ _ _).trans ?_
  rw [abs_mul, abs_of_pos hd0]
  refine (add_le_add (add_le_add (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hsd_C0 hsmall)
    (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hs_C0 hsmall)) hE3).trans (le_of_eq ?_)
  ring
private lemma summable_shiftLogIntegral {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    Summable (fun i ↦ shiftLogIntegral t d (riemannXiZeros i)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  refine Summable.of_norm_bounded_eventually
    (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
  filter_upwards [hCb] with i hi
  calc ‖shiftLogIntegral t d (riemannXiZeros i)‖
      = ‖∫ x in (0 : ℝ)..d, shiftLogIntegrand t d (riemannXiZeros i) x‖ := by rw [shiftLogIntegral]
    _ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 * |d - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hi
    _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by rw [sub_zero, abs_of_pos hd0]; ring
theorem tsum_shiftLogIntegral_eq_intervalIntegral_tsum {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hint : ∀ i, MeasureTheory.IntegrableOn
      (shiftLogIntegrand t d (riemannXiZeros i)) (Set.Ioc 0 d) := fun i ↦
    (continuous_shiftLogIntegrand t d (ht i)).integrableOn_Ioc
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  have hsummint : Summable (fun i ↦
      ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖) := by
    refine Summable.of_norm_bounded_eventually
      (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
    filter_upwards [hCb] with i hi
    have hnn : (0 : ℝ) ≤ ∫ x in Set.Ioc (0 : ℝ) d,
        ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ :=
      MeasureTheory.integral_nonneg (fun x ↦ norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖
        ≤ ∫ _x in Set.Ioc (0 : ℝ) d, C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on (hint i).norm ?_ measurableSet_Ioc ?_
          · exact MeasureTheory.integrableOn_const
              (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          · intro x hx
            exact hi x (by rw [Set.uIoc_of_le hd0.le]; exact hx)
      _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hd0.le, smul_eq_mul]
          ring
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun i ↦ shiftLogIntegrand t d (riemannXiZeros i))
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) d)) hint hsummint
  calc ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∑' i, ∫ x in Set.Ioc (0 : ℝ) d, shiftLogIntegrand t d (riemannXiZeros i) x := by
        refine tsum_congr (fun i ↦ ?_)
        rw [shiftLogIntegral, intervalIntegral.integral_of_le hd0.le]
    _ = ∫ x in Set.Ioc (0 : ℝ) d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := hswap
    _ = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
        rw [intervalIntegral.integral_of_le hd0.le]
theorem integral_tsum_log_norm_shift_le_of {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) {c : ℝ} (hc : 2 ≤ c) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c * d ^ 2 * ∑' i,
          (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re := by
  set A : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hA
  set g : ℂ → ℝ := shiftLogIntegral t d with hg
  set f : ℂ → ℝ := fun ρ ↦ ((A - ρ)⁻¹).re with hf
  have hSg : Summable fun i ↦ g (riemannXiZeros i) := summable_shiftLogIntegral hd ht
  have hSh : Summable fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff g).mpr hSg
  have hSc : Summable fun i ↦ f (riemannXiZeros i) := summable_pairDensity hd
  have hSch : Summable fun i ↦ f (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff f).mpr hSc
  have hper : ∀ i, g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))
      ≤ c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) := fun i ↦
    shiftLogIntegral_add_le_of t hd (ht i) (riemannXiZeros_re_pos i)
      (riemannXiZeros_re_lt_one i) hc
  have hreflg := tsum_riemannXiZeros_one_sub_conj g
  have hreflc := tsum_riemannXiZeros_one_sub_conj f
  have key : 2 * ∑' i, g (riemannXiZeros i) ≤ 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) :=
    calc 2 * ∑' i, g (riemannXiZeros i)
        = ∑' i, (g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))) := by
          rw [hSg.tsum_add hSh, ← hreflg]; ring
      _ ≤ ∑' i, c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) :=
          Summable.tsum_le_tsum hper (hSg.add hSh) ((hSc.add hSch).mul_left _)
      _ = 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) := by
          rw [tsum_mul_left, hSc.tsum_add hSch, ← hreflc]; ring
  linarith
open scoped LSeries.notation
open ArithmeticFunction
lemma re_logDeriv_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    (logDeriv riemannZeta s).re ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := by
  have hsum : Summable (fun n ↦ ‖LSeries.term ↗Λ s n‖) := (LSeriesSummable_vonMangoldt hs).norm
  have hlogD : logDeriv riemannZeta s = -LSeries ↗Λ s := by
    rw [logDeriv_apply, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]; ring
  calc (logDeriv riemannZeta s).re
      ≤ ‖logDeriv riemannZeta s‖ := Complex.re_le_norm _
    _ = ‖LSeries ↗Λ s‖ := by rw [hlogD, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
lemma re_digamma_le {z : ℂ} (hz : 0 < z.re) {C : ℝ}
    (hC : ‖digammaRemainderIoi z 1‖ ≤ C * ‖z‖ ^ (-(1 : ℤ))) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + (1 / 2 + C) / ‖z‖ := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzne : ‖z‖ ≠ 0 := hznorm.ne'
  have hzpow : ‖z‖ ^ (-(1 : ℤ)) = (‖z‖)⁻¹ := by rw [zpow_neg, zpow_one]
  rw [hzpow] at hC
  have heq := digamma_eq_log_sub z hz 0
  rw [show (2 * 0 + 1) = 1 from rfl,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by norm_num),
      Finset.sum_empty, sub_zero] at heq
  rw [heq, Complex.sub_re, Complex.sub_re, Complex.log_re]
  have e1 : -((2 * z)⁻¹).re ≤ (2 * ‖z‖)⁻¹ := by
    have hn : ‖(2 * z)⁻¹‖ = (2 * ‖z‖)⁻¹ := by rw [norm_inv, norm_mul, Complex.norm_ofNat]
    calc -((2 * z)⁻¹).re ≤ ‖(2 * z)⁻¹‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ = (2 * ‖z‖)⁻¹ := hn
  have e2 : -(digammaRemainderIoi z 1).re ≤ C * (‖z‖)⁻¹ :=
    le_trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) hC
  have efr : (2 * ‖z‖)⁻¹ + C * (‖z‖)⁻¹ = (1 / 2 + C) / ‖z‖ := by field_simp
  linarith [e1, e2, efr]
end
end CertificatePort69
section CertificatePort70
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Metric Real
open scoped ENNReal
private theorem lintegral_ofReal_inv_norm_closedBall {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall (0 : ℂ) r, ENNReal.ofReal ‖s‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have heqon : Set.EqOn
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 •
        (closedBall (0 : ℂ) r).indicator (fun w ↦ ENNReal.ofReal ‖w‖⁻¹)
          (Complex.polarCoord.symm p))
      ((Set.Ioc 0 r ×ˢ Set.Ioo (-π) π).indicator (fun _ ↦ 1))
      (Set.Ioi 0 ×ˢ Set.Ioo (-π) π) := by
    rintro ⟨x, y⟩ ⟨hx : (0 : ℝ) < x, hy₁, hy₂⟩
    have hnorm : ‖(Complex.polarCoord.symm (x, y) : ℂ)‖ = x := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hx]
    by_cases h : x ≤ r <;>
      simp [-Complex.polarCoord_symm_apply, mem_closedBall, dist_zero_right, hnorm, hx, hy₁, hy₂,
        h, ENNReal.mul_inv_cancel (by simp [hx] : ENNReal.ofReal x ≠ 0) ENNReal.ofReal_ne_top]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) heqon,
    setLIntegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo),
    Set.prod_inter_prod, Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, Set.inter_self,
    setLIntegral_const, one_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ r - 0)]
  congr 1
  ring
private theorem lintegral_ofReal_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall ρ r, ENNReal.ofReal ‖s - ρ‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_right_eq_self _ ρ,
    ← lintegral_ofReal_inv_norm_closedBall hr, ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_congr fun s ↦ ?_
  simp [Set.indicator, mem_closedBall, dist_eq_norm]
private theorem measurable_inv_norm_sub (ρ : ℂ) : Measurable (fun s : ℂ ↦ ‖s - ρ‖⁻¹) :=
  (continuous_norm.comp (continuous_id.sub continuous_const)).measurable.inv
theorem integrableOn_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ ‖s - ρ‖⁻¹) (closedBall ρ r) := by
  refine ⟨(measurable_inv_norm_sub ρ).aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_norm, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    lintegral_ofReal_inv_norm_sub_closedBall ρ hr]
  exact ENNReal.ofReal_lt_top
end
end CertificatePort70
section CertificatePort71
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex MeasureTheory Metric Set Filter Topology
private theorem analyticOnNhd_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_ne
private theorem analyticOnNhd_deriv_riemannZeta_ne_one :
    AnalyticOnNhd ℂ (deriv riemannZeta) {s : ℂ | s ≠ 1} :=
  fun s hs ↦ (analyticOnNhd_riemannZeta_ne_one s hs).deriv
private theorem analyticOnNhd_riemannZeta_upperHalfPlane :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.im} :=
  DifferentiableOn.analyticOnNhd (fun s hs ↦
    (differentiableAt_riemannZeta (by rintro rfl; simp at hs)).differentiableWithinAt)
    (isOpen_lt continuous_const continuous_im)
private theorem isConnected_upperHalfPlane : IsConnected {s : ℂ | 0 < s.im} :=
  (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩
private theorem im_pos_of_mem_rectangle {z w s : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hs : s ∈ Rectangle z w) : 0 < s.im := by
  simp only [Rectangle, mem_reProdIm, mem_uIcc] at hs
  rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
private theorem continuous_riemannZeta_horizontal {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun σ h ↦ ht (by simpa using congrArg Complex.im h))
private theorem continuous_riemannZeta_vertical {x : ℝ} (hx : x ≠ 1) :
    Continuous (fun τ : ℝ ↦ riemannZeta ((x : ℂ) + I * (τ : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun τ h ↦ hx (by simpa using congrArg Complex.re h))
private theorem ofReal_add_I_mul_ne_one {σ t : ℝ} (ht : t ≠ 0) :
    (σ : ℂ) + I * (t : ℂ) ≠ 1 := fun h ↦ ht (by simpa using congrArg Complex.im h)
theorem finite_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Rectangle z w ∩ {ρ | riemannZeta ρ = 0}).Finite :=
  finite_rectangle_inter_setOf_eq_zero analyticOnNhd_riemannZeta_upperHalfPlane
    isConnected_upperHalfPlane (fun _ hρ ↦ im_pos_of_mem_rectangle hz hw hρ) (z₀ := 2 + I) (by simp)
    (riemannZeta_ne_zero_of_one_le_re (by simp))
theorem finite_re_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.re '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _
theorem finite_im_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.im '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _
private theorem ofReal_add_I_mul_mem_rectangle {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {σ t : ℝ} (hσ : σ ∈ Icc z.re w.re) (ht : t ∈ Icc z.im w.im) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle z w := by
  rw [Rectangle, mem_reProdIm, Set.uIcc_of_le hre, Set.uIcc_of_le him]
  exact ⟨by simpa using hσ, by simpa using ht⟩
private theorem ofReal_add_I_mul_mem_rectangle_two {t₁ t₂ σ t : ℝ} (h12 : t₁ ≤ t₂)
    (hσ : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) (ht : t ∈ Set.Icc t₁ t₂) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ)) :=
  ofReal_add_I_mul_mem_rectangle (by norm_num) (by simpa using h12)
    (by simp only [mem_Icc]; norm_num; constructor <;> linarith) (by simpa using ht)
private theorem re_le_one_of_riemannZeta_eq_zero {σ t : ℝ}
    (hz : riemannZeta ((σ : ℂ) + I * t) = 0) : σ ≤ 1 :=
  not_lt.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using h.le) hz
private theorem riemannZeta_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) {t : ℝ}
    (ht : t ∈ Set.Icc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := fun σ hσ hzero ↦
  htbad ⟨(σ : ℂ) + I * (t : ℂ),
    ⟨ofReal_add_I_mul_mem_rectangle_two h12 hσ (re_le_one_of_riemannZeta_eq_zero hzero) ht,
      hzero⟩, by simp⟩
private theorem not_eventually_riemannZeta_eq_zero {x : ℂ} (hx : 0 < x.im) :
    ¬ ∀ᶠ z in 𝓝 x, riemannZeta z = 0 := fun hev ↦
  riemannZeta_ne_zero_of_one_le_re (s := 2 + I) (by simp)
    (analyticOnNhd_riemannZeta_upperHalfPlane.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isConnected_upperHalfPlane.isPreconnected hx hev (by simp))
private theorem integrableOn_const_div_sub_closedBall (c ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ c / (s - ρ)) (closedBall ρ r) := by
  refine Integrable.mono' ((integrableOn_inv_norm_sub_closedBall ρ hr).const_mul ‖c‖)
    (measurable_const.div (measurable_id.sub measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [norm_div, div_eq_mul_inv]
private theorem exists_integrableOn_logDeriv_riemannZeta_closedBall {x : ℂ} (hx : 0 < x.im) :
    ∃ r > 0, IntegrableOn (logDeriv riemannZeta) (closedBall x r) := by
  have hax : AnalyticAt ℂ riemannZeta x :=
    analyticOnNhd_riemannZeta_ne_one x (by rintro rfl; simp at hx)
  by_cases hzero : riemannZeta x = 0
  ·
    obtain ⟨n, g, -, -, -, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv hax (not_eventually_riemannZeta_eq_zero hx)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      ((eventually_nhdsWithin_iff.mp heq).and hlogg.eventually_analyticAt)
    have hlt : ∀ {z : ℂ}, z ∈ closedBall x (ε / 2) → dist z x < ε := fun {z} hz ↦
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
    refine ⟨ε / 2, half_pos hε, Integrable.congr
      ((integrableOn_const_div_sub_closedBall (n : ℂ) x (half_pos hε).le).add
        (ContinuousOn.integrableOn_compact (isCompact_closedBall x (ε / 2))
          fun _ hz ↦ (hball (hlt hz)).2.continuousAt.continuousWithinAt)) ?_⟩
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton x)),
      ae_restrict_mem measurableSet_closedBall] with z hzne hzmem
    exact ((hball (hlt hzmem)).1 hzne).symm
  ·
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (hax.eventually_analyticAt.and (hax.continuousAt.eventually_ne hzero))
    refine ⟨ε / 2, half_pos hε, ContinuousOn.integrableOn_compact
      (isCompact_closedBall x (ε / 2)) fun z hz ↦ ?_⟩
    obtain ⟨haz, hzne⟩ := hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    exact (haz.deriv.div haz hzne).continuousAt.continuousWithinAt
theorem integrableOn_logDeriv_riemannZeta_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (logDeriv riemannZeta) (Rectangle z w) := by
  refine LocallyIntegrableOn.integrableOn_isCompact ?_ (isCompact_uIcc.reProdIm isCompact_uIcc)
  intro x hx
  obtain ⟨r, hr, hint⟩ :=
    exists_integrableOn_logDeriv_riemannZeta_closedBall (im_pos_of_mem_rectangle hz hw hx)
  exact ⟨closedBall x r, nhdsWithin_le_nhds (closedBall_mem_nhds x hr), hint⟩
theorem log_norm_riemannZeta_sub_eq_neg_im_integral {σ t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (ht1 : 0 < t₁)
    (hne : ∀ t ∈ Icc t₁ t₂, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖ - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖
      = -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hpathcont : Continuous (fun t : ℝ ↦ (σ : ℂ) + I * t) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (σ : ℂ) + I * t) (Icc t₁ t₂) {s : ℂ | s ≠ 1} :=
    fun t ht ↦ ofReal_add_I_mul_ne_one (ht1.trans_le ht.1).ne'
  have hderiv : ∀ t ∈ Ioo t₁ t₂,
      HasDerivAt (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t) * I) t := fun t ht ↦
    ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one (ht1.trans_le ht.1.le).ne')).differentiableAt.hasDerivAt).comp t
      (by simpa using ((ofRealCLM.hasDerivAt (x := t)).const_mul I).const_add (σ : ℂ))
  have hφcont : ContinuousOn (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc t₁ t₂) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps
  have heq : (fun t : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t) * I / riemannZeta ((σ : ℂ) + I * t))
      = fun t : ℝ ↦ logDeriv riemannZeta ((σ : ℂ) + I * t) * I :=
    funext fun t ↦ by rw [logDeriv_apply, mul_div_right_comm]
  have h := re_integral_div_eq_log_norm_sub h12 hφcont hne hderiv
    (((analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps).mul
      continuousOn_const).div hφcont hne)
  rw [heq, intervalIntegral.integral_mul_const, mul_I_re] at h
  linarith
theorem argVariation_riemannZeta_horizontal_eq_im_integral {a X t : ℝ} (hX : a ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ ∈ Icc a X, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    argVariation a X (fun σ ↦ riemannZeta ((σ : ℂ) + I * t))
      = (∫ σ in a..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hφcont : ContinuousOn (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc a X) :=
    (continuous_riemannZeta_horizontal ht).continuousOn
  have hdcont : Continuous (fun σ : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t)) :=
    analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
      (fun _ ↦ ofReal_add_I_mul_ne_one ht)
  have hderiv : ∀ σ ∈ Ioo a X,
      HasDerivAt (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t)) σ := fun σ _ ↦ by
    have h1 : HasDerivAt (fun σ : ℝ ↦ (σ : ℂ) + I * t) 1 σ := by
      simpa using (ofRealCLM.hasDerivAt (x := σ)).add_const (I * (t : ℂ))
    have hd := ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one ht)).differentiableAt.hasDerivAt).comp σ h1
    rw [mul_one] at hd; exact hd
  rw [argVariation_eq_im_integral hX hφcont hne hderiv (hdcont.continuousOn.div hφcont hne)]
  simp only [logDeriv_apply]
theorem tendsto_argVariation_riemannZeta_vertical_atTop {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun X : ℝ ↦ argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))))
      atTop (𝓝 0) := by
  have key : Tendsto (fun X : ℝ ↦ (riemannZeta ((X : ℂ) + I * (t : ℂ))).arg
      - (riemannZeta ((X : ℂ) + I * ((0 : ℝ) : ℂ))).arg) atTop (𝓝 0) := by
    simpa using (tendsto_arg_riemannZeta_atTop t).sub (tendsto_arg_riemannZeta_atTop 0)
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  rw [argVariation_eq_arg_sub_arg ht
    (continuous_riemannZeta_vertical (by linarith)).continuousOn
    (fun τ _ ↦ riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hX))]
private theorem arg_riemannZeta_ofReal_eq_zero {σ : ℝ} (hσ : 2 ≤ σ) :
    (riemannZeta (σ : ℂ)).arg = 0 := by
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)
      = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := fun n ↦ by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have him : (riemannZeta (σ : ℂ)).im = 0 := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using (by linarith : (1 : ℝ) < σ)),
      tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hsp := Complex.mem_slitPlane_iff.mp
    (riemannZeta_mem_slitPlane_of_two_le_re (s := (σ : ℂ)) (by simpa using hσ))
  exact Complex.arg_eq_zero_iff.mpr ⟨hsp.elim le_of_lt (absurd him), him⟩
private theorem mem_Icc_affine {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.Icc a b :=
  Set.uIcc_of_le hab ▸ add_mul_sub_mem_uIcc hu
private theorem argVariation_riemannZeta_lineSeg_comp {a b : ℝ} (hab : a ≤ b) {P Q : ℂ}
    {g : ℝ → ℂ} (hg : ∀ u : ℝ, lineSeg P Q u = g (a + u * (b - a)))
    (hcont : ContinuousOn (fun x : ℝ ↦ riemannZeta (g x)) (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, riemannZeta (g x) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg P Q u))
      = argVariation a b (fun x : ℝ ↦ riemannZeta (g x)) := by
  rw [show (fun u : ℝ ↦ riemannZeta (lineSeg P Q u))
      = fun u : ℝ ↦ (fun x : ℝ ↦ riemannZeta (g x)) (a + u * (b - a)) from
    funext fun u ↦ by rw [hg u]]
  exact argVariation_comp hab zero_le_one (by fun_prop) (fun u hu ↦ mem_Icc_affine hab hu)
    (by ring) (by ring) hcont hne
private theorem argVariation_riemannZeta_lineSeg_symm {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc (0 : ℝ) 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hfun : (fun u : ℝ ↦ riemannZeta (lineSeg z₁ z₀ u))
      = (fun u : ℝ ↦ (fun v : ℝ ↦ riemannZeta (lineSeg z₀ z₁ v)) (0 + 1 - u)) := by
    funext u; simp only; congr 1; simp only [lineSeg]; push_cast; ring
  rw [hfun]
  exact argVariation_reverse zero_le_one hcont hne
private theorem argVariation_riemannZeta_lineSeg_horizontal_rev {a b t : ℝ} (hab : a ≤ b)
    (ht : t ≠ 0) (hrowcont : Continuous fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
    (hne : ∀ σ ∈ Set.Icc a b, riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    argVariation 0 1
        (fun u ↦ riemannZeta (lineSeg ((b : ℂ) + I * (t : ℂ)) ((a : ℂ) + I * (t : ℂ)) u))
      = - argVariation a b (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
  have heq : ∀ u : ℝ, lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u
      = (((a + u * (b - a) : ℝ)) : ℂ) + I * (t : ℂ) := fun u ↦ by
    simp only [lineSeg]; push_cast; ring
  have hcont : ContinuousOn
      (fun u : ℝ ↦ riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u))
      (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      (fun u _ ↦ by rw [heq u]; exact ofReal_add_I_mul_ne_one ht)
  have hne01 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u) ≠ 0 := fun u hu ↦ by
    rw [heq u]; exact hne _ (mem_Icc_affine hab hu)
  rw [argVariation_riemannZeta_lineSeg_symm hcont hne01,
    argVariation_riemannZeta_lineSeg_comp (g := fun σ : ℝ ↦ (σ : ℂ) + I * (t : ℂ)) hab heq
      hrowcont.continuousOn hne]
private theorem argVariation_riemannZeta_lineSeg_of_two_le_re {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, 2 ≤ (lineSeg z₀ z₁ u).re) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))
      = (riemannZeta z₁).arg - (riemannZeta z₀).arg := by
  have hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      fun u hu h1 ↦ by simpa [h1] using h u hu
  rw [argVariation_eq_arg_sub_arg zero_le_one hcont
    fun u hu ↦ riemannZeta_mem_slitPlane_of_two_le_re (h u hu), lineSeg_one, lineSeg_zero]
theorem tendsto_argVariation_riemannZeta_horizontal_atTop {t : ℝ} (ht : 0 < t)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    Tendsto (fun X : ℝ ↦ argVariation (1 / 2) X
        (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))))
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    continuous_riemannZeta_horizontal ht.ne'
  have hpi : Real.pi * argZeta t = argVariationContourL riemannZeta t := by
    rw [argZeta, ← mul_assoc, mul_one_div, div_self Real.pi_ne_zero, one_mul]
  have hlim := (tendsto_argVariation_riemannZeta_vertical_atTop ht.le).sub_const
    (Real.pi * argZeta t)
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  have hzero :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u)) = 0 := by
    have hsub : Rectangle (2 : ℂ) ((X : ℂ) + I * (t : ℂ)) ⊆ {s : ℂ | 1 < s.re} := fun ρ hρ ↦ by
      simp only [Rectangle, mem_reProdIm, mem_uIcc, show (2 : ℂ).re = 2 from by norm_num,
        show ((X : ℂ) + I * (t : ℂ)).re = X from by simp] at hρ
      rcases hρ.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Set.mem_ofPred.mpr (by linarith)
    have hz0 := rectangleArgVariation_eq_zero_of_analyticOnNhd
      (fun s hs ↦ analyticOnNhd_riemannZeta_ne_one s (by rintro rfl; simp at hs))
      (fun _ hs ↦ riemannZeta_ne_zero_of_one_le_re hs.le) hsub
    rw [rectangleArgVariation] at hz0
    simpa [Complex.re_add_im, mul_comm] using hz0
  have hEb : argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u)) = 0 := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u hu ↦ by
        simp only [lineSeg_re, Complex.re_ofNat, Complex.ofReal_re]
        nlinarith [mul_nonneg hu.1 (by linarith : (0 : ℝ) ≤ X - 2)]),
      arg_riemannZeta_ofReal_eq_zero hX,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
      arg_riemannZeta_ofReal_eq_zero (le_refl 2), sub_self]
  have hEr0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
      = argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))) :=
    argVariation_riemannZeta_lineSeg_comp (g := fun τ : ℝ ↦ (X : ℂ) + I * (τ : ℂ)) ht.le
      (fun u ↦ by simp only [lineSeg]; push_cast; ring)
      (continuous_riemannZeta_vertical (by rintro rfl; norm_num at hX)).continuousOn
      (fun τ _ ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using (by linarith : (1 : ℝ) ≤ X)))
  have hEt0 :
      argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev hX ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  have hEl0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u))
      = - argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg (2 : ℂ) ((2 : ℂ) + I * (t : ℂ)) u)) := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]),
      argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]), neg_sub]
  have hAsplit : argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
      = argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
        + argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    argVariation_trans (by norm_num) hX hrowcont.continuousOn
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  have hAlow :
      argVariation 0 1
          (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) ((1 / 2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num,
      show ((1 / 2 : ℂ) + I * (t : ℂ)) = (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev (by norm_num) ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  rw [hEb, hEr0, hEt0, hEl0] at hzero
  rw [hpi, argVariationContourL]
  linarith [hzero, hAsplit, hAlow]
private theorem abs_arg_le_arcsin_of_norm_sub_one_le {w : ℂ} {δ : ℝ}
    (hw : ‖w - 1‖ ≤ δ) (hδ : δ < 1) : |w.arg| ≤ Real.arcsin δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hw
  have hre1 : |(w - 1).re| ≤ δ := (Complex.abs_re_le_norm _).trans hw
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre1
  have hre : 0 < w.re := by linarith [hre1.1]
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr (by rintro rfl; simp at hre)
  have e3 : (w.re - 1) ^ 2 + w.im ^ 2 ≤ δ ^ 2 := by
    have he : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]; ring
    linarith [pow_le_pow_left₀ (norm_nonneg _) hw 2, he]
  have e1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1d : (0 : ℝ) ≤ 1 - δ ^ 2 := by nlinarith [hδ0, hδ]
  have habs : -(δ * ‖w‖) ≤ w.im ∧ w.im ≤ δ * ‖w‖ :=
    abs_le_of_sq_le_sq' (by
      rw [mul_pow, e1]
      nlinarith [e3, h1d, sq_nonneg (w.re - 1 + δ ^ 2), mul_nonneg h1d
        (by nlinarith [e3] : (0 : ℝ) ≤ δ ^ 2 - (w.re - 1) ^ 2 - w.im ^ 2)]) (by positivity)
  rw [Complex.arg_of_re_nonneg hre.le, abs_le, ← Real.arcsin_neg]
  exact ⟨Real.arcsin_le_arcsin (by rw [le_div_iff₀ hnorm]; linarith [habs.1]),
    Real.arcsin_le_arcsin (by rw [div_le_iff₀ hnorm]; linarith [habs.2])⟩
private theorem integrable_logDeriv_riemannZeta_box {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hcd : c ≤ d) :
    Integrable (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  have hfun : (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ))) ∘
      ⇑Complex.measurableEquivRealProd = logDeriv riemannZeta := funext fun z ↦ by
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply]
    rw [mul_comm I (z.im : ℂ), Complex.re_add_im]
  have hset : Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d)
      = Rectangle ((a : ℂ) + I * (c : ℂ)) ((b : ℂ) + I * (d : ℂ)) := by
    ext z
    simp [Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd,
      and_and_and_comm]
  rw [Measure.prod_restrict]
  change IntegrableOn (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
    (Set.Icc a b ×ˢ Set.Icc c d) volume
  rw [← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
        Complex.measurableEquivRealProd.measurableEmbedding, hfun, hset]
  exact integrableOn_logDeriv_riemannZeta_rectangle (by simpa using hc)
    (by simpa using hc.trans_le hcd)
theorem abs_argVariation_riemannZeta_horizontal_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) :=
    continuous_riemannZeta_horizontal ht
  have hhead : |argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    rw [argVariation_riemannZeta_horizontal_eq_im_integral (by norm_num) ht
      (fun σ hσ ↦ hne σ hσ.1)]
    exact (Complex.abs_im_le_norm _).trans
      (intervalIntegral.norm_integral_le_integral_norm (by norm_num))
  have htail : |argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1) := by
    have hb : ∀ σ : ℝ, 2 ≤ σ →
        |(riemannZeta ((σ : ℂ) + I * t)).arg| ≤ Real.arcsin (Real.pi ^ 2 / 6 - 1) :=
      fun σ hσ ↦ abs_arg_le_arcsin_of_norm_sub_one_le
        (norm_riemannZeta_sub_one_le_of_two_le_re (by simpa using hσ))
        (by nlinarith [Real.pi_lt_d2, Real.pi_pos])
    rw [argVariation_eq_arg_sub_arg hX hrowcont.continuousOn (fun σ hσ ↦
      riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hσ.1))]
    exact (abs_sub _ _).trans (by linarith [hb X (by linarith), hb 2 le_rfl])
  rw [argVariation_trans (by norm_num) hX hrowcont.continuousOn (fun σ hσ ↦ hne σ hσ.1)]
  exact (abs_add_le _ _).trans (by linarith [hhead, htail])
theorem integrableOn_argVariation_riemannZeta_horizontal_bound {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) :
    IntegrableOn (fun t : ℝ ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) (Icc t₁ t₂) := by
  have hbox := integrable_logDeriv_riemannZeta_box (by norm_num : (1 / 2 : ℝ) ≤ 2) ht1 h12
  refine continuous_const.continuousOn.integrableOn_Icc.add
    ((hbox.swap.integral_norm_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_))
  simp only [Function.comp_apply, Prod.swap_prod_mk,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2),
    MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem tendsto_im_integral_logDeriv_row_atTop {t : ℝ} (ht : 0 < t)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Tendsto (fun X : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  refine (tendsto_argVariation_riemannZeta_horizontal_atTop ht hray).congr' ?_
  filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
  exact argVariation_riemannZeta_horizontal_eq_im_integral hX ht.ne' fun σ hσ ↦ hray σ hσ.1
private theorem abs_im_integral_logDeriv_row_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |(∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  rw [← argVariation_riemannZeta_horizontal_eq_im_integral (by linarith) ht
    fun σ hσ ↦ hray σ hσ.1]
  exact abs_argVariation_riemannZeta_horizontal_le hX ht hray
private theorem integrable_integral_logDeriv_riemannZeta_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun t : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc t₁ t₂)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.swap.integral_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Function.comp_apply, Prod.swap_prod_mk, intervalIntegral.integral_of_le hX,
    MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem integrable_integral_logDeriv_riemannZeta_col {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun σ : ℝ ↦ ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc (1 / 2 : ℝ) X)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.integral_prod_left).congr (Filter.Eventually.of_forall fun σ ↦ ?_)
  simp only [intervalIntegral.integral_of_le h12, MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem intervalIntegral_im {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℂ}
    (hF : Integrable F (volume.restrict (Icc a b))) :
    (∫ x in a..b, (F x).im) = (∫ x in a..b, F x).im := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_im (hF.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))
private theorem intervalIntegral₂_eq_setIntegral₂ {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (F : ℝ → ℝ → ℂ) :
    (∫ x in a..b, ∫ y in c..d, F x y) = ∫ x in Icc a b, ∫ y in Icc c d, F x y := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc fun x _ ↦ by
    rw [intervalIntegral.integral_of_le hcd, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem integral_log_norm_riemannZeta_sub_eq {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = -∫ t in t₁..t₂,
          (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hcongr : (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = ∫ σ in (1 / 2 : ℝ)..X,
          -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr ((finite_re_riemannZeta_zeros_rectangle
      (z := (1 / 2 : ℂ) + I * (t₁ : ℂ)) (w := (X : ℂ) + I * (t₂ : ℂ)) (by simpa using ht1)
      (by simpa using ht1.trans_le h12)).measure_zero volume)] with σ hσ hσI
    rw [Set.uIoc_of_le hX] at hσI
    refine log_norm_riemannZeta_sub_eq_neg_im_integral h12 ht1 fun t ht hzero ↦
      hσ ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle (by simpa using hX)
        (by simpa using h12) (by simpa using (⟨hσI.1.le, hσI.2⟩ : σ ∈ Icc (1 / 2 : ℝ) X))
        (by simpa using ht), hzero⟩, by simp⟩
  have hpullσ := intervalIntegral_im hX (integrable_integral_logDeriv_riemannZeta_col ht1 h12 hX)
  have hpullt := intervalIntegral_im h12 (integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX)
  have hswap : (∫ σ in (1 / 2 : ℝ)..X, ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      = ∫ t in t₁..t₂, ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t) := by
    rw [intervalIntegral₂_eq_setIntegral₂ hX h12, intervalIntegral₂_eq_setIntegral₂ h12 hX]
    exact integral_integral_swap (integrable_logDeriv_riemannZeta_box hX ht1 h12)
  rw [hcongr, intervalIntegral.integral_neg]
  congr 1
  rw [hpullσ, hswap, ← hpullt]
private theorem ae_not_mem_im_riemannZeta_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (ht2 : 0 < t₂) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
        ∩ {ρ | riemannZeta ρ = 0}) :=
  compl_mem_ae_iff.mpr ((finite_im_riemannZeta_zeros_rectangle (by simpa using ht1)
    (by simpa using ht2)).measure_zero volume)
private theorem pos_and_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {t : ℝ} (htI : t ∈ Set.uIoc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    0 < t ∧ ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
  rw [Set.uIoc_of_le h12] at htI
  have htIcc : t ∈ Set.Icc t₁ t₂ := Set.Ioc_subset_Icc_self htI
  exact ⟨by linarith [htIcc.1], riemannZeta_ray_ne_zero_of_not_mem_im_zeros h12 htIcc htbad⟩
private theorem aestronglyMeasurable_im_integral_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) :=
  ((integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX).im).aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (Set.uIoc_of_le h12 ▸ Set.Ioc_subset_Icc_self) le_rfl)
theorem intervalIntegrable_argZeta {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    IntervalIntegrable argZeta volume t₁ t₂ := by
  have ht2 : 0 < t₂ := lt_of_lt_of_le ht1 h12
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  set bound : ℝ → ℝ := fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
  set F : ℕ → ℝ → ℝ := fun n t ↦
    (∫ σ in (1 / 2 : ℝ)..((n : ℝ) + 1), logDeriv riemannZeta ((σ : ℂ) + I * t)).im
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := fun n ↦
    aestronglyMeasurable_im_integral_row ht1 h12
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc t₁ t₂ →
      Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t)))
        ∧ ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    filter_upwards [h0T] with t htbad htI
    obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12 htI htbad
    have htend : Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t))) :=
      (tendsto_im_integral_logDeriv_row_atTop htpos hray).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine ⟨htend, le_of_tendsto htend.norm ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact abs_im_integral_logDeriv_row_le
      (by exact_mod_cast Nat.add_one_le_iff.mpr (by lia)) htpos.ne' hray
  have hmeas : AEStronglyMeasurable (fun t ↦ -(Real.pi * argZeta t))
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hFmeas ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).1
  have hbound_int : IntegrableOn bound (Set.uIoc t₁ t₂) volume :=
    Set.uIoc_of_le h12 ▸ (integrableOn_argVariation_riemannZeta_horizontal_bound ht1
      h12).mono_set Set.Ioc_subset_Icc_self
  have hdom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)),
      ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).2
  have hfun : (fun t ↦ -(1 / Real.pi) * -(Real.pi * argZeta t)) = argZeta := funext fun t ↦ by
    rw [neg_mul_neg, ← mul_assoc, one_div_mul_cancel Real.pi_ne_zero, one_mul]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12, ← Set.uIoc_of_le h12]
  exact hfun ▸ (Integrable.mono' hbound_int hmeas hdom).const_mul (-(1 / Real.pi))
theorem finite_setOf_riemannZeta_zero_ray_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    {t : ℝ | (∃ σ : ℝ, (1 / 2 : ℝ) ≤ σ ∧ riemannZeta ((σ : ℂ) + I * t) = 0)
      ∧ t ∈ Set.Icc a b}.Finite := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  refine Set.Finite.subset (finite_im_riemannZeta_zeros_rectangle
    (show (0 : ℝ) < ((1 / 2 : ℂ) + I * (a : ℂ)).im by simpa using ha)
    (show (0 : ℝ) < ((2 : ℂ) + I * (b : ℂ)).im by simpa using hb)) ?_
  rintro t ⟨⟨σ, hσ, hz⟩, htab⟩
  exact ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle_two hab hσ
    (re_le_one_of_riemannZeta_eq_zero hz) htab, hz⟩, by simp⟩
theorem pi_mul_integral_argZeta_eq_sub {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (ht1 : 0 < t₁)
    (hne1 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0)
    (hne2 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) :
    Real.pi * ∫ t in t₁..t₂, argZeta t
      = logNormZetaIntegral t₂ - logNormZetaIntegral t₁ := by
  have h12' : t₁ ≤ t₂ := h12.le
  have ht2 : 0 < t₂ := lt_trans ht1 h12
  have htr : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖)
        atTop (𝓝 (logNormZetaIntegral t)) := fun t ht hne ↦ by
    simpa [logNormZetaIntegral] using intervalIntegral_tendsto_integral_Ioi (1 / 2)
      (integrableOn_log_norm_riemannZeta_Ioi ht hne) tendsto_id
  have hii : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      ∀ X : ℝ, (1 / 2 : ℝ) ≤ X → IntervalIntegrable
        (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖) volume (1 / 2) X :=
    fun t ht hne X hX ↦ (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
      ((integrableOn_log_norm_riemannZeta_Ioi ht hne).mono_set Set.Ioc_subset_Ioi_self)
  have hDtend : Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖)) atTop
      (𝓝 (logNormZetaIntegral t₂ - logNormZetaIntegral t₁)) := by
    refine ((htr t₂ ht2.ne' hne2).sub (htr t₁ ht1.ne' hne1)).congr' ?_
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
    rw [intervalIntegral.integral_sub (hii t₂ ht2.ne' hne2 X hX) (hii t₁ ht1.ne' hne1 X hX)]
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  have hDCT : Tendsto (fun X : ℝ ↦ ∫ t in t₁..t₂,
        (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im) atTop
      (𝓝 (∫ t in t₁..t₂, -(Real.pi * argZeta t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact aestronglyMeasurable_im_integral_row ht1 h12' hX
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
      filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      rw [Real.norm_eq_abs]
      exact abs_im_integral_logDeriv_row_le hX htpos.ne' hray
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h12').mpr
        ((integrableOn_argVariation_riemannZeta_horizontal_bound ht1 h12').mono_set
          Set.Ioc_subset_Icc_self)
    · filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      exact tendsto_im_integral_logDeriv_row_atTop htpos hray
  have huniq : logNormZetaIntegral t₂ - logNormZetaIntegral t₁
      = -∫ t in t₁..t₂, -(Real.pi * argZeta t) :=
    tendsto_nhds_unique (hDtend.congr' (by
      filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact integral_log_norm_riemannZeta_sub_eq ht1 h12' hX)) hDCT.neg
  rw [huniq, intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]
end
end CertificatePort71


