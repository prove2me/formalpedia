-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Gaussian_Moment
-- name    : KLSModular_BrownianMotion_Gaussian_Moment
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:35:58.251052+00:00
-- url     : https://prove2.me/theorems/8fd71939-804d-4268-8004-6618d58ce16f
-- title:
--   Even central moments of real Gaussian laws
-- statement:
--   Vendored from the BrownianMotion library, repository https://github.com/RemyDegenne/brownian-motion, commit a7ad7af662044313bc80a7c0756360fb3745f931. For μ ∈ ℝ, σ ∈ ℝ≥0, and n ∈ ℕ, `centralMoment_two_mul_gaussianReal` states that the 2n-th central moment of the Gaussian law `gaussianReal μ (σ^2)` is σ^(2n) multiplied by the double factorial (2n − 1)!!. The companion result `centralMoment_fun_two_mul_gaussianReal` gives the same equality when the identity function is written as `fun x ↦ x`.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Probability.Distributions.Gaussian.Real
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   lemma centralMoment_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
--       centralMoment id (2 * n) (gaussianReal μ (σ^2))
--       = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1)
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Gaussian/Moment.lean) · `BrownianMotion.Gaussian.Moment` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/Moment.lean#L12-L144 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Gaussian.Moment`, definition bundle `KLSModular_BrownianMotion_Gaussian_Moment`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Distributions.Gaussian.Real

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/Moment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal
namespace ProbabilityTheory
lemma centralMoment_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by
  -- 1. Prove the case n = 0 and proceed with n ≠ 0
  by_cases hn : n = 0
  · simp [hn, centralMoment]
  -- 2. Prove the case σ = 0 and proceed with σ ≠ 0
  by_cases hσ : σ = 0
  · simp [hσ, hn, centralMoment]
  let φ x := σ * Real.sqrt (2 * x) -- used for u sub later
  have hφ_Ioi : Set.Ioi 0 = φ '' Set.Ioi 0 := by
    subst φ
    apply subset_antisymm
    · intros x hx
      rw [Set.mem_Ioi] at hx
      simp only [Nat.ofNat_nonneg, Real.sqrt_mul, Set.mem_image, Set.mem_Ioi]
      exists x^2 / (2 * σ ^ 2)
      simp only [Nat.ofNat_nonneg, Real.sqrt_mul, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, pow_nonneg, Real.sqrt_div', Real.sqrt_sq]
      exact ⟨by positivity, by field_simp; rw [Real.sqrt_sq hx.le]⟩
    · simp only [Nat.ofNat_nonneg, Real.sqrt_mul, Set.image_subset_iff]
      intros x hx
      simp only [Set.mem_Ioi, Set.mem_preimage] at hx ⊢
      positivity
  have h_diff {x} (hx : 0 < x) : DifferentiableAt ℝ φ x := by
    subst φ
    fun_prop (disch := (apply ne_of_gt; positivity))
  have h_inj : Set.InjOn φ (Set.Ioi 0) := by
    simp only [Set.InjOn, Set.mem_Ioi, Nat.ofNat_nonneg, Real.sqrt_mul, mul_eq_mul_left_iff,
      Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_false, NNReal.coe_eq_zero, hσ, φ]
    intros x1 hx1 x2 hx2 hx1x2
    rwa [Real.sqrt_inj (by positivity) (by positivity)] at hx1x2
  have h_deriv {x} (hx : 0 < x) : deriv φ x = σ / (√2 * √x) := by
    subst φ
    simp only [Nat.ofNat_nonneg, Real.sqrt_mul, deriv_const_mul_field',
      deriv_sqrt (f := fun x ↦ x) (x := x) (by fun_prop) hx.ne', deriv_id'', one_div, mul_inv_rev]
    congr
    rw [mul_comm, mul_assoc]
    simp only [mul_inv_rev, mul_eq_mul_left_iff, inv_eq_zero, (Real.sqrt_pos_of_pos hx).ne',
      or_false]
    field_simp
    rw [Real.sq_sqrt (by simp)]
  have hφ_pow {x} (hx : 0 < x) : φ x ^ (2 * n) = σ ^ (2 * n) * (2 * x) ^ n := by
    simp only [φ, Nat.ofNat_nonneg, Real.sqrt_mul]
    ring_nf
    simp_rw [mul_comm _ 2, pow_mul, Real.sq_sqrt zero_le_two, Real.sq_sqrt hx.le]
    ring
  calc centralMoment id (2 * n) (gaussianReal μ (σ^2))
  -- 3. E_{X ∼ N(μ, σ²)}[(X - E[X])^(2n)] = ∫ x^(2n) dP(x) with P = N(0, σ^2)
  _ = ∫ x, x ^ (2 * n) ∂gaussianReal 0 (σ^2) := by
    simp only [centralMoment, id_eq, integral_id_gaussianReal, Pi.pow_apply, Pi.sub_apply]
    rw [show μ = 0 + μ by ring_nf, ← gaussianReal_map_add_const,
      (measurableEmbedding_addRight μ).integral_map]
    simp
  -- 4. ... = ∫ x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
  _ = ∫ x, x^(2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2)) * Real.exp (-x ^ 2 / (2 * σ ^ 2)) := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, hσ,
      integral_gaussianReal_eq_integral_smul, gaussianPDFReal_def, NNReal.coe_pow,
      NNReal.zero_le_coe, pow_nonneg, Real.sqrt_mul', Nat.ofNat_nonneg, Real.sqrt_mul,
      Real.sqrt_sq, mul_inv_rev, sub_zero, smul_eq_mul]
    ring_nf
  -- 5. ... = 2 ∫_(0, ∞) x^(2n) / √(2πσ²) e^(- x² / 2σ^2) dx
  _ = 2 * ∫ x in Set.Ioi 0, x ^ (2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2))
                            * Real.exp (-x ^ 2 / (2 * σ ^ 2)) := by
    conv_lhs =>
      rhs
      ext x
      rw [show x ^ (2 * n) / √(2 * Real.pi * ↑σ ^ 2) * Real.exp (-x ^ 2
              / (2 * ↑σ ^ 2)) = (fun u => u ^ (2 * n) / √(2 * Real.pi * ↑σ ^ 2)
              * Real.exp (-u ^ 2 / (2 * ↑σ ^ 2))) |x| by
            simp only [NNReal.zero_le_coe, pow_nonneg, Real.sqrt_mul', Nat.ofNat_nonneg,
              Real.sqrt_mul, Real.sqrt_sq, sq_abs, mul_eq_mul_right_iff, Real.exp_ne_zero,
              or_false]
            rw [pow_mul, ← sq_abs]
            ring_nf]
    rw [integral_comp_abs
      (f := (fun u => u ^ (2 * n) / √(2 * Real.pi * σ ^ 2) * Real.exp (-u ^ 2 / (2 * σ ^ 2))))]
-- 6. ... = 2 ∫_(0, ∞) φ(x)^(2n) / √(2πσ²) e^(- φ(x)² / 2σ^2) |φ'(x)| dx
-- where φ(x) = σ √(2x) and φ'(x) = σ / (√2 * √x), i.e.,
-- u sub with y = x^2 / (2σ²) or x = σ √(2y).
  _ = 2 * ∫ x in Set.Ioi 0, φ x ^ (2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2))
        * Real.exp (-φ x ^ 2 / (2 * σ ^ 2)) * |deriv φ x| := by
    conv_lhs => rw [hφ_Ioi]
    rw [integral_image_eq_integral_abs_deriv_smul (f' := deriv φ) measurableSet_Ioi]
    · congr with x
      simp only [NNReal.zero_le_coe, pow_nonneg, Real.sqrt_mul', Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.sqrt_sq, smul_eq_mul]
      group
    · exact fun x hx ↦ (h_diff (by simpa using hx)).hasDerivAt.hasDerivWithinAt
    · exact h_inj
  _ = 2 * ∫ x in Set.Ioi 0, φ x ^ (2 * n) / (Real.sqrt (2 * Real.pi * σ ^ 2))
        * Real.exp (-x) * |deriv φ x| := by
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    simp only [Set.mem_Ioi] at hx
    congr
    simp only [Nat.ofNat_nonneg, Real.sqrt_mul, φ]
    ring_nf
    field_simp
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  -- 7. ... = σ^(2n) 2^n / √π Γ(n + 1/2)
  _ = σ ^ (2 * n) * 2 ^ n / √Real.pi * Real.Gamma (n + 1/2) := by
    rw [Real.Gamma_eq_integral (by positivity)]
    simp only [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    simp only [Set.mem_Ioi] at hx
    rw [h_deriv hx, hφ_pow hx]
    simp only [NNReal.zero_le_coe, pow_nonneg, Real.sqrt_mul', Nat.ofNat_nonneg, Real.sqrt_mul,
      Real.sqrt_sq, one_div]
    rw [abs_of_nonneg (by positivity)]
    field_simp
    ring_nf
    have : x ^ n = x ^ (-(1 : ℝ) / 2 + n) * √x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add_of_nonneg (by positivity) _ (by positivity)]
      · ring_nf
        rw [Real.rpow_natCast]
      · rw [add_comm, neg_div, ← sub_eq_add_neg]
        simp only [one_div, sub_nonneg]
        calc (2 : ℝ)⁻¹
        _ ≤ 1 := by norm_num
        _ ≤ n := by norm_cast; omega
    rw [this, Real.sq_sqrt zero_le_two]
    ring
  -- 8. ... = σ^(2n) (2n - 1)!!
  _ = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by
    rw [Real.Gamma_nat_add_half, ← sub_eq_zero]
    field_simp
    ring
lemma centralMoment_fun_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) :=
  centralMoment_two_mul_gaussianReal ..
end ProbabilityTheory


