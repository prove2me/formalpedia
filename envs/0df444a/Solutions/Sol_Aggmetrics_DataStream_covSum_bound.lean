-- Prove2me | solution 1 for Aggmetrics.DataStream.covSum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:34:38.217171+00:00
-- url     : https://prove2.me/submissions/12ead2ea-713d-4226-a9b4-afe91a5785f7

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_covSum_succ
import Theorems.Thm_Aggmetrics_DataStream_einf_eq
import Theorems.Thm_Aggmetrics_DataStream_tsum_shift
import Theorems.Thm_Aggmetrics_DataStream_lag_tail

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {ρ : ℕ → ℝ} (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) (t : ℕ) :
    |covSum ρ α t - kappaVar ρ α| ≤ max 2 |kappaVar ρ α| * α ^ t := by
  have hfix : kappaVar ρ α
      = α ^ 2 * kappaVar ρ α + 2 * α * (1 - α) * einf ρ α + (1 - α) ^ 2 := by
    rw [einf_eq]
    unfold kappaVar kappaFactor
    rw [tsum_shift]
    have : (1 + α) ≠ 0 := by linarith
    field_simp
    ring
  have hM2 : (2 : ℝ) ≤ max 2 |kappaVar ρ α| := le_max_left _ _
  induction t with
  | zero =>
    simp only [covSum, Finset.range_zero, Finset.sum_empty, zero_sub, abs_neg, pow_zero, mul_one]
    exact le_max_right _ _
  | succ t ih =>
    have hrec := covSum_succ ρ hρ0 α t
    have hE := lag_tail hρ h0 h1 t
    have hdiff : covSum ρ α (t + 1) - kappaVar ρ α
        = α ^ 2 * (covSum ρ α t - kappaVar ρ α)
          + 2 * α * (1 - α) * (lagSum ρ α t - einf ρ α) := by
      rw [hrec]
      linear_combination (-1 : ℝ) * hfix
    rw [hdiff]
    have hαt : 0 ≤ α ^ t := pow_nonneg h0 t
    have hc : 0 ≤ 2 * α * (1 - α) := by
      have : 0 ≤ 1 - α := by linarith
      positivity
    calc |α ^ 2 * (covSum ρ α t - kappaVar ρ α) + 2 * α * (1 - α) * (lagSum ρ α t - einf ρ α)|
        ≤ |α ^ 2 * (covSum ρ α t - kappaVar ρ α)|
          + |2 * α * (1 - α) * (lagSum ρ α t - einf ρ α)| := by
          first | exact abs_add_le _ _ | exact abs_add _ _
      _ = α ^ 2 * |covSum ρ α t - kappaVar ρ α|
          + 2 * α * (1 - α) * |lagSum ρ α t - einf ρ α| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2), abs_of_nonneg hc]
      _ ≤ α ^ 2 * (max 2 |kappaVar ρ α| * α ^ t) + 2 * α * (1 - α) * α ^ t :=
        add_le_add (mul_le_mul_of_nonneg_left ih (by positivity))
          (mul_le_mul_of_nonneg_left hE hc)
      _ ≤ max 2 |kappaVar ρ α| * α ^ (t + 1) := by
        have key : ∀ M : ℝ, 2 ≤ M → α ^ 2 * (M * α ^ t) + 2 * α * (1 - α) * α ^ t
            ≤ M * α ^ (t + 1) := by
          intro M hM
          rw [pow_succ α t]
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hαt h0) (by linarith : (0 : ℝ) ≤ 1 - α))
            (by linarith : (0 : ℝ) ≤ M - 2)]
        exact key _ hM2
end Aggmetrics.DataStream
