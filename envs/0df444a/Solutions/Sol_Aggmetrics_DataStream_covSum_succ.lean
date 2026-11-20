-- Prove2me | solution 1 for Aggmetrics.DataStream.covSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:55.919842+00:00
-- url     : https://prove2.me/submissions/a991b68b-5c68-4f3e-9e92-417bef3a07b0

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_natAbs_sub_of_lt
import Theorems.Thm_P2M_Aggmetrics_DataStream_natAbs_sub_of_lt__f4533c285d97
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_last
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_succ


set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 1) (α : ℝ) (t : ℕ) :
    covSum ρ α (t + 1)
      = α ^ 2 * covSum ρ α t + 2 * α * (1 - α) * lagSum ρ α t + (1 - α) ^ 2 := by
  have hE : ∑ i ∈ range t, fadeWeight α t i * ρ (t - i) = lagSum ρ α t := by
    unfold lagSum
    have h := Finset.sum_range_reflect (fun d => (1 - α) * α ^ d * ρ (d + 1)) t
    rw [← h]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hit := Finset.mem_range.mp hi
    unfold fadeWeight
    have e : t - i = (t - 1 - i) + 1 := by omega
    rw [e]
  have hI : ∀ i ∈ range t,
      ∑ j ∈ range (t + 1), fadeWeight α (t + 1) i * fadeWeight α (t + 1) j
          * ρ (Int.natAbs ((i : ℤ) - j))
        = α ^ 2 * ∑ j ∈ range t, fadeWeight α t i * fadeWeight α t j * ρ (Int.natAbs ((i : ℤ) - j))
          + α * (1 - α) * (fadeWeight α t i * ρ (t - i)) := by
    intro i hi
    have hit : i < t := Finset.mem_range.mp hi
    rw [Finset.sum_range_succ]
    have h1 : ∀ j ∈ range t, fadeWeight α (t + 1) i * fadeWeight α (t + 1) j
          * ρ (Int.natAbs ((i : ℤ) - j))
        = α ^ 2 * (fadeWeight α t i * fadeWeight α t j * ρ (Int.natAbs ((i : ℤ) - j))) := by
      intro j hj
      rw [fadeWeight_succ hit, fadeWeight_succ (Finset.mem_range.mp hj)]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, fadeWeight_succ hit, fadeWeight_last,
      natAbs_sub_of_lt hit]
    ring
  have hL : ∑ j ∈ range (t + 1), fadeWeight α (t + 1) t * fadeWeight α (t + 1) j
        * ρ (Int.natAbs ((t : ℤ) - j))
      = α * (1 - α) * (∑ j ∈ range t, fadeWeight α t j * ρ (t - j)) + (1 - α) ^ 2 := by
    rw [Finset.sum_range_succ]
    have h1 : ∀ j ∈ range t, fadeWeight α (t + 1) t * fadeWeight α (t + 1) j
          * ρ (Int.natAbs ((t : ℤ) - j))
        = α * (1 - α) * (fadeWeight α t j * ρ (t - j)) := by
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      rw [fadeWeight_last, fadeWeight_succ hjt, natAbs_sub_of_lt' hjt]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, fadeWeight_last]
    simp only [sub_self, Int.natAbs_zero, hρ0, mul_one]
    ring
  unfold covSum
  rw [Finset.sum_range_succ, Finset.sum_congr rfl hI, hL, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hE]
  ring
end Aggmetrics.DataStream
