-- Prove2me | Definitions.Def_OAIQ035K037
-- name    : OAIQ035K037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:01:25.000897+00:00
-- url     : https://prove2.me/theorems/0e0afcf4-f0d2-49e8-81f6-fcc9ec9819b5
-- title:
--   Definitions bundle OAIQ035K037 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Rounding_RationalTaperZero`.
--
--   **Imports.** It imports the bundle `OAIQ035K026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K045`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K026

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

theorem zero_data (g : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ)
    (_hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hcol : 1 ≤ colocatedMass g (fun i => (d i:ℝ)))
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    let q := zeroMarginal d own Δ
    (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧ (∑ i, g*q i=1) ∧
      (∑ i, q i=Δ) ∧ (∀ i ∈ own, q i=1) ∧ (∀ i, 0 < q i → d i=0) := by
  let Z := zeroSources d
  have hz : (Z.card:ℝ)*(g:ℝ)=colocatedMass g (fun i => (d i:ℝ)) := by
    simp only [Z,zeroSources,colocatedMass,← sum_filter,sum_const,nsmul_eq_mul,
      Rat.cast_eq_zero]
  have hzcard : Δ ≤ Z.card := by
    have hh : (Δ:ℝ) ≤ Z.card := by nlinarith only [hcol,hz,hunit]
    exact_mod_cast hh
  have hsub : own ⊆ Z := by intro i hi; exact mem_filter.mpr ⟨mem_univ _,hown i hi⟩
  obtain ⟨hownS,hSZ,hcard⟩ := extend_spec own Z Δ hsub howncard hzcard
  change (∀ i, 0 ≤ zeroMarginal d own Δ i) ∧ _
  have hsum : (∑ i, zeroMarginal d own Δ i)=(Δ:ℚ) := by
    simp only [zeroMarginal,← sum_filter,filter_univ_mem,sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast hcard
  refine ⟨?_,?_,?_,hsum,?_,?_⟩
  · intro i; unfold zeroMarginal; split_ifs <;> norm_num
  · intro i; unfold zeroMarginal; split_ifs <;> norm_num
  · rw [← mul_sum,hsum]; exact_mod_cast hunit
  · intro i hi; exact ite_eq_left (hownS hi)
  · intro i hi
    have hm : i ∈ zeroSelection d own Δ := by
      by_contra hn
      simp only [zeroMarginal,ite_eq_right hn] at hi
      exact lt_irrefl _ hi
    exact (mem_filter.mp (hSZ hm)).2

end MetricKMedian.Taper
end
end

end OAI
end


