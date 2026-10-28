-- Prove2me | Definitions.Def_OAIQ035K045
-- name    : OAIQ035K045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:10:51.72963+00:00
-- url     : https://prove2.me/theorems/aa797504-5959-4e94-9a3f-7031582eb288
-- title:
--   Definitions bundle OAIQ035K045 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 3 definitions and 1 theorem. The definitions and types are `OAI.MetricKMedian.ScalarTransfer.stdK`, `OAI.MetricKMedian.SparseIntegerLaw.expectation`, `OAI.MetricKMedian.Taper.physicalGraphData`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_NormalizedTransfer`, `KMedian_Rounding_RationalPhysicalGraph`, `KMedian_Rounding_RationalTaperData`, `KMedian_Sparse_SparseRealExpectation`.
--
--   **Imports.** It imports the bundles `OAIQ035K029`, `OAIQ035K035`, `OAIQ035K036` and `OAIQ035K037` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival`, `OAI.MetricKMedian.SparseHistories.accumulated_drift_up_to`, `OAI.MetricKMedian.SparseHistories.count_tail_up_to`, `OAI.MetricKMedian.SparseHistories.history_contraction` and `OAI.MetricKMedian.Taper.physical_sparse_graph`; the proofs of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds`, `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_lower`, `OAI.MetricKMedian.SparseEnumeratedBatch.pair_le`, `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq`, `OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail`, `OAI.MetricKMedian.SparseHistories.accumulated_drift_up_to`, `OAI.MetricKMedian.SparseHistories.count_tail_up_to`, `OAI.MetricKMedian.SparseHistories.history_contraction` and `OAI.MetricKMedian.Taper.physical_sparse_graph`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K029
import Definitions.Def_OAIQ035K035
import Definitions.Def_OAIQ035K036
import Definitions.Def_OAIQ035K037

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_NormalizedTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def stdK (p k x w r : ℝ) (s : Bool) : ℝ :=
  N p k s-stdB p x w s*r+(8/5)*p*w^2

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperData
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

theorem rational_data (g P : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    let N := rationalRadius g P d
    let q := sourceMarginals g P d own Δ
    0 ≤ N ∧ (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧ (∀ i ∈ own, q i=1) ∧
      (∀ i, q i < 1 → N*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ N*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P (fun i => (d i:ℝ)) (1/R) → (N:ℝ) ≤ R) := by
  by_cases hc : 1 ≤ rationalColocatedMass g d
  · have hcR : 1 ≤ colocatedMass g (fun i => (d i:ℝ)) := by
      rw [← cast_rationalColocatedMass]
      exact_mod_cast hc
    obtain ⟨hq0,hq1,hs,hn,ho,hz⟩ := zero_data g d own Δ hg hunit hcR hown howncard
    dsimp only
    simp only [rationalRadius,sourceMarginals,ite_eq_left hc]
    refine ⟨le_refl _,hq0,hq1,hs,hn,ho,?_,?_,?_⟩
    · intro i _; simpa only [zero_mul] using hd i
    · intro i hi; simp only [hz i hi,zero_mul,le_refl]
    · intro R hR _; simpa only [Rat.cast_zero] using hR.le
  · have hcR : colocatedMass g (fun i => (d i:ℝ)) < 1 := by
      rw [← cast_rationalColocatedMass]
      exact_mod_cast (lt_of_not_ge hc)
    obtain ⟨hN,hq0,hq1,hs,hn,ho,hl,hu,hr⟩ := positive_data g P d Δ hg hunit hP hP1 hd htotal hcR
    dsimp only
    simp only [rationalRadius,sourceMarginals,ite_eq_right hc]
    exact ⟨hN.le,hq0,hq1,hs,hn,fun i hi => ho i (hown i hi),hl,hu,hr⟩

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ} {X : Type*} [PseudoMetricSpace X]

noncomputable def physicalGraphData (Δ : ℕ) (g P : ℚ) (d : I → I → ℚ)
    (location : I → X) (own : I → Finset (I))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
    (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
    GraphData Δ (g:ℝ) (P:ℝ) location own where
  radius i := (rationalRadius g P (d i):ℝ)
  marginal h i := (sourceMarginals g P (d i) (own i) Δ h:ℝ)
  radius_nonneg i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).1
  marginal_nonneg h i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.1 h
  marginal_le_one h i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.1 h
  incoming_mass i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.1
  incoming_count i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.1
  own_certain i h he := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.1 h he
  lower h i he := by
    rw [hdist]
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.1 h (by exact_mod_cast he)
  upper h i he := by
    rw [hdist]
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.2.1 h (by exact_mod_cast he)
  minimal i R hR he := by
    simp only [hdist] at he
    exact (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.2.2 R hR he

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

noncomputable def expectation (μ : SparseIntegerLaw α) (f : α → ℝ) : ℝ :=
  μ.realIndex.expect (fun i => f μ.states[i.val])

end MetricKMedian.SparseIntegerLaw

end OAI
end


