-- Prove2me | solution 1 for Aggmetrics.DataStream.undefined_window_fading_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:34.671005+00:00
-- url     : https://prove2.me/submissions/d4a306cc-3b38-4f45-93e9-299d3f58fceb

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
import Theorems.Thm_Aggmetrics_DataStream_undefined_window_indep_const
import Theorems.Thm_Aggmetrics_DataStream_evicted_change_bound


set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p)
    {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t k : ℕ) (hk : α ^ k ≤ ε) :
    (1 - p) ^ k ≤ (μ {ω | ∑ s ∈ range t,
        (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε}).toReal := by
  have hsub : (⋂ s ∈ range k, (A s)ᶜ) ⊆ {ω | ∑ s ∈ range t,
      (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε} := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range] at hω
    simp only [Set.mem_setOf_eq]
    have hsum : ∑ s ∈ range t, (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω
        = ∑ s ∈ (range t).filter (fun s => k ≤ s),
            (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      by_cases hs : k ≤ s
      · simp [hs]
      · have hsk : s < k := not_le.mp hs
        simp [hs, Set.indicator_apply, hω s hsk]
    rw [hsum]
    calc _ ≤ |∑ s ∈ (range t).filter (fun s => k ≤ s),
              (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω| := le_abs_self _
      _ ≤ α ^ k := evicted_change_bound h0 h1 k _ (fun s hs => (Finset.mem_filter.mp hs).2)
            (fun s => (A s).indicator (fun _ => (1 : ℝ)) ω)
            (fun s => by by_cases h : ω ∈ A s <;> simp [h])
      _ ≤ ε := hk
  calc (1 - p) ^ k = (μ (⋂ s ∈ range k, (A s)ᶜ)).toReal :=
        (undefined_window_indep_const μ A hA hmeas p hp k).symm
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
end Aggmetrics.DataStream
