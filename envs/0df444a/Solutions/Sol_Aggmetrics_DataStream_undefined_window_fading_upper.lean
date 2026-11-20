-- Prove2me | solution 1 for Aggmetrics.DataStream.undefined_window_fading_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:35.178339+00:00
-- url     : https://prove2.me/submissions/1dc2ae95-acbe-46e2-a6d4-4e7d4889f876

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
import Theorems.Thm_Aggmetrics_DataStream_undefined_window_indep_const

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p)
    {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t k : ℕ) (hk : ∀ s < k, ε < (1 - α) * α ^ s)
    (hkt : k ≤ t) :
    (μ {ω | ∑ s ∈ range t,
        (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε}).toReal ≤ (1 - p) ^ k := by
  have hsub : {ω | ∑ s ∈ range t,
      (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε} ⊆ ⋂ s ∈ range k, (A s)ᶜ := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
    intro s hs hAs
    simp only [Set.mem_setOf_eq] at hω
    have hnn : ∀ i ∈ range t,
        0 ≤ (1 - α) * α ^ i * (A i).indicator (fun _ => (1 : ℝ)) ω := fun i _ =>
      mul_nonneg (mul_nonneg (by linarith) (pow_nonneg h0 i))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    have hle := Finset.single_le_sum hnn (Finset.mem_range.mpr (lt_of_lt_of_le hs hkt))
    have h2 : (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω = (1 - α) * α ^ s := by
      simp [Set.indicator_of_mem hAs]
    rw [h2] at hle
    have := hk s hs
    linarith
  calc _ ≤ (μ (⋂ s ∈ range k, (A s)ᶜ)).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ = (1 - p) ^ k := undefined_window_indep_const μ A hA hmeas p hp k
end Aggmetrics.DataStream
