-- Prove2me | solution 1 for Aggmetrics.DataStream.undefined_latency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:59.850953+00:00
-- url     : https://prove2.me/submissions/8362bda2-0124-44fd-81a6-7e88bee122ee

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
import Theorems.Thm_Aggmetrics_DataStream_undefined_window_indep

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (q : ℕ → ℝ) (hq : ∀ s, (μ (A s)).toReal = q s) (W : ℕ) :
    (μ (⋂ s ∈ range W, (A s)ᶜ)).toReal = ∏ s ∈ range W, (1 - q s) := by
  rw [undefined_window_indep μ A hA hmeas]
  exact Finset.prod_congr rfl (fun s _ => by rw [hq s])
end Aggmetrics.DataStream
