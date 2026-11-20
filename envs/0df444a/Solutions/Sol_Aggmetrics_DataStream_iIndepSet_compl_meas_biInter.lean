-- Prove2me | solution 1 for Aggmetrics.DataStream.iIndepSet_compl_meas_biInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:43.518251+00:00
-- url     : https://prove2.me/submissions/0befe592-3bb2-437f-bf7a-e58e2a108d8b

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ι → Set Ω) (hA : iIndepSet A μ) (S : Finset ι) :
    μ (⋂ i ∈ S, (A i)ᶜ) = ∏ i ∈ S, μ (A i)ᶜ := by
  have hf : iIndepFun (fun i => (A i).indicator fun _ω => (1 : ℝ)) μ := hA.iIndepFun_indicator
  refine hf.meas_biInter (fun i _ => ?_)
  refine MeasurableSpace.measurableSet_comap.mpr ⟨{0}, measurableSet_singleton 0, ?_⟩
  ext ω
  by_cases h : ω ∈ A i <;> simp [Set.indicator, h]
end Aggmetrics.DataStream
