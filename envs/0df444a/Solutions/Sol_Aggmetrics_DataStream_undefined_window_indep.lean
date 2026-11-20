-- Prove2me | solution 1 for Aggmetrics.DataStream.undefined_window_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:14.361078+00:00
-- url     : https://prove2.me/submissions/56a6596d-f730-4736-960a-1e3215decad0

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
import Theorems.Thm_Aggmetrics_DataStream_iIndepSet_compl_meas_biInter

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ι → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
    (μ (⋂ i ∈ S, (A i)ᶜ)).toReal = ∏ i ∈ S, (1 - (μ (A i)).toReal) := by
  rw [iIndepSet_compl_meas_biInter μ A hA S, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [measure_compl (hmeas i) (measure_ne_top μ _), measure_univ,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
end Aggmetrics.DataStream
