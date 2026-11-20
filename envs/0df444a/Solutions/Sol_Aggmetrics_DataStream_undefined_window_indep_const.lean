-- Prove2me | solution 1 for Aggmetrics.DataStream.undefined_window_indep_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:55.670165+00:00
-- url     : https://prove2.me/submissions/12896a5c-0d63-499a-b348-a1ae5fbc941e

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
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p) (W : ℕ) :
    (μ (⋂ i ∈ range W, (A i)ᶜ)).toReal = (1 - p) ^ W := by
  rw [undefined_window_indep μ A hA hmeas,
    Finset.prod_congr rfl (fun i _ => (by rw [hp i] : 1 - (μ (A i)).toReal = 1 - p)),
    Finset.prod_const, Finset.card_range]
end Aggmetrics.DataStream
