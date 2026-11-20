-- Prove2me | solution 1 for Aggmetrics.DataStream.undefined_window_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:44.310861+00:00
-- url     : https://prove2.me/submissions/cc7df558-7093-4840-87dd-56840107ea0e

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : ℕ) (A : Fin W → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : μ (⋂ i, (A i)ᶜ) = ∏ i, μ (A i)ᶜ)
    (p : ENNReal) (hp : ∀ i, μ (A i) = p) :
    μ (⋂ i, (A i)ᶜ) = (1 - p) ^ W := by
  rw [hindep]
  have hcompl : ∀ i, μ (A i)ᶜ = 1 - p := fun i => by
    rw [measure_compl (hA i) (measure_ne_top μ _), hp, measure_univ]
  simp [hcompl]
end Aggmetrics.DataStream
