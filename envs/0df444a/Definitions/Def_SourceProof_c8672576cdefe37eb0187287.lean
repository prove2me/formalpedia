-- Prove2me | Definitions.Def_SourceProof_c8672576cdefe37eb0187287
-- name    : SourceProof_c8672576cdefe37eb0187287
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:41:07.485173+00:00
-- url     : https://prove2.me/theorems/ff9fd440-bfce-43ee-aab0-276bf4aac5ed
-- title:
--   LevyStochCalc source module: SourceProof_c8672576cdefe37eb0187287
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT` comes from the `LevyStochCalc.Driver.CadlagMartingale` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CadlagMartingale_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg conditional-expectation martingale of a Lévy driver

`Probability/CondExpModification.lean` builds a right-continuous modification of
`t ↦ 𝔼[ξ | ℱ₊ t]` indexed by `ℝ≥0`, the index type the càdlàg machinery needs. Reindexing by `ℝ`
means saying what happens before time `0`, where the constant `𝔼 ξ` is the right answer: it is
`𝔼[ξ | ℱ₊ t]` there by Blumenthal's 0-1 law (`Driver/GermIndep.lean`), and being constant it is
measurable for every σ-algebra, which the modification's value at `0` is not.

## Main statements

* `LevyDriver.cadlagCondExp` — the reindexed process.
* `LevyDriver.martingale_cadlagCondExp` — it is a martingale for `ℱ₊`.
* `LevyDriver.cadlagCondExp_ae_eq` — it agrees with `𝔼[ξ | ℱ₊ t]` at every fixed `t`.
* `LevyDriver.tendsto_cadlagCondExp_nhdsGT`, `LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT`
  — right continuity of every path, and left limits almost surely.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν) (ξ : Ω → ℝ)

variable {D ξ}


theorem _root_.Prove2MeSourceProof.h_c8672576cdefe37eb0187287 :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ L : ℝ,
      Tendsto (fun s => D.cadlagCondExp ξ s ω) (𝓝[<] t) (𝓝 L) := by
  filter_upwards [LevyStochCalc.Probability.ae_exists_tendsto_condExpModif_nhdsLT
    (μ := P) (ℱ := D.filtration.rightCont) (ξ := ξ)] with ω hω t
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨∫ ω', ξ ω' ∂P, Tendsto.congr' ?_ tendsto_const_nhds⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [LevyStochCalc.Driver.LevyDriver.cadlagCondExp_of_neg (lt_of_lt_of_le hs ht)]
  · obtain ⟨L, hL⟩ := hω (Real.toNNReal t)
    have hmap : Tendsto Real.toNNReal (𝓝[<] t) (𝓝[<] (Real.toNNReal t)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_real_toNNReal.tendsto t).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsLT ht] with s hs
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg hs.1.le).2 hs.2
    refine ⟨L, Tendsto.congr' ?_ (hL.comp hmap)⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    rw [Function.comp_apply, LevyStochCalc.Driver.LevyDriver.cadlagCondExp_of_nonneg hs.1.le]
end LevyDriver

end LevyStochCalc.Driver


