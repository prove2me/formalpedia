-- Prove2me | Definitions.Def_SourceProof_97d4630f3ae7c9c2d2a46808
-- name    : SourceProof_97d4630f3ae7c9c2d2a46808
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:40:41.567282+00:00
-- url     : https://prove2.me/theorems/3885f800-5f0c-4e5e-922d-4a34d9df396a
-- title:
--   LevyStochCalc source module: SourceProof_97d4630f3ae7c9c2d2a46808
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.tendsto_cadlagCondExp_nhdsGT` comes from the `LevyStochCalc.Driver.CadlagMartingale` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_97d4630f3ae7c9c2d2a46808 (t : ℝ) (ω : Ω) :
    Tendsto (fun s => D.cadlagCondExp ξ s ω) (𝓝[>] t) (𝓝 (D.cadlagCondExp ξ t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · have hev : (fun _ : ℝ => ∫ ω', ξ ω' ∂P) =ᶠ[𝓝[>] t] fun s => D.cadlagCondExp ξ s ω := by
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs
      rw [LevyStochCalc.Driver.LevyDriver.cadlagCondExp_of_neg hs.2]
    rw [LevyStochCalc.Driver.LevyDriver.cadlagCondExp_of_neg ht]
    exact Tendsto.congr' hev tendsto_const_nhds
  · have hmaps : Set.MapsTo Real.toNNReal (Set.Ioi t) (Set.Ioi (Real.toNNReal t)) := by
      intro s hs
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ht).2 hs
    have hcomp : ContinuousWithinAt
        (fun s : ℝ => LevyStochCalc.Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal s) ω)
        (Set.Ioi t) t :=
      (LevyStochCalc.Probability.continuousWithinAt_condExpModif (ℱ := D.filtration.rightCont) (ξ := ξ)
        (Real.toNNReal t) ω).comp continuous_real_toNNReal.continuousWithinAt hmaps
    have hev : (fun s : ℝ =>
          LevyStochCalc.Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal s) ω)
        =ᶠ[𝓝[>] t] fun s => D.cadlagCondExp ξ s ω := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [LevyStochCalc.Driver.LevyDriver.cadlagCondExp_of_nonneg (ht.trans (le_of_lt hs))]
    rw [LevyStochCalc.Driver.LevyDriver.cadlagCondExp_of_nonneg ht]
    exact Tendsto.congr' hev hcomp
end LevyDriver

end LevyStochCalc.Driver


