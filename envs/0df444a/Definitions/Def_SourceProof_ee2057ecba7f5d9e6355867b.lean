-- Prove2me | Definitions.Def_SourceProof_ee2057ecba7f5d9e6355867b
-- name    : SourceProof_ee2057ecba7f5d9e6355867b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:48:53.795382+00:00
-- url     : https://prove2.me/theorems/92bd7769-efc6-4146-8e44-7639ee5cc629
-- title:
--   LevyStochCalc source module: SourceProof_ee2057ecba7f5d9e6355867b
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Generator.exists_progressive_modification_of_rightCont` comes from the `LevyStochCalc.BSDEJ.DriftModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001
import Definitions.Def_SourceProof_98598376fa8eb2edcffbba89

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift progressive for the right-continuous filtration

A real process that is progressively measurable for the right-continuous filtration `ℱ₊` has a
modification, equal to it almost everywhere on `Ω × [0, T]`, that is progressively measurable for
`ℱ` itself. The modification is the pointwise `limsup` of the moving averages of the process over
the windows `[s - 2c, s - c]` lying strictly to the left of `s`: each such average is
`ℱ`-progressive because it reads the process only before `s`, and Lebesgue's differentiation
theorem identifies the limit with the process at almost every time.
-/

open MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### Moving averages over a window strictly to the left -/

/-! ### Lebesgue differentiation along the left windows -/

/-! ### The modification -/


theorem _root_.Prove2MeSourceProof.h_ee2057ecba7f5d9e6355867b (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∃ b' : Ω → ℝ → ℝ, Measurable (Function.uncurry b') ∧
      Probability.ProgressivelyMeasurable ℱ b' ∧
      (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b' ω s = 0) ∧ Brownian.Ito.energy P T b' ≠ ⊤ ∧
      ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), b' p.1 p.2 = b p.1 p.2 := by
  have hae := LevyStochCalc.BSDEJ.Generator.ae_ae_leftAverageLimit_eq hbm hbz hbq
  have hbm' := _root_.Prove2MeSourceProof.h_98598376fa8eb2edcffbba89 hbm T
  have henergy : LevyStochCalc.Brownian.Ito.energy P T (LevyStochCalc.BSDEJ.Generator.leftAverageLimit b T) = LevyStochCalc.Brownian.Ito.energy P T b := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact lintegral_congr_ae (hω.mono fun s hs => by simp only [hs])
  refine ⟨LevyStochCalc.BSDEJ.Generator.leftAverageLimit b T, hbm', LevyStochCalc.BSDEJ.Generator.progressivelyMeasurable_leftAverageLimit hbp T,
    fun ω s hs => LevyStochCalc.BSDEJ.Generator.leftAverageLimit_of_notMem b T hs, by rw [henergy]; exact hbq, ?_⟩
  have hset : MeasurableSet {p : Ω × ℝ | LevyStochCalc.BSDEJ.Generator.leftAverageLimit b T p.1 p.2 = b p.1 p.2} :=
    measurableSet_eq_fun hbm' hbm
  exact (Measure.ae_prod_iff_ae_ae hset).mpr hae
end LevyStochCalc.BSDEJ.Generator


