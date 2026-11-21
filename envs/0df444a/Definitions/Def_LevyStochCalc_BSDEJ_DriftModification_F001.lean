-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001
-- name    : LevyStochCalc_BSDEJ_DriftModification_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:50:18.361256+00:00
-- url     : https://prove2.me/theorems/ef031780-ad64-4d18-a37b-38aa1da58baa
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.DriftModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.DriftModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F000
import Definitions.Def_SourceProof_98b1bfd1eba405ec69e0ef6d

open private one_div_succ_pos from Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F000
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

/-- The limit of the moving averages of a process progressively measurable for the
right-continuous filtration is progressively measurable for the filtration itself. -/
theorem progressivelyMeasurable_leftAverageLimit
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ (leftAverageLimit b T) :=
  _root_.Prove2MeSourceProof.h_98b1bfd1eba405ec69e0ef6d
    (_root_.Prove2MeSourceProof.h_f0c53d0eaa784ed729ffd61d fun n =>
      progressivelyMeasurable_leftAverage hbp (one_div_succ_pos n)) T
/-- The limit of the moving averages vanishes off the horizon. -/
theorem leftAverageLimit_of_notMem (b : Ω → ℝ → ℝ) (T : ℝ) {ω : Ω} {s : ℝ}
    (hs : s ∉ Set.Icc (0 : ℝ) T) : leftAverageLimit b T ω s = 0 :=
  Set.indicator_of_notMem hs _
/-- A process of finite energy on the horizon that vanishes off it is integrable at almost every
sample point. -/
private theorem ae_integrable (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0) :
    ∀ᵐ ω ∂P, Integrable (b ω) volume := by
  have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hbm.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  filter_upwards [ae_lt_top hmeas hbq] with ω hω
  have hfm : Measurable (b ω) := hbm.comp (measurable_const.prodMk measurable_id)
  have hsq : HasFiniteIntegral (fun s => b ω s ^ 2) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => ?_)) hω
    rw [← ENNReal.coe_pow, ← nnnorm_pow]
    rfl
  have hIO : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume :=
    ((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr
      ⟨(hfm.pow_const 2).aestronglyMeasurable, hsq⟩).integrable (by norm_num)
  have hrw : b ω = (Set.Icc (0 : ℝ) T).indicator (b ω) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, hbz ω s hs]
  rw [hrw]
  exact (integrable_indicator_iff measurableSet_Icc).mpr hIO
/-- The limit of the moving averages agrees with the process at almost every time on the
horizon, at almost every sample point. -/
theorem ae_ae_leftAverageLimit_eq (hbm : Measurable (Function.uncurry b))
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), leftAverageLimit b T ω s = b ω s := by
  filter_upwards [ae_integrable hbm hbq hbz] with ω hω
  have hae := ae_tendsto_leftAverage_of_locallyIntegrable hω.locallyIntegrable
    (c := fun n : ℕ => 1 / ((n : ℝ) + 1)) one_div_succ_pos
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ae_restrict_of_ae (hae.mono fun s hs => ?_)
  by_cases hsT : s ∈ Set.Icc (0 : ℝ) T
  · rw [leftAverageLimit, Set.indicator_of_mem hsT]
    exact hs.limsup_eq
  · rw [leftAverageLimit_of_notMem b T hsT, hbz ω s hsT]
end LevyStochCalc.BSDEJ.Generator


