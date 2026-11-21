-- Prove2me | Definitions.Def_SourceProof_ba444e4a7f686c4937645db3
-- name    : SourceProof_ba444e4a7f686c4937645db3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:08:53.065655+00:00
-- url     : https://prove2.me/theorems/1daa9224-b89b-4536-98ec-12f66c50f2d6
-- title:
--   LevyStochCalc source module: SourceProof_ba444e4a7f686c4937645db3
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stop_le` comes from the `LevyStochCalc.Ito.PicardIntegrandBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 {n : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T' * (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by
  have hXi : ∀ i : Fin n, Measurable fun p : Ω × ℝ => Y.stop.X p.2 p.1 i := fun i =>
    (measurable_pi_apply i).comp
      (Y.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst))
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun i _ => ((hXi i).nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T'))
    (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
  calc ∫⁻ s in Set.Icc (0 : ℝ) T',
        (∫⁻ ω, ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T',
          (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) ∂volume :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc
          (fun s hs => Y.lintegral_sq_stop_le hT hs.1)
    _ = (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) * volume (Set.Icc (0 : ℝ) T') :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal T' * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by
        rw [Real.volume_Icc, sub_zero, mul_comm]
end LevyStochCalc.Ito.Picard


