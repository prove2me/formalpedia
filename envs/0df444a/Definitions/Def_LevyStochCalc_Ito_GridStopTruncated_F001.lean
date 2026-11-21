-- Prove2me | Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F001
-- name    : LevyStochCalc_Ito_GridStopTruncated_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:36:59.551142+00:00
-- url     : https://prove2.me/theorems/9d4a5292-6826-44d5-8829-0632e3aa46f7
-- title:
--   Source declarations: LevyStochCalc.Ito.GridStopTruncated
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.GridStopTruncated. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F000
import Definitions.Def_SourceProof_6c627b30ca461f0bd9909b65
import Definitions.Def_SourceProof_c9f8d91666f468ff1aabe966

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The upward grid discretisation truncated at the horizon

The stopping time that stops at the first point of a uniform grid strictly beyond a stopping time
attains the horizon, so its values are not all grid points strictly below the horizon. Sending it
to `⊤` where it attains the horizon leaves a stopping time whose values are grid points strictly
below the horizon or `⊤`, and changes neither the horizon clipped at it nor an integrand cut off
at it on the closed window, hence neither the Itô integral at the horizon.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc` — the upward grid discretisation of a stopping time,
  sent to `⊤` where it attains the horizon.
* `LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc` — it is a stopping time.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_mono` — it is monotone in the stopping time.
* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStopTrunc` — the σ-algebra of a stopping
  time is contained in that of its truncated grid discretisation.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_finiteRange` — its values are grid points strictly
  below the horizon, or `⊤`.
* `LevyStochCalc.Brownian.Ito.clipTime_gridStopTrunc` — the horizon clipped at it is the horizon
  clipped at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stopped_gridStopTrunc` — an integrand cut off at it agrees on the
  closed window with the integrand cut off at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_horizon` — the Itô integral
  at a horizon depends on the integrand only on the window up to that horizon.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc` — Itô's formula
  between the grid discretisations of two stopping times, from the identity between their
  truncations.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Truncate

variable {Ω : Type u}

end Truncate

section FiniteRange

variable {Ω : Type u}

end FiniteRange

section StoppingTime

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The σ-algebra of a stopping time is contained in the σ-algebra of its truncated grid
discretisation. -/
theorem measurableSpace_le_gridStopTrunc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (T : ℝ) (m : ℕ) :
    hσ.measurableSpace ≤ (_root_.Prove2MeSourceProof.h_6c627b30ca461f0bd9909b65 hσ T m).measurableSpace :=
  hσ.measurableSpace_mono _ fun ω => le_gridStopTrunc σ T m ω
end StoppingTime

section Window

variable {Ω : Type u}

/-- The horizon clipped at the truncated grid discretisation is the horizon clipped at the grid
discretisation. -/
theorem clipTime_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    clipTime (gridStopTrunc σ T m) T ω = clipTime (gridStop σ T m) T ω := by
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · rw [clipTime_eq_self_of_top (gridStopTrunc_of_le σ T m h), clipTime_of_le h]
  · have he : gridStopTrunc σ T m ω = gridStop σ T m ω :=
      gridStopTrunc_of_lt σ T m (not_le.mp h)
    simp only [clipTime, he]
/-- On the closed window an integrand cut off at the truncated grid discretisation is the
integrand cut off at the grid discretisation. -/
theorem stopped_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (K : Ω → ℝ → ℝ) (ω : Ω)
    {s : ℝ} (hs : s ≤ T) :
    Probability.stopped (gridStopTrunc σ T m) K ω s
      = Probability.stopped (gridStop σ T m) K ω s := by
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStopTrunc σ T m ω := by
      rw [gridStopTrunc_of_le σ T m h]
      exact le_top
    have h2 : ((s : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω :=
      le_trans (by exact_mod_cast hs) h
    simp only [Probability.stopped]
    rw [if_pos h1, if_pos h2]
  · have he : gridStopTrunc σ T m ω = gridStop σ T m ω :=
      gridStopTrunc_of_lt σ T m (not_le.mp h)
    simp only [Probability.stopped, he]
end Window

section Horizon

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Itô integral at a horizon depends on the integrand only on the window up to that
horizon.** -/
theorem stochasticIntegralBrownian_congr_of_le_horizon
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → s ≤ T → H₁ ω s = H₂ ω s) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  have hconst : MeasureTheory.IsStoppingTime ℱ (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) :=
    MeasureTheory.isStoppingTime_const ℱ T
  have hag : ∀ (ω : Ω) (s : ℝ), 0 < s →
      ((s : ℝ) : WithTop ℝ) ≤ (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) ω → H₁ ω s = H₂ ω s := by
    intro ω s hs hle
    have hle' : ((s : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := hle
    exact hagree ω s hs (by exact_mod_cast hle')
  have h := _root_.Prove2MeSourceProof.h_c9f8d91666f468ff1aabe966 (fun _ : Ω => ((T : ℝ) : WithTop ℝ))
    W ℱ hℱ hconst hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hag hT
  filter_upwards [h] with ω hω
  exact hω le_rfl
/-- The Itô integral at the horizon of the increment of an integrand between the truncated grid
discretisations of two stopping times is the one between the grid discretisations. -/
theorem stochasticIntegralBrownian_stopped_sub_gridStopTrunc
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) (σ τ : Ω → WithTop ℝ) (K : Ω → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (m : ℕ)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStopTrunc τ T m) K ω s
        - Probability.stopped (gridStopTrunc σ T m) K ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStopTrunc τ T m) K ω s
        - Probability.stopped (gridStopTrunc σ T m) K ω s)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStopTrunc τ T m) K ω s
        - Probability.stopped (gridStopTrunc σ T m) K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m) K ω s
        - Probability.stopped (gridStop σ T m) K ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStop τ T m) K ω s
        - Probability.stopped (gridStop σ T m) K ω s)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStop τ T m) K ω s
        - Probability.stopped (gridStop σ T m) K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped (gridStopTrunc τ T m) K ω s
          - Probability.stopped (gridStopTrunc σ T m) K ω s) hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped (gridStop τ T m) K ω s
          - Probability.stopped (gridStop σ T m) K ω s) hm₂ hp₂ hq₂ T := by
  refine stochasticIntegralBrownian_congr_of_le_horizon W ℱ hℱ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hT ?_
  intro ω s _ hsT
  rw [stopped_gridStopTrunc τ T m K ω hsT, stopped_gridStopTrunc σ T m K ω hsT]
end Horizon

section GridShiftTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GridShiftTransfer

end LevyStochCalc.Brownian.Ito


