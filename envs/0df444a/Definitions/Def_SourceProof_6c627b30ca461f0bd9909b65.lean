-- Prove2me | Definitions.Def_SourceProof_6c627b30ca461f0bd9909b65
-- name    : SourceProof_6c627b30ca461f0bd9909b65
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:32:30.623897+00:00
-- url     : https://prove2.me/theorems/406a4faa-2a4e-4c96-8a80-d7b19777b76d
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F000

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


theorem _root_.Prove2MeSourceProof.h_6c627b30ca461f0bd9909b65 {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (T : ℝ) (m : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStopTrunc σ T m) := by
  have hG : MeasureTheory.IsStoppingTime ℱ (LevyStochCalc.Brownian.Ito.gridStop σ T m) := LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop σ hσ T m
  intro i
  by_cases hiT : i < T
  · have hset : {ω | LevyStochCalc.Brownian.Ito.gridStopTrunc σ T m ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | LevyStochCalc.Brownian.Ito.gridStop σ T m ω ≤ ((i : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hle
        by_cases h : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop σ T m ω
        · rw [LevyStochCalc.Brownian.Ito.gridStopTrunc_of_le σ T m h, top_le_iff] at hle
          exact absurd hle (by simp)
        · rwa [LevyStochCalc.Brownian.Ito.gridStopTrunc_of_lt σ T m (not_le.mp h)] at hle
      · intro hle
        have h : ¬ ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop σ T m ω := by
          intro hcon
          have h1 : ((T : ℝ) : WithTop ℝ) ≤ ((i : ℝ) : WithTop ℝ) := le_trans hcon hle
          exact absurd (by exact_mod_cast h1 : T ≤ i) (not_le.mpr hiT)
        rwa [LevyStochCalc.Brownian.Ito.gridStopTrunc_of_lt σ T m (not_le.mp h)]
    rw [hset]
    exact hG i
  · rw [not_lt] at hiT
    have hset : {ω | LevyStochCalc.Brownian.Ito.gridStopTrunc σ T m ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | LevyStochCalc.Brownian.Ito.gridStop σ T m ω ≤ ((i : ℝ) : WithTop ℝ)}
          ∩ {ω | LevyStochCalc.Brownian.Ito.gridStop σ T m ω < ((T : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro hle
        by_cases h : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop σ T m ω
        · rw [LevyStochCalc.Brownian.Ito.gridStopTrunc_of_le σ T m h, top_le_iff] at hle
          exact absurd hle (by simp)
        · rw [LevyStochCalc.Brownian.Ito.gridStopTrunc_of_lt σ T m (not_le.mp h)] at hle
          exact ⟨hle, not_le.mp h⟩
      · rintro ⟨hle, hlt⟩
        rwa [LevyStochCalc.Brownian.Ito.gridStopTrunc_of_lt σ T m hlt]
    rw [hset]
    exact (hG i).inter (ℱ.mono hiT _ (hG.measurableSet_lt T))
end StoppingTime

section Window

variable {Ω : Type u}

end Window

section Horizon

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Horizon

section GridShiftTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GridShiftTransfer

end LevyStochCalc.Brownian.Ito


