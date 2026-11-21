-- Prove2me | Definitions.Def_SourceProof_a4dbeae1c9a6b22bf7020922
-- name    : SourceProof_a4dbeae1c9a6b22bf7020922
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:01:43.446077+00:00
-- url     : https://prove2.me/theorems/6a688a9a-e6a0-4ef2-8b10-89a02eb9d117
-- title:
--   LevyStochCalc source module: SourceProof_a4dbeae1c9a6b22bf7020922
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Coefficients of a vector Itô process clamped at a finite level

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients of
finite energy whose distance in energy to the original coefficients tends to `0`, and the process
they drive stays within that distance of the original one in `L²`, uniformly on a bounded window;
along a suitable subsequence of levels the clamped processes converge to the original one almost
surely.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')


theorem _root_.Prove2MeSourceProof.h_a4dbeae1c9a6b22bf7020922 {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {w : E}
    (h : Filter.Tendsto (fun i => (‖u i - w‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 w) := by
  have hnn : Filter.Tendsto (fun i : ℕ => ‖u i - w‖₊ ^ 2) Filter.atTop (𝓝 0) := by
    rw [← ENNReal.tendsto_coe]
    push_cast
    simpa using h
  have hreal : Filter.Tendsto (fun i : ℕ => ‖u i - w‖ ^ 2) Filter.atTop (𝓝 0) := by
    have hco := NNReal.tendsto_coe.mpr hnn
    push_cast at hco
    simpa using hco
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hreal
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun i => ?_
  exact Real.sqrt_sq (norm_nonneg _)
end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


