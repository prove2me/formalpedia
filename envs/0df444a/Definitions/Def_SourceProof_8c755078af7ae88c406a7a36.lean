-- Prove2me | Definitions.Def_SourceProof_8c755078af7ae88c406a7a36
-- name    : SourceProof_8c755078af7ae88c406a7a36
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:06:34.298177+00:00
-- url     : https://prove2.me/theorems/3e60e52a-7e0c-4c16-9c31-7aca0bd8f6b0
-- title:
--   LevyStochCalc source module: SourceProof_8c755078af7ae88c406a7a36
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.gridStopAux_eq` comes from the `LevyStochCalc.Brownian.ItoLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem _root_.Prove2MeSourceProof.h_8c755078af7ae88c406a7a36 (t : ℝ) (n k : ℕ) (ω : Ω) :
    (∃ j ≤ k, gridStopAux τ t n k ω = ((gridPt t n j : ℝ) : WithTop ℝ))
      ∨ gridStopAux τ t n k ω = ⊤ := by
  induction k with
  | zero =>
    rcases LevyStochCalc.Brownian.Ito.stepStop_eq_or τ (LevyStochCalc.Brownian.Ito.gridPt t n 0) ω with h | h
    · exact Or.inl ⟨0, le_rfl, h⟩
    · exact Or.inr h
  | succ k ih =>
    have hval : LevyStochCalc.Brownian.Ito.gridStopAux τ t n (k + 1) ω
        = min (LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n (k + 1)) ω) (LevyStochCalc.Brownian.Ito.gridStopAux τ t n k ω) := rfl
    rw [hval]
    rcases le_total (LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n (k + 1)) ω) (LevyStochCalc.Brownian.Ito.gridStopAux τ t n k ω) with h | h
    · rw [min_eq_left h]
      rcases LevyStochCalc.Brownian.Ito.stepStop_eq_or τ (LevyStochCalc.Brownian.Ito.gridPt t n (k + 1)) ω with h1 | h1
      · exact Or.inl ⟨k + 1, le_rfl, h1⟩
      · exact Or.inr h1
    · rw [min_eq_right h]
      rcases ih with ⟨j, hj, hje⟩ | hje
      · exact Or.inl ⟨j, hj.trans (Nat.le_succ k), hje⟩
      · exact Or.inr hje
end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Local

end LevyStochCalc.Brownian.Ito


