-- Prove2me | Definitions.Def_SourceProof_c4dfabd4f14ab7a2037da138
-- name    : SourceProof_c4dfabd4f14ab7a2037da138
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:51:43.794593+00:00
-- url     : https://prove2.me/theorems/07d46235-1baa-4061-a5fd-448def45ccfb
-- title:
--   LevyStochCalc source module: SourceProof_c4dfabd4f14ab7a2037da138
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_dyadicRefine` comes from the `LevyStochCalc.Poisson.MarkStepIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_c4dfabd4f14ab7a2037da138 (hG : G.Adapted ℱ) (t : ℝ) :
    (fun ω => (G.dyadicRefine hnm).integral N t ω) =ᵐ[P] fun ω => G.integral N t ω := by
  have hfull : (fun ω => (G.dyadicRefine hnm).integral N T ω)
      =ᵐ[P] fun ω => G.integral N T ω := by
    have h1 : ∀ ω, (G.dyadicRefine hnm).integral N T ω = (G.dyadicRefine hnm).full N ω :=
      fun ω => (G.dyadicRefine hnm).integral_eq_full_of_horizon_le N
        (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon T hT m).le ω
    have h2 : ∀ ω, G.integral N T ω = G.full N ω :=
      fun ω => G.integral_eq_full_of_horizon_le N (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon T hT n).le ω
    simp only [h1, h2]
    exact G.full_dyadicRefine N hnm
  rcases le_or_gt t T with htT | htT
  · have hM₁ := (G.dyadicRefine hnm).martingale_integral N hℱ (hG.dyadicRefine N hnm)
    have hM₂ := G.martingale_integral N hℱ hG
    exact (hM₁.condExp_ae_eq htT).symm.trans
      ((condExp_congr_ae hfull).trans (hM₂.condExp_ae_eq htT))
  · have h1 : ∀ ω, (G.dyadicRefine hnm).integral N t ω = (G.dyadicRefine hnm).full N ω :=
      fun ω => (G.dyadicRefine hnm).integral_eq_full_of_horizon_le N
        ((LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon T hT m).le.trans htT.le) ω
    have h2 : ∀ ω, G.integral N t ω = G.full N ω :=
      fun ω => G.integral_eq_full_of_horizon_le N
        ((LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon T hT n).le.trans htT.le) ω
    simp only [h1, h2]
    exact G.full_dyadicRefine N hnm
end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


