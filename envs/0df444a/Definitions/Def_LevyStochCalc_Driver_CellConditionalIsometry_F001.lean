-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometry_F001
-- name    : LevyStochCalc_Driver_CellConditionalIsometry_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:51:32.312304+00:00
-- url     : https://prove2.me/theorems/db26205d-4ecc-4388-9511-d2fe4af4c0a4
-- title:
--   LevyStochCalc source module: LevyStochCalc.Driver.CellConditionalIsometry
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Driver.CellConditionalIsometry in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellConditionalIsometry_F000
import Definitions.Def_SourceProof_2b50de3fda4320b525536839

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell isometries for a Lévy driver

Over a cell `(a, b]` with `0 ≤ a < b` the increment of a Brownian Itô integral pairs with a
second such increment to the time integral of the product of the integrands over the cell, and
the pairing survives conditioning at the left endpoint: the conditional expectation at `ℱ a` of
the increment against the Brownian increment `W_b − W_a` is the conditional cell average of the
integrand. Restricting the integrand to the cell turns the increment into the integral at the
horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon isometry then
evaluates the pairing.

## Main statements

* `integral_brownian_cell_mul_brownian_cell` — the polarised Itô isometry over a cell.
* `condExp_brownian_cell_mul_increment` — the conditional Itô isometry over a cell, against the
  Brownian increment.
* `condExp_brownian_cell_mul_brownian_increment_eq_zero` — the increment against one coordinate
  is conditionally orthogonal to the increment of another coordinate.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section BrownianCell

variable {H K : Ω → ℝ → ℝ}

/-- **Conditional orthogonality of a cell increment to a distinct Brownian increment.** For
distinct coordinates the increment across `(a, b]` of an Itô integral against one coordinate has
vanishing conditional expectation at `a` against the increment of the other coordinate. -/
theorem condExp_brownian_cell_mul_brownian_increment_eq_zero
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i j : Fin d} (hij : i ≠ j)
    (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * ((D.W.W j).W b ω - (D.W.W j).W a ω) | ℱ a] =ᵐ[P] 0 := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hIm : Measurable (Function.uncurry (indIoc Ω a b)) :=
    Brownian.Ito.measurable_uncurry_indIoc a b
  have hIp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) :=
    Brownian.Ito.progressivelyMeasurable_indIoc_of_nonneg ℱ ha hab
  have hIq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T hT => _root_.Prove2MeSourceProof.h_0d2a3821a25704fa81bdea82 P a b T hT
  have hb' : Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hcoord j)
        (indIoc Ω a b) hIm hIp hIq b
      =ᵐ[P] fun ω => (D.W.W j).W b ω - (D.W.W j).W a ω := by
    have h := _root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 (D.W.W j) ℱ (hcoord j) ha hab
      hIm hIp hIq hb.le
    rw [min_self, min_eq_left hab.le] at h
    exact h
  have ha' : Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hcoord j)
        (indIoc Ω a b) hIm hIp hIq a
      =ᵐ[P] fun ω => (D.W.W j).W a ω - (D.W.W j).W a ω := by
    have h := _root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 (D.W.W j) ℱ (hcoord j) ha hab
      hIm hIp hIq ha
    rw [min_self, min_eq_right hab.le] at h
    exact h
  have hcross := _root_.Prove2MeSourceProof.h_2b50de3fda4320b525536839 D.W hcoord hHm hHp hHs
    hIm hIp hIq hij ha hab
  refine Filter.EventuallyEq.trans (MeasureTheory.condExp_congr_ae ?_) hcross
  filter_upwards [hb', ha'] with ω e1 e2
  rw [e1, e2]
  ring
end BrownianCell

end LevyDriver

end LevyStochCalc.Driver


