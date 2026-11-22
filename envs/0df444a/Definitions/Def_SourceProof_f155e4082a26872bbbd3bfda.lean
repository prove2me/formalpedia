-- Prove2me | Definitions.Def_SourceProof_f155e4082a26872bbbd3bfda
-- name    : SourceProof_f155e4082a26872bbbd3bfda
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:56:31.127046+00:00
-- url     : https://prove2.me/theorems/ddcada8b-e8d5-4571-8205-917418e84152
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Examples.Nonvacuity.markedEnergy_jumpU
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose jump integrand carries positive energy

The scalar backward equation

  `Y_t = ξ − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1`, the jump integrand
is the window indicator `1_{(0, 1]}`, constant in the mark, and the terminal datum is its
compensated integral over the whole horizon, so the value process is that compensated integral
and the Brownian integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_jump` — the equation is solved by a càdlàg version of the compensated
  integral of `1_{(0, 1]}` together with the integrand pair `(0, 1_{(0, 1]})`.
* `markedEnergy_jumpU` — the marked energy of `1_{(0, 1]}` on `[0, 1]` for the intensity `δ_1`
  is `1`.
* `markedEnergy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has jump
  integrand of marked energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_markedEnergy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has jump integrand of nonzero marked
  energy on the horizon.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))


theorem _root_.Prove2MeSourceProof.h_f155e4082a26872bbbd3bfda :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => jumpU Ω s ω e) = 1 := by
  have hpt : ∀ (ω : Ω) (s : ℝ),
      ∫⁻ e, (‖LevyStochCalc.Examples.Nonvacuity.jumpU Ω s ω e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)
        = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) s := by
    intro ω s
    rw [lintegral_dirac]
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [LevyStochCalc.Examples.Nonvacuity.jumpU, hs]
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      (∫⁻ e, (‖LevyStochCalc.Examples.Nonvacuity.jumpU Ω s ω e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)) ∂volume = 1 := by
    intro ω
    simp only [hpt]
    rw [lintegral_indicator measurableSet_Ioc, lintegral_one,
      Measure.restrict_apply_univ, Measure.restrict_apply' measurableSet_Icc]
    rw [Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self, Real.volume_Ioc]
    simp
  rw [Poisson.Compensated.markedEnergy]
  simp only [hinner]
  simp
end Fields

/-! ### A solution triple with a nonzero jump integrand -/

/-! ### The marked energy of the jump integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


