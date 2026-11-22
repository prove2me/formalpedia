-- Prove2me | Definitions.Def_SourceProof_037e724daadf008d5ad1442c
-- name    : SourceProof_037e724daadf008d5ad1442c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:06:36.240721+00:00
-- url     : https://prove2.me/theorems/88241f7c-05d3-4475-a940-a433d79e7ed9
-- title:
--   LevyStochCalc source module: SourceProof_037e724daadf008d5ad1442c
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_jump` comes from the `NonvacuityBSDEJJump` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CadlagLegs_F000
import Definitions.Def_NonvacuityBSDEJJump_F001

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

end Fields

/-! ### A solution triple with a nonzero jump integrand -/


theorem _root_.Prove2MeSourceProof.h_037e724daadf008d5ad1442c (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y (zeroZ Ω) (jumpU Ω) ∧
        ∀ t, Y t =ᵐ[P] jumpLeg D t := by
  obtain ⟨M, hadapt, hmeas, hae, hcadlag, -, -, hsup⟩ :=
    exists_cadlag_poissonLeg D 1 zero_le_one (LevyStochCalc.Examples.Nonvacuity.jumpU Ω) LevyStochCalc.Examples.Nonvacuity.jumpU_meas (LevyStochCalc.Examples.Nonvacuity.jumpU_prog D)
      LevyStochCalc.Examples.Nonvacuity.jumpU_vanish LevyStochCalc.Examples.Nonvacuity.jumpU_sq
  refine ⟨M, ?_, hae⟩
  refine
    { Z_meas := LevyStochCalc.Examples.Nonvacuity.zeroZ_meas
      Z_prog := LevyStochCalc.Examples.Nonvacuity.zeroZ_prog D
      Z_vanish := LevyStochCalc.Examples.Nonvacuity.zeroZ_vanish
      Z_sq := LevyStochCalc.Examples.Nonvacuity.zeroZ_sq
      U_meas := LevyStochCalc.Examples.Nonvacuity.jumpU_meas
      U_prog := LevyStochCalc.Examples.Nonvacuity.jumpU_prog D
      U_vanish := LevyStochCalc.Examples.Nonvacuity.jumpU_vanish
      U_sq := LevyStochCalc.Examples.Nonvacuity.jumpU_sq
      Y_meas := hmeas
      Y_adapted := hadapt
      Y_cadlag := hcadlag
      Y_sup := hsup
      eqn := ?_ }
  intro t ht
  filter_upwards [LevyStochCalc.Examples.Nonvacuity.brownianLeg_zeroZ_ae_zero D 1, LevyStochCalc.Examples.Nonvacuity.brownianLeg_zeroZ_ae_zero D t,
    hae t] with ω e1 e2 e3
  rw [e1, e2, e3, integral_zero]
  simp only [LevyStochCalc.Examples.Nonvacuity.jumpLeg]
  ring
/-! ### The marked energy of the jump integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


