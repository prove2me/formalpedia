-- Prove2me | Definitions.Def_NonvacuityBSDEJZ_F000
-- name    : NonvacuityBSDEJZ_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:39:42.598899+00:00
-- url     : https://prove2.me/theorems/e6a618d3-8b08-4fba-aff5-0d5c894f5748
-- title:
--   Source declarations: NonvacuityBSDEJZ
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJZ. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Solves_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F000
import Definitions.Def_NonvacuityDrivers_F002
import Definitions.Def_SourceProof_0d2a3821a25704fa81bdea82

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose Brownian integrand carries positive energy

The scalar backward equation

  `Y_t = W_1 − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1` and the terminal
datum is the Brownian value `W_1`, so the value process is the Brownian motion itself, the
Brownian integrand is the indicator `1_{(0, 1]}` of the horizon and the jump integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_windowZ` — the equation is solved by a continuous modification of the
  Brownian motion together with the integrand pair `(1_{(0, 1]}, 0)`.
* `energy_windowZ` — the energy of `1_{(0, 1]}` on `[0, 1]` is `1`.
* `energy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand
  of energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_energy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has Brownian integrand of nonzero
  energy.

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

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

/-- The indicator of the window `(0, 1]`, read as a one-dimensional Brownian integrand. -/
noncomputable def windowZ (Ω) [MeasurableSpace Ω] : ℝ → Ω → (Fin 1 → ℝ) :=
  fun s ω _ => Brownian.Ito.indIoc Ω 0 1 ω s
/-- The value of `windowZ` at a time is the indicator of `(0, 1]` at that time. -/
theorem windowZ_apply (s : ℝ) (ω : Ω) (i : Fin 1) :
    windowZ Ω s ω i = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s := rfl
section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- Each coordinate of `windowZ` is jointly measurable. -/
theorem windowZ_meas (i : Fin 1) :
    Measurable (Function.uncurry fun (ω : Ω) s => windowZ Ω s ω i) :=
  Brownian.Ito.measurable_uncurry_indIoc 0 1
/-- Each coordinate of `windowZ` is progressively measurable for the augmented joint
filtration. -/
theorem windowZ_prog (i : Fin 1) :
    Probability.ProgressivelyMeasurable (augJoint D) fun ω s => windowZ Ω s ω i :=
  Brownian.Ito.progressivelyMeasurable_indIoc₀ (augJoint D) zero_lt_one
/-- `windowZ` vanishes off the horizon `[0, 1]`. -/
theorem windowZ_vanish (ω : Ω) (s : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : windowZ Ω s ω = 0 := by
  have hs' : s ∉ Set.Ioc (0 : ℝ) 1 := fun h => hs ⟨h.1.le, h.2⟩
  funext i
  simp [windowZ, Brownian.Ito.indIoc, Set.indicator_of_notMem hs']
/-- Each coordinate of `windowZ` has finite energy on the horizon `[0, 1]`. -/
theorem windowZ_sq (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => windowZ Ω s ω i) ≠ ⊤ :=
  (_root_.Prove2MeSourceProof.h_0d2a3821a25704fa81bdea82 P 0 1 1 zero_lt_one).ne
/-- The zero jump integrand is jointly measurable in the sample point, the time and the mark. -/
theorem zeroU_meas : Measurable fun _p : Ω × ℝ × ℝ => (0 : ℝ) := measurable_const
/-- The zero jump integrand is marked progressively measurable for the augmented joint
filtration. -/
theorem zeroU_prog : Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ) :=
  Poisson.Compensated.markedProgressivelyMeasurable_zero (augJoint D)
/-- The zero jump integrand has finite marked energy on the horizon `[0, 1]`. -/
theorem zeroU_sq : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
    (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) ≠ ⊤ := by
  simp [Poisson.Compensated.markedEnergy]
end Fields

/-! ### A solution triple with the indicator integrand -/

/-! ### The energy of the Brownian integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


