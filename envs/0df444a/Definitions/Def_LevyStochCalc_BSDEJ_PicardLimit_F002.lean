-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F002
-- name    : LevyStochCalc_BSDEJ_PicardLimit_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:18:14.407175+00:00
-- url     : https://prove2.me/theorems/1adb9056-c0ec-4f15-9cc9-c63117bc5f8b
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

/-! ### Changing the input triple of a Picard step on a null set -/

/-! ### Triples at zero weighted distance -/

/-! ### The weighted norm against the energies -/

/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}

end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

end FixedPoint

/-! ### Existence of a solution -/

/-- The zero triple is admissible. -/
theorem admissible_zero (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ) :
    Admissible D T (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) where
  Y_meas := measurable_const
  Y_prog := Brownian.Ito.progressivelyMeasurable_zero _
  Y_sq := by simp [Brownian.Ito.energy]
  Z_meas := fun _ => measurable_const
  Z_prog := fun _ => Brownian.Ito.progressivelyMeasurable_zero _
  Z_vanish := fun _ _ _ => rfl
  Z_sq := fun _ => by simp [Brownian.Ito.energy]
  U_meas := measurable_const
  U_prog := markedProgressivelyMeasurable_zero _
  U_vanish := fun _ _ _ _ => rfl
  U_sq := by simp [Poisson.Compensated.markedEnergy]
end LevyStochCalc.BSDEJ.Solves


