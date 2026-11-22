-- Prove2me | Definitions.Def_NonvacuityBSDEJRate_F001
-- name    : NonvacuityBSDEJRate_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:31:04.753536+00:00
-- url     : https://prove2.me/theorems/0d6c46ce-3875-454f-be54-47863f277654
-- title:
--   Source declarations: NonvacuityBSDEJRate
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJRate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJRate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for the backward equation with the identity generator

For the scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

of `NonvacuityBSDEJExp`, the Brownian integrand of every solution triple agrees `P ⊗ dt`-almost
everywhere on `Ω × [0, 1]` with the windowed weight `e^{1-s} 1_{(0, 1]}(s)`, hence with the
globally Lipschitz clamped weight `s ↦ e^{1 - max s 0}`. Transporting the deterministic bound
`LevyStochCalc.BSDEJ.PathRegularity.energy_sub_cellTimeAverage_le_of_lipschitz` along that
agreement gives, for every solution triple and every strictly monotone partition of `[0, 1]` of
mesh at most `δ`, the energy bound `(e δ) ^ 2` for the difference between the integrand and its
pathwise cell average.

The average subtracted here is the pathwise cell average `cellTimeAverage_Z`, not the
`ℱ_{t_n}`-conditional projection; the equation is the single equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`.

## Main statements

* `abs_expWeightClamp_sub_le` — the clamped weight `s ↦ e^{1 - max s 0}` is Lipschitz with
  constant `e`.
* `ae_eq_expZ_of_solvesBSDEJ` — the Brownian integrand of a solution triple agrees with `expZ`
  almost everywhere for `P ⊗ dt` on `Ω × [0, 1]`.
* `energy_sub_cellAverage_le_of_solvesBSDEJ` — the cell-average error of the Brownian integrand
  of a solution triple has energy at most `(e δ) ^ 2` on the horizon.
* `exists_solvesBSDEJ_cellAverage_rate` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple obeys that bound.

## References

* Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with
  jumps*, Stochastic Processes Appl. **118(1)**, 2008, pp. 53–75.
* Delong, Ł., *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.BSDEJ.PathRegularity
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The clamped exponential weight -/

/-- On the window `(0, 1]` the windowed weight `expZ` is the clamped weight. -/
theorem expZ_eq_expWeightClamp {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) (ω : Ω) (i : Fin 1) :
    expZ Ω s ω i = expWeightClamp s := by
  rw [expZ_apply, Set.indicator_of_mem hs, expWeightClamp_of_nonneg hs.1.le]
/-! ### The Brownian integrand of a solution -/

/-! ### The pathwise cell average of a solution -/

/-! ### The rate -/

/-! ### The witness -/

/-! ### The uniform partition -/

variable {M : ℕ}

/-! ### The rate along the uniform partitions -/

end LevyStochCalc.Examples.Nonvacuity


