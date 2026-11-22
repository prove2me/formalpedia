-- Prove2me | Definitions.Def_NonvacuityBSDEJJump_F000
-- name    : NonvacuityBSDEJJump_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:50:56.515798+00:00
-- url     : https://prove2.me/theorems/04ac5489-799e-494f-a0e6-340f6b0883af
-- title:
--   Source declarations: NonvacuityBSDEJJump
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJJump. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJZ_F001

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

/-- A deterministic time indicator, constant in the sample point and in the mark, is marked
progressively measurable for every filtration. -/
theorem markedProgressivelyMeasurable_window {E : Type v} [MeasurableSpace E]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {S : Set ℝ} (hS : MeasurableSet S) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun (_ : Ω) (s : ℝ) (_ : E) => Set.indicator S (fun _ => (1 : ℝ)) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hg : Measurable fun r : ℝ =>
      (Set.Iic t).indicator (fun s => Set.indicator S (fun _ => (1 : ℝ)) s) r :=
    (measurable_const.indicator hS).indicator measurableSet_Iic
  exact (hg.comp measurable_snd.fst).stronglyMeasurable
/-- The indicator of the window `(0, 1]`, read as a jump integrand constant in the mark. -/
noncomputable def jumpU (Ω : Type u) : ℝ → Ω → ℝ → ℝ :=
  fun s _ _ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s
omit [MeasurableSpace Ω] in
/-- The value of `jumpU` at a time is the indicator of `(0, 1]` at that time. -/
theorem jumpU_apply (s : ℝ) (ω : Ω) (e : ℝ) :
    jumpU Ω s ω e = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s := rfl
/-- The zero one-dimensional Brownian integrand. -/
def zeroZ (Ω : Type u) : ℝ → Ω → (Fin 1 → ℝ) := fun _ _ _ => (0 : ℝ)
section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- `jumpU` is jointly measurable in the sample point, the time and the mark. -/
theorem jumpU_meas : Measurable fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := by
  have h : Measurable fun s : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s :=
    measurable_const.indicator measurableSet_Ioc
  exact h.comp measurable_snd.fst
/-- `jumpU` is marked progressively measurable for the augmented joint filtration. -/
theorem jumpU_prog :
    Probability.MarkedProgressivelyMeasurable (augJoint D) fun ω s e => jumpU Ω s ω e :=
  markedProgressivelyMeasurable_window (E := ℝ) (augJoint D) (S := Set.Ioc (0 : ℝ) 1)
    measurableSet_Ioc
omit [MeasurableSpace Ω] in
/-- `jumpU` vanishes off the horizon `[0, 1]`. -/
theorem jumpU_vanish (ω : Ω) (s e : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : jumpU Ω s ω e = 0 := by
  have hs' : s ∉ Set.Ioc (0 : ℝ) 1 := fun h => hs ⟨h.1.le, h.2⟩
  simp [jumpU, Set.indicator_of_notMem hs']
end Fields

/-! ### A solution triple with a nonzero jump integrand -/

/-! ### The marked energy of the jump integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


