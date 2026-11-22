-- Prove2me | Definitions.Def_NonvacuityBSDEJJump_F001
-- name    : NonvacuityBSDEJJump_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:01:07.553416+00:00
-- url     : https://prove2.me/theorems/11384849-75ac-42cc-9a3f-bf3d557fdc9e
-- title:
--   Source declarations: NonvacuityBSDEJJump
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJJump. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_NonvacuityBSDEJJump_F000
import Definitions.Def_SourceProof_2631a3786acbcf68272d1d52
import Definitions.Def_SourceProof_f155e4082a26872bbbd3bfda

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

/-- `jumpU` has finite marked energy on the horizon `[0, 1]`. -/
theorem jumpU_sq : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
    (fun ω s e => jumpU Ω s ω e) ≠ ⊤ := by
  rw [_root_.Prove2MeSourceProof.h_f155e4082a26872bbbd3bfda]
  exact ENNReal.one_ne_top
/-- Each coordinate of `zeroZ` is jointly measurable. -/
theorem zeroZ_meas (i : Fin 1) :
    Measurable (Function.uncurry fun (ω : Ω) s => zeroZ Ω s ω i) := measurable_const
/-- Each coordinate of `zeroZ` is progressively measurable for the augmented joint
filtration. -/
theorem zeroZ_prog (i : Fin 1) :
    Probability.ProgressivelyMeasurable (augJoint D) fun (ω : Ω) s => zeroZ Ω s ω i :=
  Probability.progressivelyMeasurable_zero (augJoint D)
omit [MeasurableSpace Ω] in
/-- `zeroZ` vanishes off the horizon `[0, 1]`. -/
theorem zeroZ_vanish (ω : Ω) (s : ℝ) (_hs : s ∉ Set.Icc (0 : ℝ) 1) : zeroZ Ω s ω = 0 := rfl
/-- Each coordinate of `zeroZ` has finite energy on the horizon `[0, 1]`. -/
theorem zeroZ_sq (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun (ω : Ω) s => zeroZ Ω s ω i) ≠ ⊤ := by
  simp [Brownian.Ito.energy, zeroZ]
/-- The compensated Itô–Lévy integral of `jumpU` for the augmented joint filtration of `D`. -/
noncomputable def jumpLeg : ℝ → Ω → ℝ :=
  Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
    (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
    (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq)
/-- The Brownian leg of `zeroZ` vanishes almost surely at every time. -/
theorem brownianLeg_zeroZ_ae_zero (t : ℝ) :
    ∀ᵐ ω ∂P, Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
      D.isBrownianFiltration_aug (zeroZ Ω) zeroZ_meas (zeroZ_prog D)
      (sq_int_global_of_vanishing zeroZ_vanish zeroZ_sq) t ω = 0 := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52 (D.W.W 0) (augJoint D)
    (D.isBrownianFiltration_aug 0) (zeroZ_meas 0) (zeroZ_prog D 0)
    (sq_int_global_of_vanishing zeroZ_vanish zeroZ_sq 0) t] with ω hω
  show Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
      D.isBrownianFiltration_aug (zeroZ Ω) zeroZ_meas (zeroZ_prog D)
      (sq_int_global_of_vanishing zeroZ_vanish zeroZ_sq) t ω = 0
  rw [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, Fin.sum_univ_one]
  exact hω
/-- The compensated integral of `jumpU` at the horizon is square integrable. -/
theorem memLp_jumpLeg_one : MemLp (jumpLeg D 1) 2 P :=
  Poisson.Compensated.stochasticIntegral_memLp D.N (augJoint D) D.isPoissonFiltration_aug
    (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
    (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq) 1
/-- The compensated integral of `jumpU` at the horizon is measurable for the augmented joint
filtration at the horizon. -/
theorem aestronglyMeasurable_jumpLeg_one :
    AEStronglyMeasurable[augJoint D 1] (jumpLeg D 1) P :=
  ((Poisson.Compensated.process_stronglyAdapted D.N (augJoint D) D.isPoissonFiltration_aug
      (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
      (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq) 1).aestronglyMeasurable).congr
    (Poisson.Compensated.stochasticIntegral_ae_eq_process D.N (augJoint D)
      D.isPoissonFiltration_aug (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
      (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq) 1).symm
end Fields

/-! ### A solution triple with a nonzero jump integrand -/

/-! ### The marked energy of the jump integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


