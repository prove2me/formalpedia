-- Prove2me | Definitions.Def_SourceProof_28ab96584fdceef9753ea692
-- name    : SourceProof_28ab96584fdceef9753ea692
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:21:06.145029+00:00
-- url     : https://prove2.me/theorems/76290a01-10f8-4ebe-8f07-f21f81e89801
-- title:
--   LevyStochCalc source module: SourceProof_28ab96584fdceef9753ea692
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.ae_eq_expZ_of_solvesBSDEJ` comes from the `NonvacuityBSDEJRate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PathRegularity_F000
import Definitions.Def_NonvacuityBSDEJExp_F000
import Definitions.Def_SourceProof_cdebc989955e2f6003b4385b

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

/-! ### The Brownian integrand of a solution -/


theorem _root_.Prove2MeSourceProof.h_28ab96584fdceef9753ea692 (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
      Z' p.2 p.1 0 = expZ Ω p.2 p.1 0 := by
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_cdebc989955e2f6003b4385b D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
    rw [LevyStochCalc.Examples.Nonvacuity.lintegral_generator_id_zero]
    exact ENNReal.zero_lt_top
  obtain ⟨-, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ y _ _ => y) (L := 1) zero_le_one
    LevyStochCalc.Examples.Nonvacuity.measurable_generator_id LevyStochCalc.Examples.Nonvacuity.lipschitz_generator_id one_pos hf0 (LevyStochCalc.Examples.Nonvacuity.memLp_brownian_one D.W)
    (LevyStochCalc.Examples.Nonvacuity.aestronglyMeasurable_brownian_one_augJoint D)
  have hzero := (huniq Y' Y Z' (LevyStochCalc.Examples.Nonvacuity.expZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.1 0
  have hmZ : Measurable (Function.uncurry fun ω s => Z' s ω 0) := h.Z_meas 0
  have hmE : Measurable (Function.uncurry fun (ω : Ω) s => LevyStochCalc.Examples.Nonvacuity.expZ Ω s ω 0) := LevyStochCalc.Examples.Nonvacuity.expZ_meas 0
  have hmd : Measurable (Function.uncurry fun ω s => Z' s ω 0 - LevyStochCalc.Examples.Nonvacuity.expZ Ω s ω 0) := hmZ.sub hmE
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ => Z' p.2 p.1 0 - LevyStochCalc.Examples.Nonvacuity.expZ Ω p.2 p.1 0) 2
      (Brownian.Ito.energyMeasure P 1) = 0 := (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hmeas : Brownian.Ito.energyMeasure P 1
      = P.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := rfl
  rw [hmeas] at hae
  filter_upwards [hae] with p hp
  have hp' : Z' p.2 p.1 0 - LevyStochCalc.Examples.Nonvacuity.expZ Ω p.2 p.1 0 = 0 := hp
  linarith
/-! ### The pathwise cell average of a solution -/

/-! ### The rate -/

/-! ### The witness -/

/-! ### The uniform partition -/

variable {M : ℕ}

/-! ### The rate along the uniform partitions -/

end LevyStochCalc.Examples.Nonvacuity


