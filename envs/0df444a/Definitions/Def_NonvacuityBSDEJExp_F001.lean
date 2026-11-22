-- Prove2me | Definitions.Def_NonvacuityBSDEJExp_F001
-- name    : NonvacuityBSDEJExp_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:04:00.845366+00:00
-- url     : https://prove2.me/theorems/d21e469b-e470-429f-b10f-b416a05ad4e5
-- title:
--   Source declarations: NonvacuityBSDEJExp
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJExp. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJExp_F000
import Definitions.Def_SourceProof_54540b497552ad6030b8042f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The explicit solution of a backward equation with the identity generator

The scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator is `f(s, y, z, u) = y`, the horizon is `T = 1` and the
terminal datum is the Brownian value `W_1`. Since `d(e^{1-t} W_t) = −e^{1-t} W_t dt + e^{1-t} dW_t`,
the value process is `Y_t = e^{1-t} W_t`, the Brownian integrand is the windowed weight
`e^{1-s} 1_{(0, 1]}(s)` and the jump integrand vanishes.

## Main statements

* `exists_solvesBSDEJ_expZ` — the equation is solved by `e^{1-t}` times a continuous modification
  of the Brownian motion, together with the integrand pair `(e^{1-s} 1_{(0, 1]}, 0)`.
* `energy_expZ` — the energy of `e^{1-s} 1_{(0, 1]}` on `[0, 1]` is `(e² − 1)/2`.
* `energy_eq_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand of
  energy `(e² − 1)/2` on `[0, 1]`.
* `exists_solvesBSDEJ_generator_id_energy_ne_zero` — on a probability space carrying such a
  driver the equation has this solution triple and every solution triple has Brownian integrand
  of nonzero energy.

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
open LevyStochCalc.Brownian.Ito (IsVectorItoVersion)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The test function `(t, x) ↦ e^{1-t} x` -/

/-! ### The exponential weight -/

/-! ### The integrands of the equation -/

/-! ### Itô's formula for `e^{1-t} W_t` -/

section Version

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- Itô's formula for `e^{1-t} V_t` at a time of the horizon `[0, 1]`, with `V` a continuous
adapted modification of the first Brownian coordinate. -/
theorem expIto_identity_of_mem {V : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => V t ω)
    (hadapt : ∀ t, Measurable[augJoint D t] (V t))
    (hae : ∀ t : ℝ, 0 ≤ t → V t =ᵐ[P] (D.W.W 0).W t)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Real.exp (1 - t) * V t ω
      = -(∫ s in Set.Ioc (0 : ℝ) t, Real.exp (1 - s) * V s ω)
        + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
            D.isBrownianFiltration_aug (expZ Ω) expZ_meas (expZ_prog (augJoint D))
            (sq_int_global_of_vanishing expZ_vanish expZ_sq) t ω := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · have hzero := _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (D.W.W 0)
      (augJoint D) (D.isBrownianFiltration_aug 0) (fun ω' s => expZ Ω s ω' 0) (expZ_meas 0)
      (expZ_prog (augJoint D) 0) (sq_int_global_of_vanishing expZ_vanish expZ_sq 0)
      (le_refl (0 : ℝ))
    filter_upwards [hae 0 le_rfl, (D.W.W 0).initial_zero, hzero] with ω e1 e2 e3
    rw [← h0, multidim_expZ_eq D 0 ω]
    simp only [Pi.zero_apply] at e3
    rw [e1, e2, e3]
    simp
  · exact _root_.Prove2MeSourceProof.h_54540b497552ad6030b8042f D hcont hadapt hae h0 ht.2
end Version

/-! ### The solution triple -/

/-! ### The energy of the Brownian integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


