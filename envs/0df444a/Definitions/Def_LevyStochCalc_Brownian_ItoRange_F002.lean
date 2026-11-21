-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002
-- name    : LevyStochCalc_Brownian_ItoRange_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:48:49.989439+00:00
-- url     : https://prove2.me/theorems/23fb0098-3c32-4211-a37e-dee684d052ca
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the Itô integral on a horizon

An integrand supported in `[0, T]`, jointly and progressively measurable and of finite energy,
is admissible for the Itô integral up to `T`. Such integrands are closed under sums and scalar
multiples, and the integral is additive and homogeneous on them, so their integrals form a
submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence of integrands to
an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {T : ℝ}

end Energy

namespace HorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Integral

end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

/-- The Itô integral over the horizon is measurable before `T`. -/
theorem HorizonIntegrand.aestronglyMeasurable (G : HorizonIntegrand P ℱ T) :
    AEStronglyMeasurable[ℱ T] (G.integral W hℱ) P :=
  stochasticIntegralBrownian_aesm W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T |>.congr
    (stochasticIntegralBrownian_ae_eq W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global T).symm
end Representation

end LevyStochCalc.Brownian.Ito


