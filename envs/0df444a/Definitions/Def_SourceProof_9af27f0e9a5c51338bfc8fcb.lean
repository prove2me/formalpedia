-- Prove2me | Definitions.Def_SourceProof_9af27f0e9a5c51338bfc8fcb
-- name    : SourceProof_9af27f0e9a5c51338bfc8fcb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:48:34.094127+00:00
-- url     : https://prove2.me/theorems/148db540-a519-4b4f-b4f2-15e6a54f7843
-- title:
--   LevyStochCalc source module: SourceProof_9af27f0e9a5c51338bfc8fcb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral_mean_zero` comes from the `LevyStochCalc.Brownian.ItoRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F000
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97

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


theorem _root_.Prove2MeSourceProof.h_9af27f0e9a5c51338bfc8fcb (hT : 0 ≤ T) (G : HorizonIntegrand P ℱ T) :
    ∫ ω, G.integral W hℱ ω ∂P = 0 := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral W ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global
  haveI : SigmaFinite (P.trim (F.le 0)) := (isFiniteMeasure_trim (F.le 0)).toSigmaFinite
  have hcond := hF.2 0 T hT
  have hz : LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global 0 =ᵐ[P] 0 :=
    _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ G.toFun G.measurable_uncurry
      G.progressive G.sq_int_global le_rfl
  calc ∫ ω, G.integral W hℱ ω ∂P
      = ∫ ω, condExp (F 0) P (fun x => LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ G.toFun
          G.measurable_uncurry G.progressive G.sq_int_global T x) ω ∂P :=
        (integral_condExp (F.le 0)).symm
    _ = ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ G.toFun G.measurable_uncurry G.progressive
          G.sq_int_global 0 ω ∂P := integral_congr_ae hcond
    _ = 0 := by rw [integral_congr_ae hz]; simp
end Integral

end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Representation

end LevyStochCalc.Brownian.Ito


