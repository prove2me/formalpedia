-- Prove2me | Definitions.Def_LevyStochCalc_Probability_MarkedPredictableModification_F001
-- name    : LevyStochCalc_Probability_MarkedPredictableModification_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:34.125658+00:00
-- url     : https://prove2.me/theorems/12d8c015-8cde-4e6c-8dfd-7531b5bf7a25
-- title:
--   Source declarations: LevyStochCalc.Probability.MarkedPredictableModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.MarkedPredictableModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F001
import Definitions.Def_SourceProof_4f66e9c655448e033b3d860d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of marked progressive integrands

A mark-step integrand adapted at the left endpoints of its cells is predictable on the time–mark
space, and the marked predictable processes are closed under pointwise upper limits. The
mark-step integrands are dense in the marked progressive integrands of finite energy, so such an
integrand agrees with a predictable one almost everywhere in time, mark and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ mΩ}

open LevyStochCalc.Poisson.Compensated

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **An admissible marked horizon integrand has a predictable version.** -/
theorem exists_markedPredictable_ae_eq_markedHorizonIntegrand
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (hT : 0 < T)
    (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∃ ψ : Ω → ℝ → E → ℝ, MarkedPredictable ℱ ν ψ ∧
      (fun p : Ω × ℝ × E => G.toFun p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 :=
  _root_.Prove2MeSourceProof.h_4f66e9c655448e033b3d860d N G.measurable_uncurry G.progressive hT G.energy_ne_top
end LevyStochCalc.Probability


