-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F001
-- name    : LevyStochCalc_Ito_ItoFormulaStoppedLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:12:37.682187+00:00
-- url     : https://prove2.me/theorems/5d5c2fd1-5a77-4847-bb9e-5eddd76c5c53
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaStoppedLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaStoppedLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStopped_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

/-- A pointwise limit of strongly measurable vector-valued functions is strongly measurable. -/
theorem stronglyMeasurable_of_tendsto_pi {mΩ : MeasurableSpace Ω} {N : ℕ}
    {F : ℕ → Ω → Fin N → ℝ} {G : Ω → Fin N → ℝ}
    (hF : ∀ i, MeasureTheory.StronglyMeasurable (F i))
    (hlim : ∀ ω, Filter.Tendsto (fun i => F i ω) Filter.atTop (𝓝 (G ω))) :
    MeasureTheory.StronglyMeasurable G :=
  _root_.stronglyMeasurable_of_tendsto Filter.atTop hF (tendsto_pi_nhds.2 hlim)
end ClipLimit

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section StoppedGeneral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end StoppedGeneral

end LevyStochCalc.Brownian.Ito


