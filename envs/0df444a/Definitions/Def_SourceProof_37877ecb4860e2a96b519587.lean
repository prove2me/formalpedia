-- Prove2me | Definitions.Def_SourceProof_37877ecb4860e2a96b519587
-- name    : SourceProof_37877ecb4860e2a96b519587
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:01:44.988299+00:00
-- url     : https://prove2.me/theorems/66923870-6767-4498-918b-88b7ac79af8f
-- title:
--   LevyStochCalc source module: SourceProof_37877ecb4860e2a96b519587
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.measurable_dyadicShift` comes from the `LevyStochCalc.Ito.ItoFormulaGeneralShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a general random vector

A random vector approached pointwise by random vectors for which Itô's formula between two
stopping times already holds carries the formula itself: the boundary term converges by
continuity of the function, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of
two increments is at most four times the energy of the difference of the integrands, hence
almost surely along a subsequence common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_stopped_sub_diff_le` — the energy of the difference of
  the increments of two integrands is at most four times the energy of their difference.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy` — a path of finite energy is almost
  surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_sum_mul` — the pointwise inner product of two
  families of paths of finite energy is almost surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift` — Itô's formula for the increment
  of a path between two stopping times, for a function translated by a general random vector.
* `LevyStochCalc.Brownian.Ito.dyadicShift` — the dyadic lattice point of a given resolution below
  a vector, coordinate by coordinate.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx` — a bounded random vector known at a
  stopping time is a pointwise limit of finitely valued random vectors known at that time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end IncrementEnergy

section WindowIntegrability

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end WindowIntegrability

section GeneralShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GeneralShift

section DyadicApproximation

theorem _root_.Prove2MeSourceProof.h_37877ecb4860e2a96b519587 {n m : ℕ} : Measurable (dyadicShift (n := n) m) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hfr : ∀ z : Fin n → ℝ, LevyStochCalc.Brownian.Ito.dyadicShift m z i
      = z i - Int.fract ((2 : ℝ) ^ m * z i) / (2 : ℝ) ^ m := by
    intro z
    have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
    simp only [LevyStochCalc.Brownian.Ito.dyadicShift, Int.fract]
    field_simp
    ring
  simp only [hfr]
  exact (measurable_pi_apply i).sub
    ((measurable_fract.comp ((measurable_pi_apply i).const_mul _)).div_const _)
variable {Ω : Type u} [MeasurableSpace Ω]

end DyadicApproximation

end LevyStochCalc.Brownian.Ito


