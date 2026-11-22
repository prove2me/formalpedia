-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F001
-- name    : LevyStochCalc_Ito_ItoFormulaGeneralShift_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:57:57.246018+00:00
-- url     : https://prove2.me/theorems/8dfa104c-b1a3-44fe-aad2-6cb231d35657
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaGeneralShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaGeneralShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftIntegral_F000

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

/-- The vector of dyadic lattice points of resolution `2 ^ m` below the coordinates of a vector. -/
noncomputable def dyadicShift {n : ℕ} (m : ℕ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (⌊(2 : ℝ) ^ m * z i⌋ : ℝ) / (2 : ℝ) ^ m
theorem dyadicShift_sub_eq {n : ℕ} (m : ℕ) (z : Fin n → ℝ) (i : Fin n) :
    dyadicShift m z i - z i
      = (((⌊(2 : ℝ) ^ m * z i⌋ : ℤ) : ℝ) - (2 : ℝ) ^ m * z i) / (2 : ℝ) ^ m := by
  have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  simp only [dyadicShift]
  field_simp
variable {Ω : Type u} [MeasurableSpace Ω]

end DyadicApproximation

end LevyStochCalc.Brownian.Ito


