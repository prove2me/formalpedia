-- Prove2me | Definitions.Def_SourceProof_149ceb509314dcf41ef9a279
-- name    : SourceProof_149ceb509314dcf41ef9a279
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:57:36.836095+00:00
-- url     : https://prove2.me/theorems/4b2eca43-04dc-4e46-9fbf-5e831353d765
-- title:
--   LevyStochCalc source module: SourceProof_149ceb509314dcf41ef9a279
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.floor_mul_mem_Icc` comes from the `LevyStochCalc.Ito.ItoFormulaGeneralShift` module. The staged Lean declaration includes its source proof and dependency references.
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

theorem _root_.Prove2MeSourceProof.h_149ceb509314dcf41ef9a279 {M x : ℝ} (m : ℕ) (hx : |x| ≤ M) :
    ⌊(2 : ℝ) ^ m * x⌋
      ∈ Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have hceil : (2 : ℝ) ^ m * M ≤ ((⌈(2 : ℝ) ^ m * M⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hfl : ((⌊(2 : ℝ) ^ m * x⌋ : ℤ) : ℝ) ≤ (2 : ℝ) ^ m * x := Int.floor_le _
  have hxu : (2 : ℝ) ^ m * x ≤ (2 : ℝ) ^ m * M := mul_le_mul_of_nonneg_left hu h2.le
  have hxl : -((2 : ℝ) ^ m * M) ≤ (2 : ℝ) ^ m * x := by
    have hml := mul_le_mul_of_nonneg_left hl h2.le
    linarith
  refine Finset.mem_Icc.mpr ⟨Int.le_floor.mpr ?_, ?_⟩
  · push_cast
    linarith
  · have hcast : ((⌊(2 : ℝ) ^ m * x⌋ : ℤ) : ℝ) ≤ (((⌈(2 : ℝ) ^ m * M⌉ + 1 : ℤ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
variable {Ω : Type u} [MeasurableSpace Ω]

end DyadicApproximation

end LevyStochCalc.Brownian.Ito


