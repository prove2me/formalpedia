-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellPairing_F000
-- name    : LevyStochCalc_Driver_CellPairing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:57:33.614381+00:00
-- url     : https://prove2.me/theorems/fa65aa93-9f0b-4257-9808-45bdbee7bacb
-- title:
--   Source declarations: LevyStochCalc.Driver.CellPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F001
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F002
import Definitions.Def_LevyStochCalc_Poisson_CellIntegrand_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing the jump term of the product rule

A weight orthogonal to every compensated integral over the horizon does not see the compensated
half of a window integral against the random measure: pairing it, times a bounded weight
measurable before the window, with the integral of a continuous adapted factor against the
random measure leaves only the integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section JumpTerm

omit [IsProbabilityMeasure P] in
/-- The product of an `L²` function with a bounded one is integrable. -/
theorem integrable_mul_bdd_mul {Z V F : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hF2 : MemLp F 2 P)
    (hVm : Measurable V) {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    Integrable (fun ω => Z ω * V ω * F ω) P := by
  have hZF : Integrable (fun ω => Z ω * F ω) P := integrable_mul_of_memLp_two hZ2 hF2
  have hVnorm : ∀ᵐ ω ∂P, ‖V ω‖ ≤ M :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hVb ω
  exact (hZF.bdd_mul hVm.aestronglyMeasurable hVnorm).congr
    (Filter.Eventually.of_forall fun ω => by ring)
variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ}

end JumpTerm

section BrownianTerm

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end BrownianTerm

section Assembly

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end Assembly

end LevyStochCalc.Driver


