-- Prove2me | Definitions.Def_SourceProof_2f34208c7b9f4e759c37de78
-- name    : SourceProof_2f34208c7b9f4e759c37de78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:50:20.541223+00:00
-- url     : https://prove2.me/theorems/057bcc37-6290-4396-b5b9-2d23f057ee43
-- title:
--   LevyStochCalc source module: SourceProof_2f34208c7b9f4e759c37de78
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_mul_increment_pow` comes from the `LevyStochCalc.Brownian.ItoFourthMomentIncrements` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)


theorem _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by
  have hΔ : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hindepσ := hℱ.indep ha hab
  have hYcomap : MeasurableSpace.comap Y inferInstance ≤ ℱ a := hY.measurable.comap_le
  have hIF : ProbabilityTheory.IndepFun Y (fun ω => W.W b ω - W.W a ω) P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at hindepσ
    exact hindepσ u v (hYcomap u hu) hv
  have hIF' : ProbabilityTheory.IndepFun Y (fun ω => (W.W b ω - W.W a ω) ^ m) P :=
    hIF.comp measurable_id (measurable_id.pow_const m)
  exact hIF'.integral_mul_eq_mul_integral hYm.aestronglyMeasurable
    (hΔ.pow_const m).aestronglyMeasurable
end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

end SimplePredictable

end LevyStochCalc.Brownian.Ito


