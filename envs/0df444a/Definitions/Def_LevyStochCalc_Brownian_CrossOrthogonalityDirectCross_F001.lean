-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001
-- name    : LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:08:47.460154+00:00
-- url     : https://prove2.me/theorems/ddda3a7f-3d71-48b9-8be5-7c6b1e5913cd
-- title:
--   Source declarations: LevyStochCalc.Brownian.CrossOrthogonalityDirectCross
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CrossOrthogonalityDirectCross. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
import Definitions.Def_LevyStochCalc_Brownian_MultidimFiltered_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The direct cross identity for distinct Brownian coordinates

For a `d`-dimensional Brownian motion `W` whose coordinates are all Brownian motions for one
filtration `ℱ`, and distinct coordinates `i ≠ j`, the identity
`E[Z (Wⁱ_b - Wⁱ_a)(Wʲ_b - Wʲ_a)] = 0` holds for a bounded `ℱ_a`-measurable weight `Z`: along a
uniform grid of `[a, b]`, the product of the two increments telescopes into cell-wise terms, the
terms with a past factor are killed by conditioning, and the sum of the cell-wise cross products
has second moment `(b - a)² / m` by the independence of the two coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section DirectCross

/-- A coefficient measurable at the start of an interval is orthogonal to the Brownian increment
over it. -/
lemma integral_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s < u) {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ s] Y) (hYm : Measurable Y) :
    ∫ ω, Y ω * (V.W u ω - V.W s ω) ∂P = 0 := by
  have h := _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 V ℱ hV hs hsu hY hYm 1
  rw [Ito.integral_increment_pow_odd V hs hsu odd_one, mul_zero] at h
  simpa only [pow_one] using h
end DirectCross

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


