-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
-- name    : LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:11:33.038913+00:00
-- url     : https://prove2.me/theorems/bfa9e1c8-22f9-46e8-99df-593c676025eb
-- title:
--   Source declarations: LevyStochCalc.Brownian.CrossOrthogonalityLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CrossOrthogonalityLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

omit [IsProbabilityMeasure P] in
/-- The `L²` inner product of two `Lp` representatives is the integral of their product. -/
lemma inner_toLp_eq_integral_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (inner ℝ (hf.toLp f) (hg.toLp g) : ℝ) = ∫ ω, f ω * g ω ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [RCLike.inner_apply, h1, h2]
  simp [mul_comm]
end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


