-- Prove2me | Definitions.Def_SourceProof_a54f17b20359f1a9dacf5570
-- name    : SourceProof_a54f17b20359f1a9dacf5570
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:58:29.628566+00:00
-- url     : https://prove2.me/theorems/3c0972bc-a6d7-4989-b7af-56b607c456d0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsConditionalIncrementModulus.ae_le_of_bound

import Definitions.Def_StochLean_Probability_Martingale_Doob_ConditionalModulus_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Version-safe conditional increment moduli

The compact short-window modulus is specified as a measurable essential supremum,
not as the pointwise supremum of arbitrarily chosen uncountably many conditional
expectations. Existence and almost-sure uniqueness precede any representative choice.
The diagonal is included, so taking positive parts does not change a consistent
supremum. These interfaces do not yet assert small-window convergence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  {T δ η : ℝ≥0} {W V : Ω → ℝ≥0∞}

namespace IsConditionalIncrementModulus
theorem _root_.Prove2MeSourceProof.h_a54f17b20359f1a9dacf5570
    (hW : IsConditionalIncrementModulus F P X T δ W) (U : Ω → ℝ≥0∞)
    (hU : ∀ t u : ℝ≥0, t ≤ u → u ≤ T → u ≤ t + δ →
      (fun ω ↦ ENNReal.ofReal (P[X t - X u | F t] ω)) ≤ᵐ[P] U) : W ≤ᵐ[P] U :=
  hW.ae_le U (fun i ↦ hU i.1.1 i.1.2 i.2.1 i.2.2.1 i.2.2.2)
end IsConditionalIncrementModulus

end ProbabilityTheory


