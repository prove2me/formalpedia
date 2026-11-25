-- Prove2me | Definitions.Def_SourceProof_9d156f29c7de720a7f707cce
-- name    : SourceProof_9d156f29c7de720a7f707cce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:45.498113+00:00
-- url     : https://prove2.me/theorems/64624d2d-dcf6-4c57-9f75-3abcde22a4bf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsConditionalIncrementModulus.ae_ne_top_of_norm_bound

import Definitions.Def_SourceProof_aa6f20a5580f229d1fa4465e

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
theorem _root_.Prove2MeSourceProof.h_9d156f29c7de720a7f707cce [IsFiniteMeasure P]
    (hW : IsConditionalIncrementModulus F P X T δ W) {N : ℝ}
    (hi : ∀ t, t ≤ T → Integrable (X t) P)
    (hb : ∀ t, t ≤ T → ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) :
    ∀ᵐ ω ∂P, W ω ≠ ∞ :=
  ((_root_.Prove2MeSourceProof.h_aa6f20a5580f229d1fa4465e hW) hi hb).mono fun _ hω ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
end IsConditionalIncrementModulus

end ProbabilityTheory


