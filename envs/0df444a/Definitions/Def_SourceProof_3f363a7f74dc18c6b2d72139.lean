-- Prove2me | Definitions.Def_SourceProof_3f363a7f74dc18c6b2d72139
-- name    : SourceProof_3f363a7f74dc18c6b2d72139
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:58:14.440062+00:00
-- url     : https://prove2.me/theorems/12a2a858-837a-445c-b24e-0d53c2d49dbb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.map₂

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_SourceProof_6d26b1970649598147e36afa

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_3f363a7f74dc18c6b2d72139 (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F)
    (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (h0 : φ 0 0 = 0) :
    IsSimplePredictable (fun t ω ↦ φ (H t ω) (K t ω)) F := by
  refine ⟨hH.choose.combine hK.choose φ hφ, ?_⟩
  rw [_root_.Prove2MeSourceProof.h_6d26b1970649598147e36afa _ _ φ hφ h0, hH.choose_spec, hK.choose_spec]
end IsSimplePredictable
end ProbabilityTheory


