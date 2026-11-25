-- Prove2me | Definitions.Def_SourceProof_de08a420ec63708a2d73d894
-- name    : SourceProof_de08a420ec63708a2d73d894
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:49.95605+00:00
-- url     : https://prove2.me/theorems/8f2c60b3-709a-425c-9bae-b825f937e0b7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_smul

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
import Definitions.Def_SourceProof_2e6ca13dfe2fe5276b1d3986
import Definitions.Def_SourceProof_308ca0aff4af17c75a3e2378
import Definitions.Def_SourceProof_3d83037636fda5e157d51fda
import Definitions.Def_SourceProof_ec04cdbdbe92b05b4697a078

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

theorem _root_.Prove2MeSourceProof.h_de08a420ec63708a2d73d894 (hH : IsSimplePredictable H F) (c : ℝ)
    (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_2e6ca13dfe2fe5276b1d3986 hH) c).elementaryIntegral X = fun ω ↦ c * hH.elementaryIntegral X ω := by
  have heq : (hH.choose.scale c).toProcess = c • H := by
    rw [_root_.Prove2MeSourceProof.h_3d83037636fda5e157d51fda, hH.choose_spec]
    rfl
  rw [_root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 _ _ heq, _root_.Prove2MeSourceProof.h_308ca0aff4af17c75a3e2378]
  rfl
end IsSimplePredictable
end ProbabilityTheory


