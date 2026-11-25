-- Prove2me | Definitions.Def_SourceProof_bc53441c2020b643491018cd
-- name    : SourceProof_bc53441c2020b643491018cd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:19:27.890073+00:00
-- url     : https://prove2.me/theorems/d61a72df-b378-5669-8b94-c0ca0351e2a7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.sub

import Definitions.Def_SourceProof_59ed35988bf791fd6e7e31bb
import Definitions.Def_SourceProof_c128905347c476a8d319023c

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

theorem _root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F) :
    IsSimplePredictable (H - K) F := by
  simpa only [sub_eq_add_neg] using (_root_.Prove2MeSourceProof.h_59ed35988bf791fd6e7e31bb hH) (_root_.Prove2MeSourceProof.h_c128905347c476a8d319023c hK)
end IsSimplePredictable
end ProbabilityTheory


