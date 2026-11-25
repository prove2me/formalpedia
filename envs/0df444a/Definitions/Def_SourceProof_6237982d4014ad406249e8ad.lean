-- Prove2me | Definitions.Def_SourceProof_6237982d4014ad406249e8ad
-- name    : SourceProof_6237982d4014ad406249e8ad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:35.576442+00:00
-- url     : https://prove2.me/theorems/19062bf5-0df0-59a7-bc41-63ce7fa39474
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_sub

import Definitions.Def_SourceProof_59ed35988bf791fd6e7e31bb
import Definitions.Def_SourceProof_92f98353d1ecfc763009098e
import Definitions.Def_SourceProof_bc53441c2020b643491018cd
import Definitions.Def_SourceProof_c128905347c476a8d319023c
import Definitions.Def_SourceProof_e646c38e672f646e937ef288
import Definitions.Def_SourceProof_f267311a53bb9d8d0cbfc95b

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

theorem _root_.Prove2MeSourceProof.h_6237982d4014ad406249e8ad (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd hH) hK).elementaryIntegral X =
      fun ω ↦ hH.elementaryIntegral X ω - hK.elementaryIntegral X ω := by
  rw [(_root_.Prove2MeSourceProof.h_92f98353d1ecfc763009098e ((_root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd hH) hK)) ((_root_.Prove2MeSourceProof.h_59ed35988bf791fd6e7e31bb hH) (_root_.Prove2MeSourceProof.h_c128905347c476a8d319023c hK)) (sub_eq_add_neg H K) X,
    (_root_.Prove2MeSourceProof.h_e646c38e672f646e937ef288 hH) (_root_.Prove2MeSourceProof.h_c128905347c476a8d319023c hK) X, (_root_.Prove2MeSourceProof.h_f267311a53bb9d8d0cbfc95b hK) X]
  rfl
end IsSimplePredictable
end ProbabilityTheory


