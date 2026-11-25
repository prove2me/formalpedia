-- Prove2me | Definitions.Def_SourceProof_e646c38e672f646e937ef288
-- name    : SourceProof_e646c38e672f646e937ef288
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:55:28.508187+00:00
-- url     : https://prove2.me/theorems/036ea38f-3dc2-5d5e-8f9e-f47b25b279ef
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_SourceProof_59ed35988bf791fd6e7e31bb
import Definitions.Def_SourceProof_6d26b1970649598147e36afa
import Definitions.Def_SourceProof_96d13a5b369119fc30e6525e
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

theorem _root_.Prove2MeSourceProof.h_e646c38e672f646e937ef288 (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    ((_root_.Prove2MeSourceProof.h_59ed35988bf791fd6e7e31bb hH) hK).elementaryIntegral X =
      fun ω ↦ hH.elementaryIntegral X ω + hK.elementaryIntegral X ω := by
  have heq : (hH.choose.combine hK.choose (· + ·)
      (measurable_fst.add measurable_snd)).toProcess = H + K := by
    funext t ω
    calc
      _ = hH.choose.toProcess t ω + hK.choose.toProcess t ω :=
        congrFun (congrFun ((_root_.Prove2MeSourceProof.h_6d26b1970649598147e36afa hH.choose) hK.choose
          (fun a b : ℝ ↦ a + b) (measurable_fst.add measurable_snd) (add_zero 0)) t) ω
      _ = (H + K) t ω := congrArg₂ (· + ·)
        (congrFun (congrFun hH.choose_spec t) ω) (congrFun (congrFun hK.choose_spec t) ω)
  rw [_root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 _ _ heq, _root_.Prove2MeSourceProof.h_96d13a5b369119fc30e6525e]
  rfl
end IsSimplePredictable
end ProbabilityTheory


