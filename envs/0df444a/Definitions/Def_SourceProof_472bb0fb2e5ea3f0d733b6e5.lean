-- Prove2me | Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
-- name    : SourceProof_472bb0fb2e5ea3f0d733b6e5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:31:23.455015+00:00
-- url     : https://prove2.me/theorems/6e3352ef-6761-4ced-9e46-6f81b7a6d737
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.summable_sq_jumps

import Definitions.Def_SourceProof_7a2cd734cad19a873789e942

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous component of the unique raw quadratic variation

The definition removes the point atoms of a genuine Stieltjes version of the
already constructed raw bracket. It is not a second quadratic-variation
construction. Its exact decomposition uses the squared jumps of the original
semimartingale, with the initial square separate and summability proved.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦ (jumpProcess X s ω) ^ 2) :=
  ((_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hX) hF).mono fun _ h t ↦ (h t).1
end IsSemimartingale

end ProbabilityTheory


