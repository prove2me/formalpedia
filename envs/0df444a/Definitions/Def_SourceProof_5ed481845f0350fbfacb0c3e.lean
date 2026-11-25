-- Prove2me | Definitions.Def_SourceProof_5ed481845f0350fbfacb0c3e
-- name    : SourceProof_5ed481845f0350fbfacb0c3e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:27:30.405558+00:00
-- url     : https://prove2.me/theorems/6b24bc98-2454-43b7-b859-3f78bf6aa6bd
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_endpoint_difference

import Definitions.Def_SourceProof_7571e2c33b7245dcac603c85
import Definitions.Def_SourceProof_9e21fcad2fff4622240860ee
import Definitions.Def_SourceProof_c928481d34614e91d290315c
import Definitions.Def_SourceProof_df748caa15ccf18186e5d2f4
import Definitions.Def_SourceProof_f72cde5ffb5df7e2856ca7ba

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Square sums of a cadlag finite-variation path

The limit is the Stieltjes increment integral of the actual jump. The next
identification with a jump series is separate; no summability is assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_5ed481845f0350fbfacb0c3e (π : TimePartition T) :
    pathStieltjesIncrementIntegral x hx hr
      (fun u ↦ π.taggedStep π.right x u - π.leftStep x u) 0 T =
      quadraticVariationSum π x := by
  rw [_root_.Prove2MeSourceProof.h_df748caa15ccf18186e5d2f4
    (_root_.Prove2MeSourceProof.h_c928481d34614e91d290315c π π.right x T)
    (_root_.Prove2MeSourceProof.h_f72cde5ffb5df7e2856ca7ba π x T),
    _root_.Prove2MeSourceProof.h_7571e2c33b7245dcac603c85,
    _root_.Prove2MeSourceProof.h_9e21fcad2fff4622240860ee, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [StochLean.TimePartition.increment]
  ring
end StochLean


