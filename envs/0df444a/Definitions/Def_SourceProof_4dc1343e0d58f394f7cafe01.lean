-- Prove2me | Definitions.Def_SourceProof_4dc1343e0d58f394f7cafe01
-- name    : SourceProof_4dc1343e0d58f394f7cafe01
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:03.875003+00:00
-- url     : https://prove2.me/theorems/cafd6671-233e-43f6-a742-a6182b98a173
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.neg

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear operations and indistinguishable changes in UCP

These statements use the canonical UCP owner and outer-measure event bounds.
No additional path measurability or regularity assumptions are necessary.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Z : ι → ℝ≥0 → Ω → ℝ} {Y W : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_4dc1343e0d58f394f7cafe01 (h : TendstoUCP P X l Y) :
    TendstoUCP P (fun i ↦ -X i) l (-Y) := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using
    _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp h T ε hε
end TendstoUCP

end ProbabilityTheory


