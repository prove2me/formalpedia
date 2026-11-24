-- Prove2me | Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb
-- name    : SourceProof_ff07642989734d14cb2ac8eb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:18:43.019349+00:00
-- url     : https://prove2.me/theorems/e90a205f-8d50-46a6-bb87-7220ed83161d
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.sub

import Definitions.Def_SourceProof_4dc1343e0d58f394f7cafe01
import Definitions.Def_SourceProof_c55d17120c217e6f4e472165

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
theorem _root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb (hX : TendstoUCP P X l Y) (hZ : TendstoUCP P Z l W) :
    TendstoUCP P (fun i ↦ X i - Z i) l (Y - W) := by
  simpa only [sub_eq_add_neg] using (_root_.Prove2MeSourceProof.h_c55d17120c217e6f4e472165 hX) (_root_.Prove2MeSourceProof.h_4dc1343e0d58f394f7cafe01 hZ)
end TendstoUCP

end ProbabilityTheory


