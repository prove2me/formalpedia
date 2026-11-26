-- Prove2me | Definitions.Def_SourceProof_f9b9945a35d8fec22e63e77b
-- name    : SourceProof_f9b9945a35d8fec22e63e77b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:35:39.863086+00:00
-- url     : https://prove2.me/theorems/93ec9cff-ad6e-58f4-802e-baf31ac38715
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_weightedQuadraticVariationSum

import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_3c620db59a5da172a27c5abb
import Definitions.Def_SourceProof_3f47dd2e31d438d877ce48c9
import Definitions.Def_SourceProof_3f728ff17fd2f56aaee18b4e
import Definitions.Def_SourceProof_9a15eada3555a513322a1de0
import Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
import Definitions.Def_SourceProof_a648f5e42a2456dbcb33c4d9
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Weighted square sums against the sole raw square bracket

The existing mixed-sum owner is specialized on the diagonal. Bracket
invariance identifies its integral with the existing raw QV integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_f9b9945a35d8fec22e63e77b
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCadlagPaths H P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).weightedQuadraticCovariationSumProcess H X X) atTop
      (((_root_.Prove2MeSourceProof.h_a648f5e42a2456dbcb33c4d9 hX) hF).stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha) hF hr) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr)) :=
  (_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 ((_root_.Prove2MeSourceProof.h_3c620db59a5da172a27c5abb hX) hX hF ha hr hπ))
    ((_root_.Prove2MeSourceProof.h_3f47dd2e31d438d877ce48c9 ((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 hX) hX hF))
      ((_root_.Prove2MeSourceProof.h_a648f5e42a2456dbcb33c4d9 hX) hF) hF
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha) hF hr) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr)
      ((_root_.Prove2MeSourceProof.h_3f728ff17fd2f56aaee18b4e hX) hF))
end IsSemimartingale

end ProbabilityTheory


