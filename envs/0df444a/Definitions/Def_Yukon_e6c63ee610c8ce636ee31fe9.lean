-- Prove2me | Definitions.Def_Yukon_e6c63ee610c8ce636ee31fe9
-- name    : Yukon_e6c63ee610c8ce636ee31fe9
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T09:02:00.58747+00:00
-- url     : https://prove2.me/theorems/658857ef-4317-4355-9315-4fc8c3ecdfae
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourcePersistentSeeds6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-bf9c03e70f904a1bd1ddd2023cf648d432cc8c48a5cb4a0c09049fd61cb1902e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGRhNjc2ZTAzNjBkMDZmODI5Njg5YjFlYzdjZjcyODAzOGM3YTIwZGJmNmYyOWNmNjMwNTU5ODU5NmJiNTQzNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtYmY5YzAzZTcwZjkwNGExYmQxZGRkMjAyM2NmNjQ4ZDQzMmNjOGM0OGE1Y2I0YTBjMDkwNDlmZDYxY2IxOTAyZSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2U2YzYzZWU2MTBjOGNlNjM2ZWUzMWZlOSIsInYiOjJ9]

import Definitions.Def_Yukon_c71a73feb87d242e88d6b4dc















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The old persistent/tangent engine works with the new frame's pole
bound. It does not require a second global budget family to be built. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN174
open RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open MovingSourceProjectionFamily6814 MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceReducedRoutes6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev PersistentComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
      ∀ delay, globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∈C.1}




theorem persistent_checked_budget :
    (80889+1)*flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitYZFlag=497878763753400 := by decide +kernel



end
end ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814


