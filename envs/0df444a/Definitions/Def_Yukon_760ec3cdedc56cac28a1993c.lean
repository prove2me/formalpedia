-- Prove2me | Definitions.Def_Yukon_760ec3cdedc56cac28a1993c
-- name    : Yukon_760ec3cdedc56cac28a1993c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T12:40:05.854989+00:00
-- url     : https://prove2.me/theorems/8cf06b08-b82c-4310-96b1-b03fafa97199
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.ThreeChannelJoint6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.ThreeChannelJoint6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/ThreeChannelJoint6807.lean
--
--   yukon-proof-operation:foundation-direct-187d4faa8ab4939f0d6dc1e0fe6ef2a40bee5adbbc51dd62d015d088778d799a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzkzMjdiYWQzMmFkNzQxOGRhNDIxMWY0YWYwMWYzNzk2M2YyNGY0MzkwOGQ0ZTAwNjQ1ODVkYWFhOGE0NzA5YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTE4N2Q0ZmFhOGFiNDkzOWYwZDZkYzFlMGZlNmVmMmE0MGJlZTVhZGJiYzUxZGQ2MmQwMTVkMDg4Nzc4ZDc5OWEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83NjBlYzNjZGVkYzU2Y2FjMjhhMTk5M2MiLCJ2IjoyfQ]

/-
UNCOMPILED. All THREE unit cuts are supplied by the actual generic-channel
construction; none is a theorem premise here. The remaining pointwise moving
inequality is the original actual-source output, consumed at the Stage entry.
-/
import Definitions.Def_Yukon_9bc6354a39244d128eafc24b

import Definitions.Def_Yukon_910f7f29d27cb8bde8dfa124

import Definitions.Def_Yukon_4f4570e485073d9f82646920












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ThreeChannelJoint6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN135 RCN136 RCN156 RCN207 RCN244 RCN264 RCN313
open RCN341 RCN344 RCN046 RCN237
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 CommonLinearChannels6807
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local instance  _root_.ProximityPrize.SubmissionLower.ThreeChannelJoint6807.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.ThreeChannelJoint6807.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.ThreeChannelJoint6807


