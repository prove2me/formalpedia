-- Prove2me | Definitions.Def_Yukon_1c9853f4364428ab76f81792
-- name    : Yukon_1c9853f4364428ab76f81792
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T13:55:58.485978+00:00
-- url     : https://prove2.me/theorems/55ed269a-c159-420f-8ad0-3d9477d10e9a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailDualRetained6807.lean
--
--   yukon-proof-operation:foundation-direct-797c6f7ac89f2928f500e06933ae15cf737871c580d15b256445e81acedf437a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZTZjZTkxNDgyNjRkOGU1MGMxZTM1M2U3YmYxODI0NmI5MTE2YzM3NDQ2ZThiNGZiZTg3NDViYmEzMjUwYWMyYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTc5N2M2ZjdhYzg5ZjI5MjhmNTAwZTA2OTMzYWUxNWNmNzM3ODcxYzU4MGQxNWIyNTY0NDVlODFhY2VkZjQzN2EiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8xYzk4NTNmNDM2NDQyOGFiNzZmODE3OTIiLCJ2IjoyfQ]

/-
UNCOMPILED. Actual retained proper-first-tail Stage adapter. The joint budget is
built inside the body from actual-source pointwise budgets and three actual
common linear channels. Neither hcut nor hjoint is a theorem premise.
This is not an unconditional ProtocolClaim or a full mixed-branch regular bound.
-/
import Definitions.Def_Yukon_52f7c2cb3790c155905697c9

import Definitions.Def_Yukon_760ec3cdedc56cac28a1993c

import Definitions.Def_Yukon_1cfb6b19fd8d8d5aca848f54

import Definitions.Def_Yukon_95f4f1bf21e75689043f9a32

import Definitions.Def_Yukon_9e01353f705b1903d07af3b0











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807


