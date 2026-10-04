-- Prove2me | Definitions.Def_Yukon_de091d30b1349f12d747d334
-- name    : Yukon_de091d30b1349f12d747d334
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:35:05.051627+00:00
-- url     : https://prove2.me/theorems/6872ab0a-4b9b-442d-894b-855ed316559a
-- title:
--   Relative certificate source part 2/3
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B52T3680To3840Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B52T3680To3840Fast.lean
--
--   yukon-proof-operation:certificate-b52-tail-module-Yukon_de091d30b1349f12d747d334
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTc4MTI2MTE3Y2ZhYTNmNDQ0YzEzODNiNDM0NmM0MmU1N2ZkYmQ1NjA3Y2Y3NmQ1ZGVhNmYzZjlhMmJiMjZjMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Mi10YWlsLW1vZHVsZS1ZdWtvbl9kZTA5MWQzMGIxMzQ5ZjEyZDc0N2QzMzQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kZTA5MWQzMGIxMzQ5ZjEyZDc0N2QzMzQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_3610560a362096f5bd3bc086
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_4e6a4328ff3b4945ae675da9











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 641479a808f9c4405d3bda86b9d2a699e3fb8a5d22a965a26786df9004fc102a.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b45 : List (Rectangle × FastWitness) := [(r360,⟨64,48,49⟩),(r361,⟨64,48,49⟩),(r362,⟨64,48,49⟩),(r363,⟨64,49,49⟩),(r364,⟨64,49,49⟩),(r365,⟨64,49,49⟩),(r366,⟨64,49,49⟩),(r367,⟨64,49,49⟩)]
theorem checked45 : fastCheckList band b45=true := by decide +kernel

def b46 : List (Rectangle × FastWitness) := [(r368,⟨64,49,49⟩),(r369,⟨64,49,49⟩),(r370,⟨64,49,49⟩),(r371,⟨64,49,49⟩),(r372,⟨64,49,49⟩),(r373,⟨64,49,49⟩),(r374,⟨64,49,49⟩),(r375,⟨64,49,49⟩)]
theorem checked46 : fastCheckList band b46=true := by decide +kernel

def b47 : List (Rectangle × FastWitness) := [(r376,⟨64,49,49⟩),(r377,⟨64,49,49⟩),(r378,⟨64,49,49⟩),(r379,⟨64,49,49⟩),(r380,⟨64,49,49⟩),(r381,⟨64,49,49⟩),(r382,⟨64,49,49⟩),(r383,⟨64,49,49⟩)]
theorem checked47 : fastCheckList band b47=true := by decide +kernel

def b48 : List (Rectangle × FastWitness) := [(r384,⟨64,49,49⟩),(r385,⟨64,49,49⟩),(r386,⟨64,49,49⟩),(r387,⟨64,49,49⟩),(r388,⟨64,49,49⟩),(r389,⟨64,49,49⟩),(r390,⟨64,49,49⟩),(r391,⟨64,49,49⟩)]
theorem checked48 : fastCheckList band b48=true := by decide +kernel

def b49 : List (Rectangle × FastWitness) := [(r392,⟨64,49,50⟩),(r393,⟨64,51,52⟩),(r394,⟨64,51,52⟩),(r395,⟨64,51,52⟩),(r396,⟨64,51,52⟩),(r397,⟨64,51,52⟩),(r398,⟨64,51,52⟩),(r399,⟨64,51,52⟩)]
theorem checked49 : fastCheckList band b49=true := by decide +kernel

def b50 : List (Rectangle × FastWitness) := [(r400,⟨64,51,52⟩),(r401,⟨64,52,52⟩),(r402,⟨64,52,52⟩),(r403,⟨64,52,52⟩),(r404,⟨64,52,52⟩),(r405,⟨64,52,52⟩),(r406,⟨64,52,52⟩),(r407,⟨64,52,52⟩)]
theorem checked50 : fastCheckList band b50=true := by decide +kernel

def b51 : List (Rectangle × FastWitness) := [(r408,⟨64,52,52⟩),(r409,⟨64,52,52⟩),(r410,⟨64,52,52⟩),(r411,⟨64,52,52⟩),(r412,⟨64,52,52⟩),(r413,⟨64,52,52⟩),(r414,⟨64,52,52⟩),(r415,⟨64,52,52⟩)]
theorem checked51 : fastCheckList band b51=true := by decide +kernel

def b52 : List (Rectangle × FastWitness) := [(r416,⟨64,52,52⟩),(r417,⟨64,52,52⟩),(r418,⟨64,52,52⟩),(r419,⟨64,52,52⟩),(r420,⟨64,52,52⟩),(r421,⟨64,52,53⟩),(r422,⟨64,53,53⟩),(r423,⟨64,53,53⟩)]
theorem checked52 : fastCheckList band b52=true := by decide +kernel

def b53 : List (Rectangle × FastWitness) := [(r424,⟨64,53,53⟩),(r425,⟨64,53,53⟩),(r426,⟨64,53,53⟩),(r427,⟨64,53,53⟩),(r428,⟨64,53,53⟩),(r429,⟨64,53,53⟩),(r430,⟨64,53,53⟩),(r431,⟨64,53,53⟩)]
theorem checked53 : fastCheckList band b53=true := by decide +kernel

def b54 : List (Rectangle × FastWitness) := [(r432,⟨64,53,53⟩),(r433,⟨64,53,53⟩),(r434,⟨64,53,53⟩),(r435,⟨64,53,53⟩),(r436,⟨64,53,53⟩),(r437,⟨64,53,53⟩),(r438,⟨64,54,54⟩),(r439,⟨64,54,54⟩)]
theorem checked54 : fastCheckList band b54=true := by decide +kernel

def b55 : List (Rectangle × FastWitness) := [(r440,⟨64,54,54⟩),(r441,⟨64,54,54⟩),(r442,⟨64,57,57⟩),(r443,⟨64,57,57⟩),(r444,⟨64,57,57⟩),(r445,⟨64,57,57⟩),(r446,⟨64,57,57⟩),(r447,⟨64,57,57⟩)]
theorem checked55 : fastCheckList band b55=true := by decide +kernel

def b56 : List (Rectangle × FastWitness) := [(r448,⟨64,57,57⟩),(r449,⟨64,57,57⟩),(r450,⟨64,57,57⟩),(r451,⟨64,57,57⟩),(r452,⟨64,57,57⟩),(r453,⟨64,57,57⟩),(r454,⟨64,57,57⟩),(r455,⟨64,57,57⟩)]
theorem checked56 : fastCheckList band b56=true := by decide +kernel

def b57 : List (Rectangle × FastWitness) := [(r456,⟨64,57,57⟩),(r457,⟨64,57,57⟩),(r458,⟨64,58,58⟩),(r459,⟨64,58,58⟩),(r460,⟨64,58,58⟩),(r461,⟨64,58,58⟩),(r462,⟨64,58,58⟩),(r463,⟨64,58,58⟩)]
theorem checked57 : fastCheckList band b57=true := by decide +kernel

def b58 : List (Rectangle × FastWitness) := [(r464,⟨64,58,58⟩),(r465,⟨64,58,58⟩),(r466,⟨64,58,58⟩),(r467,⟨64,59,59⟩),(r468,⟨64,59,59⟩),(r469,⟨64,59,59⟩),(r470,⟨64,59,59⟩),(r471,⟨64,59,59⟩)]
theorem checked58 : fastCheckList band b58=true := by decide +kernel

def b59 : List (Rectangle × FastWitness) := [(r472,⟨64,59,59⟩),(r473,⟨64,59,59⟩),(r474,⟨64,59,59⟩),(r475,⟨64,60,60⟩)]
theorem checked59 : fastCheckList band b59=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast


