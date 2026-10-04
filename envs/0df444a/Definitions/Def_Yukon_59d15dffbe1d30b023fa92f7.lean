-- Prove2me | Definitions.Def_Yukon_59d15dffbe1d30b023fa92f7
-- name    : Yukon_59d15dffbe1d30b023fa92f7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:33:54.205175+00:00
-- url     : https://prove2.me/theorems/ac143ba7-3365-47de-9d21-7935c7af2bfd
-- title:
--   Relative certificate source part 3/6
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
--
--   yukon-proof-operation:certificate-b56-865d7eaca44cfa117ed485c621cf08e6186df7837609c4a893ee14a7fc903fb2
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGY1MzBjYmQ3ZWM2NjE1MmUzYjRkZDQ1ZGM0NzEyZWJjNjUxYWI1ODZhOGRiZWI4ZDNiYzUxMTJhMWY2MjYyMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni04NjVkN2VhY2E0NGNmYTExN2VkNDg1YzYyMWNmMDhlNjE4NmRmNzgzNzYwOWM0YTg5M2VlMTRhN2ZjOTAzZmIyIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNTlkMTVkZmZiZTFkMzBiMDIzZmE5MmY3IiwidiI6Mn0]

import Definitions.Def_Yukon_45e9531aff2eaeac0335aa05
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_dd35002c4104ec31e41819fa











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 07832c8515ee45a9cd576a8e6dc88890fd3e7c99ee877e80bf6d1362ebaf25e9.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b35 : List (Rectangle × FastWitness) := [(r280,⟨68,42,42⟩),(r281,⟨68,42,42⟩),(r282,⟨68,42,42⟩),(r283,⟨68,42,42⟩),(r284,⟨68,42,42⟩),(r285,⟨68,42,42⟩),(r286,⟨68,42,42⟩),(r287,⟨68,42,42⟩)]
theorem checked35 : fastCheckList band b35=true := by decide +kernel

def b36 : List (Rectangle × FastWitness) := [(r288,⟨68,42,42⟩),(r289,⟨68,42,42⟩),(r290,⟨68,42,42⟩),(r291,⟨68,42,42⟩),(r292,⟨68,42,42⟩),(r293,⟨68,42,42⟩),(r294,⟨68,42,42⟩),(r295,⟨68,42,42⟩)]
theorem checked36 : fastCheckList band b36=true := by decide +kernel

def b37 : List (Rectangle × FastWitness) := [(r296,⟨68,42,42⟩),(r297,⟨68,42,42⟩),(r298,⟨68,42,42⟩),(r299,⟨68,42,42⟩),(r300,⟨68,42,42⟩),(r301,⟨68,42,42⟩),(r302,⟨68,42,42⟩),(r303,⟨68,42,42⟩)]
theorem checked37 : fastCheckList band b37=true := by decide +kernel

def b38 : List (Rectangle × FastWitness) := [(r304,⟨68,42,42⟩),(r305,⟨68,42,42⟩),(r306,⟨68,42,42⟩),(r307,⟨68,42,42⟩),(r308,⟨68,42,42⟩),(r309,⟨68,42,42⟩),(r310,⟨68,42,42⟩),(r311,⟨68,42,42⟩)]
theorem checked38 : fastCheckList band b38=true := by decide +kernel

def b39 : List (Rectangle × FastWitness) := [(r312,⟨68,42,43⟩),(r313,⟨68,42,43⟩),(r314,⟨68,42,42⟩),(r315,⟨68,42,42⟩),(r316,⟨68,42,42⟩),(r317,⟨68,42,42⟩),(r318,⟨68,42,42⟩),(r319,⟨68,42,42⟩)]
theorem checked39 : fastCheckList band b39=true := by decide +kernel

def b40 : List (Rectangle × FastWitness) := [(r320,⟨68,42,42⟩),(r321,⟨68,42,42⟩),(r322,⟨68,42,42⟩),(r323,⟨68,42,42⟩),(r324,⟨68,42,42⟩),(r325,⟨68,42,42⟩),(r326,⟨68,42,42⟩),(r327,⟨68,42,42⟩)]
theorem checked40 : fastCheckList band b40=true := by decide +kernel

def b41 : List (Rectangle × FastWitness) := [(r328,⟨68,42,42⟩),(r329,⟨68,42,42⟩),(r330,⟨68,42,42⟩),(r331,⟨68,42,42⟩),(r332,⟨68,42,42⟩),(r333,⟨68,42,42⟩),(r334,⟨68,42,42⟩),(r335,⟨68,42,42⟩)]
theorem checked41 : fastCheckList band b41=true := by decide +kernel

def b42 : List (Rectangle × FastWitness) := [(r336,⟨68,42,42⟩),(r337,⟨68,42,42⟩),(r338,⟨68,42,42⟩),(r339,⟨68,42,42⟩),(r340,⟨68,42,42⟩),(r341,⟨68,42,42⟩),(r342,⟨68,42,42⟩),(r343,⟨68,42,42⟩)]
theorem checked42 : fastCheckList band b42=true := by decide +kernel

def b43 : List (Rectangle × FastWitness) := [(r344,⟨68,42,42⟩),(r345,⟨68,42,42⟩),(r346,⟨68,42,42⟩),(r347,⟨68,42,42⟩),(r348,⟨68,42,42⟩),(r349,⟨68,42,42⟩),(r350,⟨68,42,42⟩),(r351,⟨68,42,42⟩)]
theorem checked43 : fastCheckList band b43=true := by decide +kernel

def b44 : List (Rectangle × FastWitness) := [(r352,⟨68,42,42⟩),(r353,⟨68,42,42⟩),(r354,⟨68,42,42⟩),(r355,⟨68,42,42⟩),(r356,⟨68,42,42⟩),(r357,⟨68,42,42⟩),(r358,⟨68,42,42⟩),(r359,⟨68,42,42⟩)]
theorem checked44 : fastCheckList band b44=true := by decide +kernel

def b45 : List (Rectangle × FastWitness) := [(r360,⟨68,42,42⟩),(r361,⟨68,42,42⟩),(r362,⟨68,42,42⟩),(r363,⟨68,42,42⟩),(r364,⟨68,42,42⟩),(r365,⟨68,42,42⟩),(r366,⟨68,42,42⟩),(r367,⟨68,42,42⟩)]
theorem checked45 : fastCheckList band b45=true := by decide +kernel

def b46 : List (Rectangle × FastWitness) := [(r368,⟨68,42,42⟩),(r369,⟨68,42,42⟩),(r370,⟨68,42,42⟩),(r371,⟨68,42,42⟩),(r372,⟨68,42,42⟩),(r373,⟨68,42,42⟩),(r374,⟨68,42,42⟩),(r375,⟨68,42,42⟩)]
theorem checked46 : fastCheckList band b46=true := by decide +kernel

def b47 : List (Rectangle × FastWitness) := [(r376,⟨68,42,42⟩),(r377,⟨68,42,42⟩),(r378,⟨68,42,42⟩),(r379,⟨68,42,42⟩),(r380,⟨68,42,42⟩),(r381,⟨68,42,42⟩),(r382,⟨68,42,42⟩),(r383,⟨68,42,42⟩)]
theorem checked47 : fastCheckList band b47=true := by decide +kernel

def b48 : List (Rectangle × FastWitness) := [(r384,⟨68,42,42⟩),(r385,⟨68,42,42⟩),(r386,⟨68,42,42⟩),(r387,⟨68,42,42⟩),(r388,⟨68,42,42⟩),(r389,⟨68,42,43⟩),(r390,⟨68,42,43⟩),(r391,⟨68,42,43⟩)]
theorem checked48 : fastCheckList band b48=true := by decide +kernel

def b49 : List (Rectangle × FastWitness) := [(r392,⟨68,42,43⟩),(r393,⟨68,42,43⟩),(r394,⟨68,42,43⟩),(r395,⟨68,42,43⟩),(r396,⟨68,42,43⟩),(r397,⟨68,42,43⟩),(r398,⟨68,42,43⟩),(r399,⟨68,42,43⟩)]
theorem checked49 : fastCheckList band b49=true := by decide +kernel

def b50 : List (Rectangle × FastWitness) := [(r400,⟨68,42,43⟩),(r401,⟨68,42,43⟩),(r402,⟨68,42,43⟩),(r403,⟨68,42,43⟩),(r404,⟨68,42,43⟩),(r405,⟨68,42,43⟩),(r406,⟨68,42,43⟩),(r407,⟨68,42,43⟩)]
theorem checked50 : fastCheckList band b50=true := by decide +kernel

def b51 : List (Rectangle × FastWitness) := [(r408,⟨68,42,43⟩),(r409,⟨68,42,43⟩),(r410,⟨68,42,43⟩),(r411,⟨68,42,43⟩),(r412,⟨68,42,43⟩),(r413,⟨68,42,43⟩),(r414,⟨68,42,43⟩),(r415,⟨68,42,43⟩)]
theorem checked51 : fastCheckList band b51=true := by decide +kernel

def b52 : List (Rectangle × FastWitness) := [(r416,⟨68,42,43⟩),(r417,⟨68,42,43⟩),(r418,⟨68,42,43⟩),(r419,⟨68,42,43⟩),(r420,⟨68,42,43⟩),(r421,⟨68,42,43⟩),(r422,⟨68,42,43⟩),(r423,⟨68,42,43⟩)]
theorem checked52 : fastCheckList band b52=true := by decide +kernel

def b53 : List (Rectangle × FastWitness) := [(r424,⟨68,42,43⟩),(r425,⟨68,42,43⟩),(r426,⟨68,42,43⟩),(r427,⟨68,42,43⟩),(r428,⟨68,42,43⟩),(r429,⟨68,42,43⟩),(r430,⟨68,42,43⟩),(r431,⟨68,42,43⟩)]
theorem checked53 : fastCheckList band b53=true := by decide +kernel

def b54 : List (Rectangle × FastWitness) := [(r432,⟨68,42,43⟩),(r433,⟨68,42,43⟩),(r434,⟨68,42,43⟩),(r435,⟨68,42,43⟩),(r436,⟨68,42,43⟩),(r437,⟨68,42,43⟩),(r438,⟨68,42,43⟩),(r439,⟨68,42,43⟩)]
theorem checked54 : fastCheckList band b54=true := by decide +kernel

def b55 : List (Rectangle × FastWitness) := [(r440,⟨68,42,43⟩),(r441,⟨68,42,43⟩),(r442,⟨68,42,43⟩),(r443,⟨68,42,43⟩),(r444,⟨68,42,43⟩),(r445,⟨68,42,43⟩),(r446,⟨68,42,43⟩),(r447,⟨68,42,43⟩)]
theorem checked55 : fastCheckList band b55=true := by decide +kernel

def b56 : List (Rectangle × FastWitness) := [(r448,⟨68,42,43⟩),(r449,⟨68,42,43⟩),(r450,⟨68,42,43⟩),(r451,⟨68,42,43⟩),(r452,⟨68,42,43⟩),(r453,⟨68,42,43⟩),(r454,⟨68,42,43⟩),(r455,⟨68,42,43⟩)]
theorem checked56 : fastCheckList band b56=true := by decide +kernel

def b57 : List (Rectangle × FastWitness) := [(r456,⟨68,42,43⟩),(r457,⟨68,42,43⟩),(r458,⟨68,42,43⟩),(r459,⟨68,42,43⟩),(r460,⟨68,42,43⟩),(r461,⟨68,42,43⟩),(r462,⟨68,42,43⟩),(r463,⟨68,42,43⟩)]
theorem checked57 : fastCheckList band b57=true := by decide +kernel

def b58 : List (Rectangle × FastWitness) := [(r464,⟨68,42,43⟩),(r465,⟨68,42,43⟩),(r466,⟨68,42,43⟩),(r467,⟨68,42,43⟩),(r468,⟨68,42,43⟩),(r469,⟨68,42,43⟩),(r470,⟨68,42,43⟩),(r471,⟨68,42,43⟩)]
theorem checked58 : fastCheckList band b58=true := by decide +kernel

def b59 : List (Rectangle × FastWitness) := [(r472,⟨68,42,43⟩),(r473,⟨68,42,43⟩),(r474,⟨68,42,43⟩),(r475,⟨68,42,43⟩),(r476,⟨68,42,43⟩),(r477,⟨68,42,43⟩),(r478,⟨68,42,43⟩),(r479,⟨68,42,43⟩)]
theorem checked59 : fastCheckList band b59=true := by decide +kernel

def b60 : List (Rectangle × FastWitness) := [(r480,⟨68,42,43⟩),(r481,⟨68,42,43⟩),(r482,⟨68,42,43⟩),(r483,⟨68,42,43⟩),(r484,⟨68,42,43⟩),(r485,⟨68,42,43⟩),(r486,⟨68,42,43⟩),(r487,⟨68,42,43⟩)]
theorem checked60 : fastCheckList band b60=true := by decide +kernel

def b61 : List (Rectangle × FastWitness) := [(r488,⟨68,42,43⟩),(r489,⟨68,42,43⟩),(r490,⟨68,42,43⟩),(r491,⟨68,42,43⟩),(r492,⟨68,42,43⟩),(r493,⟨68,42,43⟩),(r494,⟨68,42,43⟩),(r495,⟨68,42,43⟩)]
theorem checked61 : fastCheckList band b61=true := by decide +kernel

def b62 : List (Rectangle × FastWitness) := [(r496,⟨68,42,43⟩),(r497,⟨68,43,43⟩),(r498,⟨68,43,43⟩),(r499,⟨68,43,43⟩),(r500,⟨68,43,43⟩),(r501,⟨68,43,43⟩),(r502,⟨68,43,43⟩),(r503,⟨68,43,43⟩)]
theorem checked62 : fastCheckList band b62=true := by decide +kernel

def b63 : List (Rectangle × FastWitness) := [(r504,⟨68,43,43⟩),(r505,⟨68,43,43⟩),(r506,⟨68,43,43⟩),(r507,⟨68,43,43⟩),(r508,⟨68,43,43⟩),(r509,⟨68,43,43⟩),(r510,⟨68,43,43⟩),(r511,⟨68,43,43⟩)]
theorem checked63 : fastCheckList band b63=true := by decide +kernel

def b64 : List (Rectangle × FastWitness) := [(r512,⟨68,43,43⟩),(r513,⟨68,43,43⟩),(r514,⟨68,43,43⟩),(r515,⟨68,43,43⟩),(r516,⟨68,43,43⟩),(r517,⟨68,43,43⟩),(r518,⟨68,43,43⟩),(r519,⟨68,43,43⟩)]
theorem checked64 : fastCheckList band b64=true := by decide +kernel

def b65 : List (Rectangle × FastWitness) := [(r520,⟨68,43,43⟩),(r521,⟨68,43,43⟩),(r522,⟨68,43,43⟩),(r523,⟨68,43,43⟩),(r524,⟨68,43,43⟩),(r525,⟨68,43,43⟩),(r526,⟨68,43,43⟩),(r527,⟨68,43,43⟩)]
theorem checked65 : fastCheckList band b65=true := by decide +kernel

def b66 : List (Rectangle × FastWitness) := [(r528,⟨68,43,43⟩),(r529,⟨68,43,43⟩),(r530,⟨68,43,43⟩),(r531,⟨68,43,43⟩),(r532,⟨68,43,43⟩),(r533,⟨68,43,43⟩),(r534,⟨68,43,43⟩),(r535,⟨68,43,43⟩)]
theorem checked66 : fastCheckList band b66=true := by decide +kernel

def b67 : List (Rectangle × FastWitness) := [(r536,⟨68,43,43⟩),(r537,⟨68,43,43⟩),(r538,⟨68,43,43⟩),(r539,⟨68,43,43⟩),(r540,⟨68,43,43⟩),(r541,⟨68,43,43⟩),(r542,⟨68,43,43⟩),(r543,⟨68,43,43⟩)]
theorem checked67 : fastCheckList band b67=true := by decide +kernel

def b68 : List (Rectangle × FastWitness) := [(r544,⟨68,43,43⟩),(r545,⟨68,43,43⟩),(r546,⟨68,43,43⟩),(r547,⟨68,43,43⟩),(r548,⟨68,43,43⟩),(r549,⟨68,43,43⟩),(r550,⟨68,43,43⟩),(r551,⟨68,43,43⟩)]
theorem checked68 : fastCheckList band b68=true := by decide +kernel

def b69 : List (Rectangle × FastWitness) := [(r552,⟨68,43,43⟩),(r553,⟨68,43,43⟩),(r554,⟨68,43,43⟩),(r555,⟨68,43,43⟩),(r556,⟨68,43,43⟩),(r557,⟨68,43,43⟩),(r558,⟨68,43,43⟩),(r559,⟨68,43,43⟩)]
theorem checked69 : fastCheckList band b69=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast


