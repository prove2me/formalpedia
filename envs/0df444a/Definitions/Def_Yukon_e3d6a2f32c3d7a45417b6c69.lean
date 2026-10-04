-- Prove2me | Definitions.Def_Yukon_e3d6a2f32c3d7a45417b6c69
-- name    : Yukon_e3d6a2f32c3d7a45417b6c69
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:05:49.881515+00:00
-- url     : https://prove2.me/theorems/b1dcd7db-35ad-4108-85fa-c72ba7a80459
-- title:
--   Relative certificate source part 3/8
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
--
--   yukon-proof-operation:certificate-b58-module-Yukon_e3d6a2f32c3d7a45417b6c69
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDU3OTljNGE4NWM3YTc1MWRkZTIyNjkyMmU4ZTk3YjAxYzk3ZGYyMTNiYTZjZTk5OTU5MDlkZWU3MWQzZTVlZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1OC1tb2R1bGUtWXVrb25fZTNkNmEyZjMyYzNkN2E0NTQxN2I2YzY5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZTNkNmEyZjMyYzNkN2E0NTQxN2I2YzY5IiwidiI6Mn0]

import Definitions.Def_Yukon_31f07acb57a8a8d5ca2bbbda
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_5a41472b766ae83852cae05b











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 260bcf0650f7b5b3a615c929dc34473a82a4248f4336de3d1583e250ba65488d.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b36 : List (Rectangle × FastWitness) := [(r288,⟨70,42,42⟩),(r289,⟨70,42,42⟩),(r290,⟨70,42,42⟩),(r291,⟨70,42,42⟩),(r292,⟨70,42,42⟩),(r293,⟨70,42,42⟩),(r294,⟨70,42,42⟩),(r295,⟨70,42,42⟩)]
theorem checked36 : fastCheckList band b36=true := by decide +kernel

def b37 : List (Rectangle × FastWitness) := [(r296,⟨70,42,42⟩),(r297,⟨70,42,42⟩),(r298,⟨70,42,42⟩),(r299,⟨70,42,42⟩),(r300,⟨70,42,42⟩),(r301,⟨70,42,42⟩),(r302,⟨70,42,42⟩),(r303,⟨70,42,42⟩)]
theorem checked37 : fastCheckList band b37=true := by decide +kernel

def b38 : List (Rectangle × FastWitness) := [(r304,⟨70,42,42⟩),(r305,⟨70,42,42⟩),(r306,⟨70,42,42⟩),(r307,⟨70,42,42⟩),(r308,⟨70,42,42⟩),(r309,⟨70,42,42⟩),(r310,⟨70,42,42⟩),(r311,⟨70,42,42⟩)]
theorem checked38 : fastCheckList band b38=true := by decide +kernel

def b39 : List (Rectangle × FastWitness) := [(r312,⟨70,42,42⟩),(r313,⟨70,42,42⟩),(r314,⟨70,42,42⟩),(r315,⟨70,42,42⟩),(r316,⟨70,42,42⟩),(r317,⟨70,42,42⟩),(r318,⟨70,42,42⟩),(r319,⟨70,42,42⟩)]
theorem checked39 : fastCheckList band b39=true := by decide +kernel

def b40 : List (Rectangle × FastWitness) := [(r320,⟨70,42,42⟩),(r321,⟨70,42,42⟩),(r322,⟨70,42,42⟩),(r323,⟨70,42,42⟩),(r324,⟨70,42,42⟩),(r325,⟨70,42,42⟩),(r326,⟨70,42,42⟩),(r327,⟨70,42,42⟩)]
theorem checked40 : fastCheckList band b40=true := by decide +kernel

def b41 : List (Rectangle × FastWitness) := [(r328,⟨70,42,42⟩),(r329,⟨70,42,42⟩),(r330,⟨70,42,42⟩),(r331,⟨70,42,42⟩),(r332,⟨70,42,42⟩),(r333,⟨70,42,42⟩),(r334,⟨70,42,42⟩),(r335,⟨70,42,42⟩)]
theorem checked41 : fastCheckList band b41=true := by decide +kernel

def b42 : List (Rectangle × FastWitness) := [(r336,⟨70,42,42⟩),(r337,⟨70,42,42⟩),(r338,⟨70,42,42⟩),(r339,⟨70,42,42⟩),(r340,⟨70,42,42⟩),(r341,⟨70,42,42⟩),(r342,⟨70,42,42⟩),(r343,⟨70,42,42⟩)]
theorem checked42 : fastCheckList band b42=true := by decide +kernel

def b43 : List (Rectangle × FastWitness) := [(r344,⟨70,42,42⟩),(r345,⟨70,42,42⟩),(r346,⟨70,42,42⟩),(r347,⟨70,42,42⟩),(r348,⟨70,42,42⟩),(r349,⟨70,42,42⟩),(r350,⟨70,42,42⟩),(r351,⟨70,42,42⟩)]
theorem checked43 : fastCheckList band b43=true := by decide +kernel

def b44 : List (Rectangle × FastWitness) := [(r352,⟨70,42,42⟩),(r353,⟨70,42,42⟩),(r354,⟨70,42,42⟩),(r355,⟨70,42,42⟩),(r356,⟨70,42,42⟩),(r357,⟨70,42,42⟩),(r358,⟨70,42,42⟩),(r359,⟨70,42,42⟩)]
theorem checked44 : fastCheckList band b44=true := by decide +kernel

def b45 : List (Rectangle × FastWitness) := [(r360,⟨70,42,42⟩),(r361,⟨70,42,42⟩),(r362,⟨70,42,42⟩),(r363,⟨70,42,42⟩),(r364,⟨70,42,42⟩),(r365,⟨70,42,42⟩),(r366,⟨70,42,42⟩),(r367,⟨70,42,42⟩)]
theorem checked45 : fastCheckList band b45=true := by decide +kernel

def b46 : List (Rectangle × FastWitness) := [(r368,⟨70,42,42⟩),(r369,⟨70,42,42⟩),(r370,⟨70,42,42⟩),(r371,⟨70,42,42⟩),(r372,⟨70,42,42⟩),(r373,⟨70,42,42⟩),(r374,⟨70,42,42⟩),(r375,⟨70,42,42⟩)]
theorem checked46 : fastCheckList band b46=true := by decide +kernel

def b47 : List (Rectangle × FastWitness) := [(r376,⟨70,42,42⟩),(r377,⟨70,42,42⟩),(r378,⟨70,42,42⟩),(r379,⟨70,42,42⟩),(r380,⟨70,42,42⟩),(r381,⟨70,42,42⟩),(r382,⟨70,42,42⟩),(r383,⟨70,42,42⟩)]
theorem checked47 : fastCheckList band b47=true := by decide +kernel

def b48 : List (Rectangle × FastWitness) := [(r384,⟨70,42,42⟩),(r385,⟨70,42,42⟩),(r386,⟨70,42,42⟩),(r387,⟨70,42,42⟩),(r388,⟨70,42,42⟩),(r389,⟨70,42,42⟩),(r390,⟨70,42,42⟩),(r391,⟨70,42,42⟩)]
theorem checked48 : fastCheckList band b48=true := by decide +kernel

def b49 : List (Rectangle × FastWitness) := [(r392,⟨70,42,42⟩),(r393,⟨70,42,42⟩),(r394,⟨70,42,42⟩),(r395,⟨70,42,42⟩),(r396,⟨70,42,42⟩),(r397,⟨70,42,42⟩),(r398,⟨70,42,42⟩),(r399,⟨70,42,42⟩)]
theorem checked49 : fastCheckList band b49=true := by decide +kernel

def b50 : List (Rectangle × FastWitness) := [(r400,⟨70,42,42⟩),(r401,⟨70,42,42⟩),(r402,⟨70,42,42⟩),(r403,⟨70,42,42⟩),(r404,⟨70,42,42⟩),(r405,⟨70,42,42⟩),(r406,⟨70,42,42⟩),(r407,⟨70,42,42⟩)]
theorem checked50 : fastCheckList band b50=true := by decide +kernel

def b51 : List (Rectangle × FastWitness) := [(r408,⟨70,42,42⟩),(r409,⟨70,42,42⟩),(r410,⟨70,42,42⟩),(r411,⟨70,42,42⟩),(r412,⟨70,42,42⟩),(r413,⟨70,42,42⟩),(r414,⟨70,42,42⟩),(r415,⟨70,42,42⟩)]
theorem checked51 : fastCheckList band b51=true := by decide +kernel

def b52 : List (Rectangle × FastWitness) := [(r416,⟨70,42,42⟩),(r417,⟨70,42,42⟩),(r418,⟨70,42,42⟩),(r419,⟨70,42,42⟩),(r420,⟨70,42,42⟩),(r421,⟨70,42,42⟩),(r422,⟨70,42,42⟩),(r423,⟨70,42,42⟩)]
theorem checked52 : fastCheckList band b52=true := by decide +kernel

def b53 : List (Rectangle × FastWitness) := [(r424,⟨70,42,42⟩),(r425,⟨70,42,42⟩),(r426,⟨70,42,42⟩),(r427,⟨70,42,42⟩),(r428,⟨70,42,42⟩),(r429,⟨70,42,42⟩),(r430,⟨70,42,42⟩),(r431,⟨70,42,42⟩)]
theorem checked53 : fastCheckList band b53=true := by decide +kernel

def b54 : List (Rectangle × FastWitness) := [(r432,⟨70,42,42⟩),(r433,⟨70,42,42⟩),(r434,⟨70,42,42⟩),(r435,⟨70,42,42⟩),(r436,⟨70,42,42⟩),(r437,⟨70,42,42⟩),(r438,⟨70,42,42⟩),(r439,⟨70,42,42⟩)]
theorem checked54 : fastCheckList band b54=true := by decide +kernel

def b55 : List (Rectangle × FastWitness) := [(r440,⟨70,42,42⟩),(r441,⟨70,42,42⟩),(r442,⟨70,42,42⟩),(r443,⟨70,42,42⟩),(r444,⟨70,42,42⟩),(r445,⟨70,42,42⟩),(r446,⟨70,42,42⟩),(r447,⟨70,42,42⟩)]
theorem checked55 : fastCheckList band b55=true := by decide +kernel

def b56 : List (Rectangle × FastWitness) := [(r448,⟨70,42,42⟩),(r449,⟨70,42,42⟩),(r450,⟨70,42,42⟩),(r451,⟨70,42,42⟩),(r452,⟨70,42,42⟩),(r453,⟨70,42,42⟩),(r454,⟨70,42,42⟩),(r455,⟨70,42,42⟩)]
theorem checked56 : fastCheckList band b56=true := by decide +kernel

def b57 : List (Rectangle × FastWitness) := [(r456,⟨70,42,42⟩),(r457,⟨70,42,42⟩),(r458,⟨70,42,42⟩),(r459,⟨70,42,42⟩),(r460,⟨70,42,42⟩),(r461,⟨70,42,42⟩),(r462,⟨70,42,42⟩),(r463,⟨70,42,42⟩)]
theorem checked57 : fastCheckList band b57=true := by decide +kernel

def b58 : List (Rectangle × FastWitness) := [(r464,⟨70,42,42⟩),(r465,⟨70,42,42⟩),(r466,⟨70,42,42⟩),(r467,⟨70,42,42⟩),(r468,⟨70,42,42⟩),(r469,⟨70,42,42⟩),(r470,⟨70,42,42⟩),(r471,⟨70,42,42⟩)]
theorem checked58 : fastCheckList band b58=true := by decide +kernel

def b59 : List (Rectangle × FastWitness) := [(r472,⟨70,42,42⟩),(r473,⟨70,42,42⟩),(r474,⟨70,42,42⟩),(r475,⟨70,42,42⟩),(r476,⟨70,42,42⟩),(r477,⟨70,42,42⟩),(r478,⟨70,42,42⟩),(r479,⟨70,42,42⟩)]
theorem checked59 : fastCheckList band b59=true := by decide +kernel

def b60 : List (Rectangle × FastWitness) := [(r480,⟨70,42,42⟩),(r481,⟨70,42,42⟩),(r482,⟨70,42,42⟩),(r483,⟨70,42,42⟩),(r484,⟨70,42,42⟩),(r485,⟨70,42,42⟩),(r486,⟨70,42,42⟩),(r487,⟨70,42,42⟩)]
theorem checked60 : fastCheckList band b60=true := by decide +kernel

def b61 : List (Rectangle × FastWitness) := [(r488,⟨70,42,42⟩),(r489,⟨70,42,42⟩),(r490,⟨70,42,42⟩),(r491,⟨70,42,42⟩),(r492,⟨70,42,42⟩),(r493,⟨70,42,42⟩),(r494,⟨70,42,42⟩),(r495,⟨70,42,42⟩)]
theorem checked61 : fastCheckList band b61=true := by decide +kernel

def b62 : List (Rectangle × FastWitness) := [(r496,⟨70,42,42⟩),(r497,⟨70,42,42⟩),(r498,⟨70,42,42⟩),(r499,⟨70,42,42⟩),(r500,⟨70,42,42⟩),(r501,⟨70,42,42⟩),(r502,⟨70,42,42⟩),(r503,⟨70,42,42⟩)]
theorem checked62 : fastCheckList band b62=true := by decide +kernel

def b63 : List (Rectangle × FastWitness) := [(r504,⟨70,42,42⟩),(r505,⟨70,42,42⟩),(r506,⟨70,42,42⟩),(r507,⟨70,42,42⟩),(r508,⟨70,42,42⟩),(r509,⟨70,42,42⟩),(r510,⟨70,42,42⟩),(r511,⟨70,42,42⟩)]
theorem checked63 : fastCheckList band b63=true := by decide +kernel

def b64 : List (Rectangle × FastWitness) := [(r512,⟨70,42,42⟩),(r513,⟨70,42,42⟩),(r514,⟨70,42,42⟩),(r515,⟨70,42,42⟩),(r516,⟨70,42,42⟩),(r517,⟨70,42,42⟩),(r518,⟨70,42,42⟩),(r519,⟨70,42,42⟩)]
theorem checked64 : fastCheckList band b64=true := by decide +kernel

def b65 : List (Rectangle × FastWitness) := [(r520,⟨70,42,42⟩),(r521,⟨70,42,42⟩),(r522,⟨70,42,42⟩),(r523,⟨70,42,42⟩),(r524,⟨70,42,42⟩),(r525,⟨70,42,42⟩),(r526,⟨70,42,42⟩),(r527,⟨70,42,42⟩)]
theorem checked65 : fastCheckList band b65=true := by decide +kernel

def b66 : List (Rectangle × FastWitness) := [(r528,⟨70,42,42⟩),(r529,⟨70,42,42⟩),(r530,⟨70,42,42⟩),(r531,⟨70,42,42⟩),(r532,⟨70,42,42⟩),(r533,⟨70,42,42⟩),(r534,⟨70,42,42⟩),(r535,⟨70,42,42⟩)]
theorem checked66 : fastCheckList band b66=true := by decide +kernel

def b67 : List (Rectangle × FastWitness) := [(r536,⟨70,42,42⟩),(r537,⟨70,42,42⟩),(r538,⟨70,42,42⟩),(r539,⟨70,42,42⟩),(r540,⟨70,42,42⟩),(r541,⟨70,42,42⟩),(r542,⟨70,42,42⟩),(r543,⟨70,42,42⟩)]
theorem checked67 : fastCheckList band b67=true := by decide +kernel

def b68 : List (Rectangle × FastWitness) := [(r544,⟨70,42,42⟩),(r545,⟨70,42,42⟩),(r546,⟨70,42,42⟩),(r547,⟨70,42,42⟩),(r548,⟨70,42,42⟩),(r549,⟨70,42,42⟩),(r550,⟨70,42,42⟩),(r551,⟨70,42,42⟩)]
theorem checked68 : fastCheckList band b68=true := by decide +kernel

def b69 : List (Rectangle × FastWitness) := [(r552,⟨70,42,42⟩),(r553,⟨70,42,42⟩),(r554,⟨70,42,42⟩),(r555,⟨70,42,42⟩),(r556,⟨70,42,42⟩),(r557,⟨70,42,42⟩),(r558,⟨70,42,42⟩),(r559,⟨70,42,42⟩)]
theorem checked69 : fastCheckList band b69=true := by decide +kernel

def b70 : List (Rectangle × FastWitness) := [(r560,⟨70,42,42⟩),(r561,⟨70,42,42⟩),(r562,⟨70,42,42⟩),(r563,⟨70,42,42⟩),(r564,⟨70,42,42⟩),(r565,⟨70,42,42⟩),(r566,⟨70,42,42⟩),(r567,⟨70,42,42⟩)]
theorem checked70 : fastCheckList band b70=true := by decide +kernel

def b71 : List (Rectangle × FastWitness) := [(r568,⟨70,42,42⟩),(r569,⟨70,42,42⟩),(r570,⟨70,42,42⟩),(r571,⟨70,42,42⟩),(r572,⟨70,42,42⟩),(r573,⟨70,42,42⟩),(r574,⟨70,42,42⟩),(r575,⟨70,42,42⟩)]
theorem checked71 : fastCheckList band b71=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast


