-- Prove2me | Definitions.Def_Yukon_27892ecd094dc72d57113e4a
-- name    : Yukon_27892ecd094dc72d57113e4a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:45:43.419657+00:00
-- url     : https://prove2.me/theorems/47747b71-b8b3-4392-875a-6fdac3820fe0
-- title:
--   Relative certificate source part 3/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_27892ecd094dc72d57113e4a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTIyNzVkOGI4MTUzODlkOTY2MTIzZGNkZDZmZjVlMjNiNWY4ZmUxMTk2ODNkMGIyYjVjY2ZlOGRjMTY2NGE0NSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uXzI3ODkyZWNkMDk0ZGM3MmQ1NzExM2U0YSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzI3ODkyZWNkMDk0ZGM3MmQ1NzExM2U0YSIsInYiOjJ9]

import Definitions.Def_Yukon_93f639d3938205e1e2162e83
import Definitions.Def_Yukon_e757298719adf05c20287f89












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: c5a3d79401563549e3da246da1fa707d32f52f28e1c561a2e007749bd764d43f.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b32 : List (Rectangle × FastWitness) := [(r256,⟨67,40,40⟩),(r257,⟨67,40,40⟩),(r258,⟨67,40,40⟩),(r259,⟨67,40,40⟩),(r260,⟨67,40,40⟩),(r261,⟨67,40,40⟩),(r262,⟨67,40,40⟩),(r263,⟨67,40,40⟩)]
theorem checked32 : fastCheckList band b32=true := by decide +kernel

def b33 : List (Rectangle × FastWitness) := [(r264,⟨67,40,40⟩),(r265,⟨67,40,40⟩),(r266,⟨67,40,40⟩),(r267,⟨67,40,40⟩),(r268,⟨67,40,40⟩),(r269,⟨67,40,40⟩),(r270,⟨67,40,40⟩),(r271,⟨67,40,40⟩)]
theorem checked33 : fastCheckList band b33=true := by decide +kernel

def b34 : List (Rectangle × FastWitness) := [(r272,⟨67,40,40⟩),(r273,⟨67,40,40⟩),(r274,⟨67,40,40⟩),(r275,⟨67,40,40⟩),(r276,⟨67,40,40⟩),(r277,⟨67,40,40⟩),(r278,⟨67,40,40⟩),(r279,⟨67,40,40⟩)]
theorem checked34 : fastCheckList band b34=true := by decide +kernel

def b35 : List (Rectangle × FastWitness) := [(r280,⟨67,40,40⟩),(r281,⟨67,40,40⟩),(r282,⟨67,40,40⟩),(r283,⟨67,40,40⟩),(r284,⟨67,40,40⟩),(r285,⟨67,40,40⟩),(r286,⟨67,40,40⟩),(r287,⟨67,40,40⟩)]
theorem checked35 : fastCheckList band b35=true := by decide +kernel

def b36 : List (Rectangle × FastWitness) := [(r288,⟨67,40,40⟩),(r289,⟨67,40,40⟩),(r290,⟨67,40,40⟩),(r291,⟨67,40,40⟩),(r292,⟨67,40,40⟩),(r293,⟨67,40,40⟩),(r294,⟨67,40,40⟩),(r295,⟨67,40,40⟩)]
theorem checked36 : fastCheckList band b36=true := by decide +kernel

def b37 : List (Rectangle × FastWitness) := [(r296,⟨67,40,40⟩),(r297,⟨67,40,40⟩),(r298,⟨67,40,40⟩),(r299,⟨67,40,40⟩),(r300,⟨67,40,40⟩),(r301,⟨67,40,40⟩),(r302,⟨67,40,40⟩),(r303,⟨67,40,40⟩)]
theorem checked37 : fastCheckList band b37=true := by decide +kernel

def b38 : List (Rectangle × FastWitness) := [(r304,⟨67,40,40⟩),(r305,⟨67,40,40⟩),(r306,⟨67,40,40⟩),(r307,⟨67,40,40⟩),(r308,⟨67,40,40⟩),(r309,⟨67,40,40⟩),(r310,⟨67,40,40⟩),(r311,⟨67,40,40⟩)]
theorem checked38 : fastCheckList band b38=true := by decide +kernel

def b39 : List (Rectangle × FastWitness) := [(r312,⟨67,40,40⟩),(r313,⟨67,40,40⟩),(r314,⟨67,40,40⟩),(r315,⟨67,40,40⟩),(r316,⟨67,40,40⟩),(r317,⟨67,40,40⟩),(r318,⟨67,40,40⟩),(r319,⟨67,40,40⟩)]
theorem checked39 : fastCheckList band b39=true := by decide +kernel

def b40 : List (Rectangle × FastWitness) := [(r320,⟨67,40,40⟩),(r321,⟨67,40,40⟩),(r322,⟨67,40,40⟩),(r323,⟨67,40,40⟩),(r324,⟨67,40,40⟩),(r325,⟨67,40,40⟩),(r326,⟨67,40,40⟩),(r327,⟨67,40,40⟩)]
theorem checked40 : fastCheckList band b40=true := by decide +kernel

def b41 : List (Rectangle × FastWitness) := [(r328,⟨67,40,40⟩),(r329,⟨67,40,40⟩),(r330,⟨67,40,40⟩),(r331,⟨67,40,40⟩),(r332,⟨67,40,40⟩),(r333,⟨67,40,40⟩),(r334,⟨67,40,40⟩),(r335,⟨67,40,40⟩)]
theorem checked41 : fastCheckList band b41=true := by decide +kernel

def b42 : List (Rectangle × FastWitness) := [(r336,⟨67,40,40⟩),(r337,⟨67,40,40⟩),(r338,⟨67,40,40⟩),(r339,⟨67,40,40⟩),(r340,⟨67,40,40⟩),(r341,⟨67,40,40⟩),(r342,⟨67,40,40⟩),(r343,⟨67,40,40⟩)]
theorem checked42 : fastCheckList band b42=true := by decide +kernel

def b43 : List (Rectangle × FastWitness) := [(r344,⟨67,40,40⟩),(r345,⟨67,40,40⟩),(r346,⟨67,40,40⟩),(r347,⟨67,40,40⟩),(r348,⟨67,40,40⟩),(r349,⟨67,40,40⟩),(r350,⟨67,40,40⟩),(r351,⟨67,40,40⟩)]
theorem checked43 : fastCheckList band b43=true := by decide +kernel

def b44 : List (Rectangle × FastWitness) := [(r352,⟨67,40,40⟩),(r353,⟨67,40,40⟩),(r354,⟨67,40,40⟩),(r355,⟨67,40,40⟩),(r356,⟨67,40,40⟩),(r357,⟨67,40,40⟩),(r358,⟨67,40,40⟩),(r359,⟨67,40,40⟩)]
theorem checked44 : fastCheckList band b44=true := by decide +kernel

def b45 : List (Rectangle × FastWitness) := [(r360,⟨67,40,40⟩),(r361,⟨67,40,40⟩),(r362,⟨67,40,40⟩),(r363,⟨67,40,40⟩),(r364,⟨67,40,40⟩),(r365,⟨67,40,40⟩),(r366,⟨67,40,40⟩),(r367,⟨67,40,40⟩)]
theorem checked45 : fastCheckList band b45=true := by decide +kernel

def b46 : List (Rectangle × FastWitness) := [(r368,⟨67,40,40⟩),(r369,⟨67,40,40⟩),(r370,⟨67,40,40⟩),(r371,⟨67,40,40⟩),(r372,⟨67,40,40⟩),(r373,⟨67,40,40⟩),(r374,⟨67,40,40⟩),(r375,⟨67,40,40⟩)]
theorem checked46 : fastCheckList band b46=true := by decide +kernel

def b47 : List (Rectangle × FastWitness) := [(r376,⟨67,40,40⟩),(r377,⟨67,40,40⟩),(r378,⟨67,40,40⟩),(r379,⟨67,40,40⟩),(r380,⟨67,40,40⟩),(r381,⟨67,40,40⟩),(r382,⟨67,40,40⟩),(r383,⟨67,40,40⟩)]
theorem checked47 : fastCheckList band b47=true := by decide +kernel

def b48 : List (Rectangle × FastWitness) := [(r384,⟨67,40,40⟩),(r385,⟨67,40,40⟩),(r386,⟨67,40,40⟩),(r387,⟨67,40,40⟩),(r388,⟨67,40,40⟩),(r389,⟨67,40,40⟩),(r390,⟨67,40,40⟩),(r391,⟨67,40,40⟩)]
theorem checked48 : fastCheckList band b48=true := by decide +kernel

def b49 : List (Rectangle × FastWitness) := [(r392,⟨67,40,40⟩),(r393,⟨67,40,40⟩),(r394,⟨67,40,40⟩),(r395,⟨67,40,40⟩),(r396,⟨67,40,40⟩),(r397,⟨67,40,40⟩),(r398,⟨67,40,40⟩),(r399,⟨67,40,40⟩)]
theorem checked49 : fastCheckList band b49=true := by decide +kernel

def b50 : List (Rectangle × FastWitness) := [(r400,⟨67,40,40⟩),(r401,⟨67,40,40⟩),(r402,⟨67,40,40⟩),(r403,⟨67,40,40⟩),(r404,⟨67,40,40⟩),(r405,⟨67,40,40⟩),(r406,⟨67,40,40⟩),(r407,⟨67,40,40⟩)]
theorem checked50 : fastCheckList band b50=true := by decide +kernel

def b51 : List (Rectangle × FastWitness) := [(r408,⟨67,40,40⟩),(r409,⟨67,40,40⟩),(r410,⟨67,40,40⟩),(r411,⟨67,40,40⟩),(r412,⟨67,40,40⟩),(r413,⟨67,40,40⟩),(r414,⟨67,40,40⟩),(r415,⟨67,40,40⟩)]
theorem checked51 : fastCheckList band b51=true := by decide +kernel

def b52 : List (Rectangle × FastWitness) := [(r416,⟨67,40,40⟩),(r417,⟨67,40,40⟩),(r418,⟨67,40,40⟩),(r419,⟨67,40,40⟩),(r420,⟨67,40,40⟩),(r421,⟨67,40,40⟩),(r422,⟨67,40,40⟩),(r423,⟨67,40,40⟩)]
theorem checked52 : fastCheckList band b52=true := by decide +kernel

def b53 : List (Rectangle × FastWitness) := [(r424,⟨67,40,40⟩),(r425,⟨67,40,40⟩),(r426,⟨67,40,40⟩),(r427,⟨67,40,40⟩),(r428,⟨67,40,40⟩),(r429,⟨67,40,40⟩),(r430,⟨67,40,40⟩),(r431,⟨67,40,40⟩)]
theorem checked53 : fastCheckList band b53=true := by decide +kernel

def b54 : List (Rectangle × FastWitness) := [(r432,⟨67,40,40⟩),(r433,⟨67,40,40⟩),(r434,⟨67,40,40⟩),(r435,⟨67,40,40⟩),(r436,⟨67,40,40⟩),(r437,⟨67,40,40⟩),(r438,⟨67,40,40⟩),(r439,⟨67,40,40⟩)]
theorem checked54 : fastCheckList band b54=true := by decide +kernel

def b55 : List (Rectangle × FastWitness) := [(r440,⟨67,40,40⟩),(r441,⟨67,40,40⟩),(r442,⟨67,40,40⟩),(r443,⟨67,40,40⟩),(r444,⟨67,40,40⟩),(r445,⟨67,40,40⟩),(r446,⟨67,40,40⟩),(r447,⟨67,40,40⟩)]
theorem checked55 : fastCheckList band b55=true := by decide +kernel

def b56 : List (Rectangle × FastWitness) := [(r448,⟨67,40,40⟩),(r449,⟨67,40,40⟩),(r450,⟨67,40,40⟩),(r451,⟨67,40,40⟩),(r452,⟨67,40,40⟩),(r453,⟨67,40,40⟩),(r454,⟨67,40,40⟩),(r455,⟨67,40,40⟩)]
theorem checked56 : fastCheckList band b56=true := by decide +kernel

def b57 : List (Rectangle × FastWitness) := [(r456,⟨67,40,40⟩),(r457,⟨67,40,40⟩),(r458,⟨67,40,40⟩),(r459,⟨67,40,40⟩),(r460,⟨67,40,40⟩),(r461,⟨67,40,40⟩),(r462,⟨67,40,40⟩),(r463,⟨67,40,40⟩)]
theorem checked57 : fastCheckList band b57=true := by decide +kernel

def b58 : List (Rectangle × FastWitness) := [(r464,⟨67,40,40⟩),(r465,⟨67,40,40⟩),(r466,⟨67,40,40⟩),(r467,⟨67,40,40⟩),(r468,⟨67,40,40⟩),(r469,⟨67,40,40⟩),(r470,⟨67,40,40⟩),(r471,⟨67,40,40⟩)]
theorem checked58 : fastCheckList band b58=true := by decide +kernel

def b59 : List (Rectangle × FastWitness) := [(r472,⟨67,40,40⟩),(r473,⟨67,40,40⟩),(r474,⟨67,40,40⟩),(r475,⟨67,40,40⟩),(r476,⟨67,40,40⟩),(r477,⟨67,40,40⟩),(r478,⟨67,40,40⟩),(r479,⟨67,40,40⟩)]
theorem checked59 : fastCheckList band b59=true := by decide +kernel

def b60 : List (Rectangle × FastWitness) := [(r480,⟨67,40,40⟩),(r481,⟨67,40,40⟩),(r482,⟨67,40,40⟩),(r483,⟨67,40,40⟩),(r484,⟨67,40,40⟩),(r485,⟨67,40,40⟩),(r486,⟨67,40,40⟩),(r487,⟨67,40,40⟩)]
theorem checked60 : fastCheckList band b60=true := by decide +kernel

def b61 : List (Rectangle × FastWitness) := [(r488,⟨67,40,40⟩),(r489,⟨67,40,40⟩),(r490,⟨67,40,40⟩),(r491,⟨67,40,40⟩),(r492,⟨67,40,40⟩),(r493,⟨67,40,40⟩),(r494,⟨67,40,40⟩),(r495,⟨67,40,40⟩)]
theorem checked61 : fastCheckList band b61=true := by decide +kernel

def b62 : List (Rectangle × FastWitness) := [(r496,⟨67,40,40⟩),(r497,⟨67,40,40⟩),(r498,⟨67,40,40⟩),(r499,⟨67,40,40⟩),(r500,⟨67,40,40⟩),(r501,⟨67,40,40⟩),(r502,⟨67,40,40⟩),(r503,⟨67,40,40⟩)]
theorem checked62 : fastCheckList band b62=true := by decide +kernel

def b63 : List (Rectangle × FastWitness) := [(r504,⟨67,40,40⟩),(r505,⟨67,40,40⟩),(r506,⟨67,40,40⟩),(r507,⟨67,40,40⟩),(r508,⟨67,40,40⟩),(r509,⟨67,40,40⟩),(r510,⟨67,40,40⟩),(r511,⟨67,40,40⟩)]
theorem checked63 : fastCheckList band b63=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


