-- Prove2me | Definitions.Def_Yukon_e5c1f5184c9f9303ee7a5551
-- name    : Yukon_e5c1f5184c9f9303ee7a5551
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:42:39.477809+00:00
-- url     : https://prove2.me/theorems/84c7f391-69da-4a14-8b36-42b3e0de8ed9
-- title:
--   Relative certificate source part 2/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_e5c1f5184c9f9303ee7a5551
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGY2OTMyMDQxNWQ0OTU4MDRlNjZiNDc0YTJjOGEzMGE4MDVjM2UxMzQzMWU2ZWI4MTEwNTNiMzUzMmQ3MDhiOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2U1YzFmNTE4NGM5ZjkzMDNlZTdhNTU1MSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2U1YzFmNTE4NGM5ZjkzMDNlZTdhNTU1MSIsInYiOjJ9]

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

def b0 : List (Rectangle × FastWitness) := [(r0,⟨67,40,46⟩),(r1,⟨67,39,52⟩),(r2,⟨67,39,54⟩),(r3,⟨67,1,41⟩),(r4,⟨67,1,40⟩),(r5,⟨67,39,54⟩),(r6,⟨67,1,41⟩),(r7,⟨67,1,41⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨67,1,41⟩),(r9,⟨67,1,40⟩),(r10,⟨67,1,41⟩),(r11,⟨67,1,41⟩),(r12,⟨67,1,40⟩),(r13,⟨67,1,40⟩),(r14,⟨67,1,41⟩),(r15,⟨67,1,40⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def b2 : List (Rectangle × FastWitness) := [(r16,⟨67,1,40⟩),(r17,⟨67,1,40⟩),(r18,⟨67,1,40⟩),(r19,⟨67,1,40⟩),(r20,⟨67,1,40⟩),(r21,⟨67,1,40⟩),(r22,⟨67,1,40⟩),(r23,⟨67,1,40⟩)]
theorem checked2 : fastCheckList band b2=true := by decide +kernel

def b3 : List (Rectangle × FastWitness) := [(r24,⟨67,1,40⟩),(r25,⟨67,1,40⟩),(r26,⟨67,1,40⟩),(r27,⟨67,1,40⟩),(r28,⟨67,1,40⟩),(r29,⟨67,1,40⟩),(r30,⟨67,1,40⟩),(r31,⟨67,1,40⟩)]
theorem checked3 : fastCheckList band b3=true := by decide +kernel

def b4 : List (Rectangle × FastWitness) := [(r32,⟨67,1,40⟩),(r33,⟨67,1,40⟩),(r34,⟨67,1,40⟩),(r35,⟨67,1,40⟩),(r36,⟨67,1,40⟩),(r37,⟨67,1,40⟩),(r38,⟨67,1,40⟩),(r39,⟨67,1,40⟩)]
theorem checked4 : fastCheckList band b4=true := by decide +kernel

def b5 : List (Rectangle × FastWitness) := [(r40,⟨67,1,40⟩),(r41,⟨67,1,40⟩),(r42,⟨67,1,40⟩),(r43,⟨67,1,40⟩),(r44,⟨67,1,40⟩),(r45,⟨67,1,40⟩),(r46,⟨67,1,40⟩),(r47,⟨67,1,40⟩)]
theorem checked5 : fastCheckList band b5=true := by decide +kernel

def b6 : List (Rectangle × FastWitness) := [(r48,⟨67,1,40⟩),(r49,⟨67,1,40⟩),(r50,⟨67,1,40⟩),(r51,⟨67,1,40⟩),(r52,⟨67,1,40⟩),(r53,⟨67,1,40⟩),(r54,⟨67,1,40⟩),(r55,⟨67,1,40⟩)]
theorem checked6 : fastCheckList band b6=true := by decide +kernel

def b7 : List (Rectangle × FastWitness) := [(r56,⟨67,1,40⟩),(r57,⟨67,1,40⟩),(r58,⟨67,1,40⟩),(r59,⟨67,1,40⟩),(r60,⟨67,1,40⟩),(r61,⟨67,1,40⟩),(r62,⟨67,1,40⟩),(r63,⟨67,1,40⟩)]
theorem checked7 : fastCheckList band b7=true := by decide +kernel

def b8 : List (Rectangle × FastWitness) := [(r64,⟨67,1,40⟩),(r65,⟨67,1,41⟩),(r66,⟨67,1,40⟩),(r67,⟨67,1,40⟩),(r68,⟨67,1,41⟩),(r69,⟨67,1,40⟩),(r70,⟨67,1,41⟩),(r71,⟨67,1,40⟩)]
theorem checked8 : fastCheckList band b8=true := by decide +kernel

def b9 : List (Rectangle × FastWitness) := [(r72,⟨67,1,40⟩),(r73,⟨67,1,41⟩),(r74,⟨67,1,40⟩),(r75,⟨67,1,40⟩),(r76,⟨67,1,40⟩),(r77,⟨67,1,40⟩),(r78,⟨67,1,41⟩),(r79,⟨67,1,40⟩)]
theorem checked9 : fastCheckList band b9=true := by decide +kernel

def b10 : List (Rectangle × FastWitness) := [(r80,⟨67,1,40⟩),(r81,⟨67,1,40⟩),(r82,⟨67,1,40⟩),(r83,⟨67,1,40⟩),(r84,⟨67,1,40⟩),(r85,⟨67,1,40⟩),(r86,⟨67,1,40⟩),(r87,⟨67,1,40⟩)]
theorem checked10 : fastCheckList band b10=true := by decide +kernel

def b11 : List (Rectangle × FastWitness) := [(r88,⟨67,1,40⟩),(r89,⟨67,1,40⟩),(r90,⟨67,1,40⟩),(r91,⟨67,1,40⟩),(r92,⟨67,1,40⟩),(r93,⟨67,1,40⟩),(r94,⟨67,1,40⟩),(r95,⟨67,1,40⟩)]
theorem checked11 : fastCheckList band b11=true := by decide +kernel

def b12 : List (Rectangle × FastWitness) := [(r96,⟨67,1,40⟩),(r97,⟨67,1,40⟩),(r98,⟨67,1,40⟩),(r99,⟨67,1,40⟩),(r100,⟨67,1,40⟩),(r101,⟨67,1,40⟩),(r102,⟨67,1,40⟩),(r103,⟨67,1,41⟩)]
theorem checked12 : fastCheckList band b12=true := by decide +kernel

def b13 : List (Rectangle × FastWitness) := [(r104,⟨67,1,40⟩),(r105,⟨67,1,40⟩),(r106,⟨67,1,40⟩),(r107,⟨67,1,40⟩),(r108,⟨67,1,40⟩),(r109,⟨67,1,40⟩),(r110,⟨67,1,40⟩),(r111,⟨67,1,40⟩)]
theorem checked13 : fastCheckList band b13=true := by decide +kernel

def b14 : List (Rectangle × FastWitness) := [(r112,⟨67,1,40⟩),(r113,⟨67,1,40⟩),(r114,⟨67,1,40⟩),(r115,⟨67,1,40⟩),(r116,⟨67,1,40⟩),(r117,⟨67,1,40⟩),(r118,⟨67,1,40⟩),(r119,⟨67,1,40⟩)]
theorem checked14 : fastCheckList band b14=true := by decide +kernel

def b15 : List (Rectangle × FastWitness) := [(r120,⟨67,1,40⟩),(r121,⟨67,1,54⟩),(r122,⟨67,1,54⟩),(r123,⟨67,1,53⟩),(r124,⟨67,1,52⟩),(r125,⟨67,1,50⟩),(r126,⟨67,1,52⟩),(r127,⟨67,1,51⟩)]
theorem checked15 : fastCheckList band b15=true := by decide +kernel

def b16 : List (Rectangle × FastWitness) := [(r128,⟨67,1,51⟩),(r129,⟨67,1,52⟩),(r130,⟨67,1,51⟩),(r131,⟨67,1,51⟩),(r132,⟨67,1,50⟩),(r133,⟨67,1,50⟩),(r134,⟨67,1,51⟩),(r135,⟨67,1,50⟩)]
theorem checked16 : fastCheckList band b16=true := by decide +kernel

def b17 : List (Rectangle × FastWitness) := [(r136,⟨67,1,50⟩),(r137,⟨67,1,50⟩),(r138,⟨67,1,50⟩),(r139,⟨67,1,50⟩),(r140,⟨67,1,50⟩),(r141,⟨67,1,50⟩),(r142,⟨67,40,40⟩),(r143,⟨67,40,40⟩)]
theorem checked17 : fastCheckList band b17=true := by decide +kernel

def b18 : List (Rectangle × FastWitness) := [(r144,⟨67,40,40⟩),(r145,⟨67,40,40⟩),(r146,⟨67,40,40⟩),(r147,⟨67,40,40⟩),(r148,⟨67,40,40⟩),(r149,⟨67,40,40⟩),(r150,⟨67,40,40⟩),(r151,⟨67,40,40⟩)]
theorem checked18 : fastCheckList band b18=true := by decide +kernel

def b19 : List (Rectangle × FastWitness) := [(r152,⟨67,40,40⟩),(r153,⟨67,40,40⟩),(r154,⟨67,40,40⟩),(r155,⟨67,40,40⟩),(r156,⟨67,40,40⟩),(r157,⟨67,40,40⟩),(r158,⟨67,40,40⟩),(r159,⟨67,40,40⟩)]
theorem checked19 : fastCheckList band b19=true := by decide +kernel

def b20 : List (Rectangle × FastWitness) := [(r160,⟨67,40,40⟩),(r161,⟨67,40,40⟩),(r162,⟨67,40,40⟩),(r163,⟨67,40,40⟩),(r164,⟨67,40,40⟩),(r165,⟨67,40,40⟩),(r166,⟨67,40,40⟩),(r167,⟨67,40,40⟩)]
theorem checked20 : fastCheckList band b20=true := by decide +kernel

def b21 : List (Rectangle × FastWitness) := [(r168,⟨67,40,40⟩),(r169,⟨67,40,40⟩),(r170,⟨67,40,40⟩),(r171,⟨67,40,40⟩),(r172,⟨67,40,40⟩),(r173,⟨67,40,40⟩),(r174,⟨67,40,40⟩),(r175,⟨67,40,40⟩)]
theorem checked21 : fastCheckList band b21=true := by decide +kernel

def b22 : List (Rectangle × FastWitness) := [(r176,⟨67,40,40⟩),(r177,⟨67,40,40⟩),(r178,⟨67,40,40⟩),(r179,⟨67,40,40⟩),(r180,⟨67,40,40⟩),(r181,⟨67,40,40⟩),(r182,⟨67,40,40⟩),(r183,⟨67,40,40⟩)]
theorem checked22 : fastCheckList band b22=true := by decide +kernel

def b23 : List (Rectangle × FastWitness) := [(r184,⟨67,40,40⟩),(r185,⟨67,40,40⟩),(r186,⟨67,40,40⟩),(r187,⟨67,40,40⟩),(r188,⟨67,40,40⟩),(r189,⟨67,40,40⟩),(r190,⟨67,40,40⟩),(r191,⟨67,40,40⟩)]
theorem checked23 : fastCheckList band b23=true := by decide +kernel

def b24 : List (Rectangle × FastWitness) := [(r192,⟨67,40,40⟩),(r193,⟨67,40,40⟩),(r194,⟨67,40,40⟩),(r195,⟨67,40,40⟩),(r196,⟨67,40,40⟩),(r197,⟨67,40,40⟩),(r198,⟨67,40,40⟩),(r199,⟨67,40,40⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def b25 : List (Rectangle × FastWitness) := [(r200,⟨67,40,40⟩),(r201,⟨67,40,40⟩),(r202,⟨67,40,40⟩),(r203,⟨67,40,40⟩),(r204,⟨67,40,40⟩),(r205,⟨67,40,40⟩),(r206,⟨67,40,40⟩),(r207,⟨67,40,40⟩)]
theorem checked25 : fastCheckList band b25=true := by decide +kernel

def b26 : List (Rectangle × FastWitness) := [(r208,⟨67,40,40⟩),(r209,⟨67,40,40⟩),(r210,⟨67,40,40⟩),(r211,⟨67,40,40⟩),(r212,⟨67,40,40⟩),(r213,⟨67,40,40⟩),(r214,⟨67,40,40⟩),(r215,⟨67,40,40⟩)]
theorem checked26 : fastCheckList band b26=true := by decide +kernel

def b27 : List (Rectangle × FastWitness) := [(r216,⟨67,40,40⟩),(r217,⟨67,40,40⟩),(r218,⟨67,40,40⟩),(r219,⟨67,40,40⟩),(r220,⟨67,40,40⟩),(r221,⟨67,40,40⟩),(r222,⟨67,40,40⟩),(r223,⟨67,40,40⟩)]
theorem checked27 : fastCheckList band b27=true := by decide +kernel

def b28 : List (Rectangle × FastWitness) := [(r224,⟨67,40,40⟩),(r225,⟨67,40,40⟩),(r226,⟨67,40,40⟩),(r227,⟨67,40,40⟩),(r228,⟨67,40,40⟩),(r229,⟨67,40,40⟩),(r230,⟨67,40,40⟩),(r231,⟨67,40,40⟩)]
theorem checked28 : fastCheckList band b28=true := by decide +kernel

def b29 : List (Rectangle × FastWitness) := [(r232,⟨67,40,40⟩),(r233,⟨67,40,40⟩),(r234,⟨67,40,40⟩),(r235,⟨67,40,40⟩),(r236,⟨67,40,40⟩),(r237,⟨67,40,40⟩),(r238,⟨67,40,40⟩),(r239,⟨67,40,40⟩)]
theorem checked29 : fastCheckList band b29=true := by decide +kernel

def b30 : List (Rectangle × FastWitness) := [(r240,⟨67,40,40⟩),(r241,⟨67,40,40⟩),(r242,⟨67,40,40⟩),(r243,⟨67,40,40⟩),(r244,⟨67,40,40⟩),(r245,⟨67,40,40⟩),(r246,⟨67,40,40⟩),(r247,⟨67,40,40⟩)]
theorem checked30 : fastCheckList band b30=true := by decide +kernel

def b31 : List (Rectangle × FastWitness) := [(r248,⟨67,40,40⟩),(r249,⟨67,40,40⟩),(r250,⟨67,40,40⟩),(r251,⟨67,40,40⟩),(r252,⟨67,40,40⟩),(r253,⟨67,40,40⟩),(r254,⟨67,40,40⟩),(r255,⟨67,40,40⟩)]
theorem checked31 : fastCheckList band b31=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


