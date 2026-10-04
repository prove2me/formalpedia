-- Prove2me | Definitions.Def_Yukon_5d0797dafa92de1f4d3d3165
-- name    : Yukon_5d0797dafa92de1f4d3d3165
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:36:48.722382+00:00
-- url     : https://prove2.me/theorems/c4289544-adb6-41a7-bd04-cf7cd750f739
-- title:
--   Relative certificate source part 2/6
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
--
--   yukon-proof-operation:certificate-b56-e11c56c15110d705fe94f2e22186cf05b6b4e58642dc90cdfe1881da976731cd
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzg2OTE4NzQ1N2MyMTM5N2Q3OGUyM2RkM2YwNGY2Yjg1YjRjZmJjZGQzNzViMmM5ZmZjOTEwOTE3NGQyYzMzZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni1lMTFjNTZjMTUxMTBkNzA1ZmU5NGYyZTIyMTg2Y2YwNWI2YjRlNTg2NDJkYzkwY2RmZTE4ODFkYTk3NjczMWNkIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNWQwNzk3ZGFmYTkyZGUxZjRkM2QzMTY1IiwidiI6Mn0]

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

def b0 : List (Rectangle × FastWitness) := [(r0,⟨68,1,42⟩),(r1,⟨68,1,41⟩),(r2,⟨68,40,57⟩),(r3,⟨68,1,42⟩),(r4,⟨68,1,42⟩),(r5,⟨68,1,42⟩),(r6,⟨68,1,42⟩),(r7,⟨68,1,42⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨68,1,42⟩),(r9,⟨68,1,43⟩),(r10,⟨68,1,42⟩),(r11,⟨68,1,42⟩),(r12,⟨68,1,43⟩),(r13,⟨68,1,43⟩),(r14,⟨68,1,43⟩),(r15,⟨68,1,42⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def b2 : List (Rectangle × FastWitness) := [(r16,⟨68,1,43⟩),(r17,⟨68,1,43⟩),(r18,⟨68,1,43⟩),(r19,⟨68,1,43⟩),(r20,⟨68,1,43⟩),(r21,⟨68,1,43⟩),(r22,⟨68,1,43⟩),(r23,⟨68,1,43⟩)]
theorem checked2 : fastCheckList band b2=true := by decide +kernel

def b3 : List (Rectangle × FastWitness) := [(r24,⟨68,1,42⟩),(r25,⟨68,1,43⟩),(r26,⟨68,1,43⟩),(r27,⟨68,1,42⟩),(r28,⟨68,1,42⟩),(r29,⟨68,1,43⟩),(r30,⟨68,1,43⟩),(r31,⟨68,1,42⟩)]
theorem checked3 : fastCheckList band b3=true := by decide +kernel

def b4 : List (Rectangle × FastWitness) := [(r32,⟨68,1,43⟩),(r33,⟨68,1,43⟩),(r34,⟨68,1,42⟩),(r35,⟨68,1,43⟩),(r36,⟨68,1,43⟩),(r37,⟨68,1,43⟩),(r38,⟨68,1,43⟩),(r39,⟨68,1,42⟩)]
theorem checked4 : fastCheckList band b4=true := by decide +kernel

def b5 : List (Rectangle × FastWitness) := [(r40,⟨68,1,43⟩),(r41,⟨68,1,43⟩),(r42,⟨68,1,43⟩),(r43,⟨68,1,43⟩),(r44,⟨68,1,43⟩),(r45,⟨68,1,42⟩),(r46,⟨68,1,43⟩),(r47,⟨68,1,42⟩)]
theorem checked5 : fastCheckList band b5=true := by decide +kernel

def b6 : List (Rectangle × FastWitness) := [(r48,⟨68,1,43⟩),(r49,⟨68,1,42⟩),(r50,⟨68,1,42⟩),(r51,⟨68,1,43⟩),(r52,⟨68,1,43⟩),(r53,⟨68,1,43⟩),(r54,⟨68,1,43⟩),(r55,⟨68,1,42⟩)]
theorem checked6 : fastCheckList band b6=true := by decide +kernel

def b7 : List (Rectangle × FastWitness) := [(r56,⟨68,1,42⟩),(r57,⟨68,1,43⟩),(r58,⟨68,1,43⟩),(r59,⟨68,1,43⟩),(r60,⟨68,1,43⟩),(r61,⟨68,1,43⟩),(r62,⟨68,1,43⟩),(r63,⟨68,1,43⟩)]
theorem checked7 : fastCheckList band b7=true := by decide +kernel

def b8 : List (Rectangle × FastWitness) := [(r64,⟨68,1,43⟩),(r65,⟨68,1,43⟩),(r66,⟨68,1,43⟩),(r67,⟨68,1,43⟩),(r68,⟨68,1,43⟩),(r69,⟨68,1,43⟩),(r70,⟨68,1,43⟩),(r71,⟨68,1,43⟩)]
theorem checked8 : fastCheckList band b8=true := by decide +kernel

def b9 : List (Rectangle × FastWitness) := [(r72,⟨68,1,43⟩),(r73,⟨68,1,43⟩),(r74,⟨68,1,43⟩),(r75,⟨68,1,43⟩),(r76,⟨68,1,43⟩),(r77,⟨68,1,43⟩),(r78,⟨68,1,43⟩),(r79,⟨68,1,42⟩)]
theorem checked9 : fastCheckList band b9=true := by decide +kernel

def b10 : List (Rectangle × FastWitness) := [(r80,⟨68,1,42⟩),(r81,⟨68,1,43⟩),(r82,⟨68,1,43⟩),(r83,⟨68,1,42⟩),(r84,⟨68,1,42⟩),(r85,⟨68,1,43⟩),(r86,⟨68,1,42⟩),(r87,⟨68,1,42⟩)]
theorem checked10 : fastCheckList band b10=true := by decide +kernel

def b11 : List (Rectangle × FastWitness) := [(r88,⟨68,1,43⟩),(r89,⟨68,1,42⟩),(r90,⟨68,1,43⟩),(r91,⟨68,1,43⟩),(r92,⟨68,1,42⟩),(r93,⟨68,1,42⟩),(r94,⟨68,42,42⟩),(r95,⟨68,42,42⟩)]
theorem checked11 : fastCheckList band b11=true := by decide +kernel

def b12 : List (Rectangle × FastWitness) := [(r96,⟨68,42,42⟩),(r97,⟨68,42,42⟩),(r98,⟨68,42,42⟩),(r99,⟨68,42,42⟩),(r100,⟨68,42,42⟩),(r101,⟨68,42,42⟩),(r102,⟨68,42,42⟩),(r103,⟨68,42,42⟩)]
theorem checked12 : fastCheckList band b12=true := by decide +kernel

def b13 : List (Rectangle × FastWitness) := [(r104,⟨68,42,42⟩),(r105,⟨68,42,42⟩),(r106,⟨68,42,42⟩),(r107,⟨68,42,42⟩),(r108,⟨68,42,42⟩),(r109,⟨68,42,42⟩),(r110,⟨68,42,42⟩),(r111,⟨68,42,42⟩)]
theorem checked13 : fastCheckList band b13=true := by decide +kernel

def b14 : List (Rectangle × FastWitness) := [(r112,⟨68,42,42⟩),(r113,⟨68,42,42⟩),(r114,⟨68,42,42⟩),(r115,⟨68,42,42⟩),(r116,⟨68,42,42⟩),(r117,⟨68,42,42⟩),(r118,⟨68,42,42⟩),(r119,⟨68,42,42⟩)]
theorem checked14 : fastCheckList band b14=true := by decide +kernel

def b15 : List (Rectangle × FastWitness) := [(r120,⟨68,42,42⟩),(r121,⟨68,42,42⟩),(r122,⟨68,42,42⟩),(r123,⟨68,42,42⟩),(r124,⟨68,42,42⟩),(r125,⟨68,42,42⟩),(r126,⟨68,42,42⟩),(r127,⟨68,42,42⟩)]
theorem checked15 : fastCheckList band b15=true := by decide +kernel

def b16 : List (Rectangle × FastWitness) := [(r128,⟨68,42,42⟩),(r129,⟨68,42,42⟩),(r130,⟨68,42,42⟩),(r131,⟨68,42,42⟩),(r132,⟨68,42,42⟩),(r133,⟨68,42,42⟩),(r134,⟨68,42,42⟩),(r135,⟨68,42,42⟩)]
theorem checked16 : fastCheckList band b16=true := by decide +kernel

def b17 : List (Rectangle × FastWitness) := [(r136,⟨68,42,42⟩),(r137,⟨68,42,42⟩),(r138,⟨68,42,42⟩),(r139,⟨68,42,42⟩),(r140,⟨68,42,42⟩),(r141,⟨68,42,42⟩),(r142,⟨68,42,42⟩),(r143,⟨68,42,42⟩)]
theorem checked17 : fastCheckList band b17=true := by decide +kernel

def b18 : List (Rectangle × FastWitness) := [(r144,⟨68,42,42⟩),(r145,⟨68,42,42⟩),(r146,⟨68,42,42⟩),(r147,⟨68,42,42⟩),(r148,⟨68,42,42⟩),(r149,⟨68,42,42⟩),(r150,⟨68,42,42⟩),(r151,⟨68,42,42⟩)]
theorem checked18 : fastCheckList band b18=true := by decide +kernel

def b19 : List (Rectangle × FastWitness) := [(r152,⟨68,42,42⟩),(r153,⟨68,42,42⟩),(r154,⟨68,42,42⟩),(r155,⟨68,42,42⟩),(r156,⟨68,42,42⟩),(r157,⟨68,42,42⟩),(r158,⟨68,42,42⟩),(r159,⟨68,42,42⟩)]
theorem checked19 : fastCheckList band b19=true := by decide +kernel

def b20 : List (Rectangle × FastWitness) := [(r160,⟨68,42,42⟩),(r161,⟨68,42,42⟩),(r162,⟨68,42,42⟩),(r163,⟨68,42,42⟩),(r164,⟨68,42,42⟩),(r165,⟨68,42,42⟩),(r166,⟨68,42,42⟩),(r167,⟨68,42,42⟩)]
theorem checked20 : fastCheckList band b20=true := by decide +kernel

def b21 : List (Rectangle × FastWitness) := [(r168,⟨68,42,42⟩),(r169,⟨68,42,42⟩),(r170,⟨68,42,42⟩),(r171,⟨68,42,42⟩),(r172,⟨68,42,42⟩),(r173,⟨68,42,42⟩),(r174,⟨68,42,42⟩),(r175,⟨68,42,42⟩)]
theorem checked21 : fastCheckList band b21=true := by decide +kernel

def b22 : List (Rectangle × FastWitness) := [(r176,⟨68,42,42⟩),(r177,⟨68,42,42⟩),(r178,⟨68,42,42⟩),(r179,⟨68,42,42⟩),(r180,⟨68,42,42⟩),(r181,⟨68,42,42⟩),(r182,⟨68,42,42⟩),(r183,⟨68,42,42⟩)]
theorem checked22 : fastCheckList band b22=true := by decide +kernel

def b23 : List (Rectangle × FastWitness) := [(r184,⟨68,42,42⟩),(r185,⟨68,42,42⟩),(r186,⟨68,42,42⟩),(r187,⟨68,42,42⟩),(r188,⟨68,42,42⟩),(r189,⟨68,42,42⟩),(r190,⟨68,42,42⟩),(r191,⟨68,42,42⟩)]
theorem checked23 : fastCheckList band b23=true := by decide +kernel

def b24 : List (Rectangle × FastWitness) := [(r192,⟨68,42,42⟩),(r193,⟨68,42,42⟩),(r194,⟨68,42,42⟩),(r195,⟨68,42,42⟩),(r196,⟨68,42,42⟩),(r197,⟨68,42,42⟩),(r198,⟨68,42,42⟩),(r199,⟨68,42,42⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def b25 : List (Rectangle × FastWitness) := [(r200,⟨68,42,42⟩),(r201,⟨68,42,42⟩),(r202,⟨68,42,42⟩),(r203,⟨68,42,42⟩),(r204,⟨68,42,42⟩),(r205,⟨68,42,42⟩),(r206,⟨68,42,42⟩),(r207,⟨68,42,42⟩)]
theorem checked25 : fastCheckList band b25=true := by decide +kernel

def b26 : List (Rectangle × FastWitness) := [(r208,⟨68,42,42⟩),(r209,⟨68,42,42⟩),(r210,⟨68,42,42⟩),(r211,⟨68,42,42⟩),(r212,⟨68,42,42⟩),(r213,⟨68,42,42⟩),(r214,⟨68,42,42⟩),(r215,⟨68,42,42⟩)]
theorem checked26 : fastCheckList band b26=true := by decide +kernel

def b27 : List (Rectangle × FastWitness) := [(r216,⟨68,42,42⟩),(r217,⟨68,42,42⟩),(r218,⟨68,42,42⟩),(r219,⟨68,42,42⟩),(r220,⟨68,42,42⟩),(r221,⟨68,42,42⟩),(r222,⟨68,42,42⟩),(r223,⟨68,42,42⟩)]
theorem checked27 : fastCheckList band b27=true := by decide +kernel

def b28 : List (Rectangle × FastWitness) := [(r224,⟨68,42,42⟩),(r225,⟨68,42,42⟩),(r226,⟨68,42,42⟩),(r227,⟨68,42,42⟩),(r228,⟨68,42,42⟩),(r229,⟨68,42,42⟩),(r230,⟨68,42,42⟩),(r231,⟨68,42,42⟩)]
theorem checked28 : fastCheckList band b28=true := by decide +kernel

def b29 : List (Rectangle × FastWitness) := [(r232,⟨68,42,42⟩),(r233,⟨68,42,42⟩),(r234,⟨68,42,42⟩),(r235,⟨68,42,42⟩),(r236,⟨68,42,42⟩),(r237,⟨68,42,42⟩),(r238,⟨68,42,42⟩),(r239,⟨68,42,42⟩)]
theorem checked29 : fastCheckList band b29=true := by decide +kernel

def b30 : List (Rectangle × FastWitness) := [(r240,⟨68,42,42⟩),(r241,⟨68,42,42⟩),(r242,⟨68,42,42⟩),(r243,⟨68,42,42⟩),(r244,⟨68,42,42⟩),(r245,⟨68,42,42⟩),(r246,⟨68,42,42⟩),(r247,⟨68,42,42⟩)]
theorem checked30 : fastCheckList band b30=true := by decide +kernel

def b31 : List (Rectangle × FastWitness) := [(r248,⟨68,42,42⟩),(r249,⟨68,42,42⟩),(r250,⟨68,42,42⟩),(r251,⟨68,42,42⟩),(r252,⟨68,42,42⟩),(r253,⟨68,42,42⟩),(r254,⟨68,42,42⟩),(r255,⟨68,42,42⟩)]
theorem checked31 : fastCheckList band b31=true := by decide +kernel

def b32 : List (Rectangle × FastWitness) := [(r256,⟨68,42,42⟩),(r257,⟨68,42,42⟩),(r258,⟨68,42,42⟩),(r259,⟨68,42,42⟩),(r260,⟨68,42,42⟩),(r261,⟨68,42,42⟩),(r262,⟨68,42,42⟩),(r263,⟨68,42,42⟩)]
theorem checked32 : fastCheckList band b32=true := by decide +kernel

def b33 : List (Rectangle × FastWitness) := [(r264,⟨68,42,42⟩),(r265,⟨68,42,42⟩),(r266,⟨68,42,42⟩),(r267,⟨68,42,42⟩),(r268,⟨68,42,42⟩),(r269,⟨68,42,42⟩),(r270,⟨68,42,42⟩),(r271,⟨68,42,42⟩)]
theorem checked33 : fastCheckList band b33=true := by decide +kernel

def b34 : List (Rectangle × FastWitness) := [(r272,⟨68,42,42⟩),(r273,⟨68,42,42⟩),(r274,⟨68,42,42⟩),(r275,⟨68,42,42⟩),(r276,⟨68,42,42⟩),(r277,⟨68,42,42⟩),(r278,⟨68,42,42⟩),(r279,⟨68,42,42⟩)]
theorem checked34 : fastCheckList band b34=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast


