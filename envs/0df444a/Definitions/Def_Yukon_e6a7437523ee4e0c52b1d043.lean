-- Prove2me | Definitions.Def_Yukon_e6a7437523ee4e0c52b1d043
-- name    : Yukon_e6a7437523ee4e0c52b1d043
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:03:55.419311+00:00
-- url     : https://prove2.me/theorems/73bbc8ef-bfba-41ab-9123-92995f3178e7
-- title:
--   Relative certificate source part 2/8
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
--
--   yukon-proof-operation:certificate-b58-module-Yukon_e6a7437523ee4e0c52b1d043
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjcxZTZhYTE4YzQxZDI5NWU1Yzk0YmQ2ZDZmNzZkZmNmNmM4MzA4MWZjZGI5YzQwYzVhZjVmNzMxNjQzODAwMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1OC1tb2R1bGUtWXVrb25fZTZhNzQzNzUyM2VlNGUwYzUyYjFkMDQzIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZTZhNzQzNzUyM2VlNGUwYzUyYjFkMDQzIiwidiI6Mn0]

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

def b0 : List (Rectangle × FastWitness) := [(r0,⟨70,42,42⟩),(r1,⟨70,42,42⟩),(r2,⟨70,42,42⟩),(r3,⟨70,42,42⟩),(r4,⟨70,42,42⟩),(r5,⟨70,42,42⟩),(r6,⟨70,42,42⟩),(r7,⟨70,42,42⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨70,42,42⟩),(r9,⟨70,42,42⟩),(r10,⟨70,42,42⟩),(r11,⟨70,42,42⟩),(r12,⟨70,42,42⟩),(r13,⟨70,42,42⟩),(r14,⟨70,42,42⟩),(r15,⟨70,42,42⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def b2 : List (Rectangle × FastWitness) := [(r16,⟨70,42,42⟩),(r17,⟨70,42,42⟩),(r18,⟨70,42,42⟩),(r19,⟨70,42,42⟩),(r20,⟨70,42,42⟩),(r21,⟨70,42,42⟩),(r22,⟨70,42,42⟩),(r23,⟨70,42,42⟩)]
theorem checked2 : fastCheckList band b2=true := by decide +kernel

def b3 : List (Rectangle × FastWitness) := [(r24,⟨70,42,42⟩),(r25,⟨70,42,42⟩),(r26,⟨70,42,42⟩),(r27,⟨70,42,42⟩),(r28,⟨70,42,42⟩),(r29,⟨70,42,42⟩),(r30,⟨70,42,42⟩),(r31,⟨70,42,42⟩)]
theorem checked3 : fastCheckList band b3=true := by decide +kernel

def b4 : List (Rectangle × FastWitness) := [(r32,⟨70,42,42⟩),(r33,⟨70,42,42⟩),(r34,⟨70,42,42⟩),(r35,⟨70,42,42⟩),(r36,⟨70,42,42⟩),(r37,⟨70,42,42⟩),(r38,⟨70,42,42⟩),(r39,⟨70,42,42⟩)]
theorem checked4 : fastCheckList band b4=true := by decide +kernel

def b5 : List (Rectangle × FastWitness) := [(r40,⟨70,42,42⟩),(r41,⟨70,42,42⟩),(r42,⟨70,42,42⟩),(r43,⟨70,42,42⟩),(r44,⟨70,42,42⟩),(r45,⟨70,42,42⟩),(r46,⟨70,42,42⟩),(r47,⟨70,42,42⟩)]
theorem checked5 : fastCheckList band b5=true := by decide +kernel

def b6 : List (Rectangle × FastWitness) := [(r48,⟨70,42,42⟩),(r49,⟨70,42,42⟩),(r50,⟨70,42,42⟩),(r51,⟨70,42,42⟩),(r52,⟨70,42,42⟩),(r53,⟨70,42,42⟩),(r54,⟨70,42,42⟩),(r55,⟨70,42,42⟩)]
theorem checked6 : fastCheckList band b6=true := by decide +kernel

def b7 : List (Rectangle × FastWitness) := [(r56,⟨70,42,42⟩),(r57,⟨70,42,42⟩),(r58,⟨70,42,42⟩),(r59,⟨70,42,42⟩),(r60,⟨70,42,42⟩),(r61,⟨70,42,42⟩),(r62,⟨70,42,42⟩),(r63,⟨70,42,42⟩)]
theorem checked7 : fastCheckList band b7=true := by decide +kernel

def b8 : List (Rectangle × FastWitness) := [(r64,⟨70,42,42⟩),(r65,⟨70,42,42⟩),(r66,⟨70,42,42⟩),(r67,⟨70,42,42⟩),(r68,⟨70,42,42⟩),(r69,⟨70,42,42⟩),(r70,⟨70,42,42⟩),(r71,⟨70,42,42⟩)]
theorem checked8 : fastCheckList band b8=true := by decide +kernel

def b9 : List (Rectangle × FastWitness) := [(r72,⟨70,42,42⟩),(r73,⟨70,42,42⟩),(r74,⟨70,42,42⟩),(r75,⟨70,42,42⟩),(r76,⟨70,42,42⟩),(r77,⟨70,42,42⟩),(r78,⟨70,42,42⟩),(r79,⟨70,42,42⟩)]
theorem checked9 : fastCheckList band b9=true := by decide +kernel

def b10 : List (Rectangle × FastWitness) := [(r80,⟨70,42,42⟩),(r81,⟨70,42,42⟩),(r82,⟨70,42,42⟩),(r83,⟨70,42,42⟩),(r84,⟨70,42,42⟩),(r85,⟨70,42,42⟩),(r86,⟨70,42,42⟩),(r87,⟨70,42,42⟩)]
theorem checked10 : fastCheckList band b10=true := by decide +kernel

def b11 : List (Rectangle × FastWitness) := [(r88,⟨70,42,42⟩),(r89,⟨70,42,42⟩),(r90,⟨70,42,42⟩),(r91,⟨70,42,42⟩),(r92,⟨70,42,42⟩),(r93,⟨70,42,42⟩),(r94,⟨70,42,42⟩),(r95,⟨70,42,42⟩)]
theorem checked11 : fastCheckList band b11=true := by decide +kernel

def b12 : List (Rectangle × FastWitness) := [(r96,⟨70,42,42⟩),(r97,⟨70,42,42⟩),(r98,⟨70,42,42⟩),(r99,⟨70,42,42⟩),(r100,⟨70,42,42⟩),(r101,⟨70,42,42⟩),(r102,⟨70,42,42⟩),(r103,⟨70,42,42⟩)]
theorem checked12 : fastCheckList band b12=true := by decide +kernel

def b13 : List (Rectangle × FastWitness) := [(r104,⟨70,42,42⟩),(r105,⟨70,42,42⟩),(r106,⟨70,42,42⟩),(r107,⟨70,42,42⟩),(r108,⟨70,42,42⟩),(r109,⟨70,42,42⟩),(r110,⟨70,42,42⟩),(r111,⟨70,42,42⟩)]
theorem checked13 : fastCheckList band b13=true := by decide +kernel

def b14 : List (Rectangle × FastWitness) := [(r112,⟨70,42,42⟩),(r113,⟨70,42,42⟩),(r114,⟨70,42,42⟩),(r115,⟨70,42,42⟩),(r116,⟨70,42,42⟩),(r117,⟨70,42,42⟩),(r118,⟨70,42,42⟩),(r119,⟨70,42,42⟩)]
theorem checked14 : fastCheckList band b14=true := by decide +kernel

def b15 : List (Rectangle × FastWitness) := [(r120,⟨70,42,42⟩),(r121,⟨70,42,42⟩),(r122,⟨70,42,42⟩),(r123,⟨70,42,42⟩),(r124,⟨70,42,42⟩),(r125,⟨70,42,42⟩),(r126,⟨70,42,42⟩),(r127,⟨70,42,42⟩)]
theorem checked15 : fastCheckList band b15=true := by decide +kernel

def b16 : List (Rectangle × FastWitness) := [(r128,⟨70,42,42⟩),(r129,⟨70,42,42⟩),(r130,⟨70,42,42⟩),(r131,⟨70,42,42⟩),(r132,⟨70,42,42⟩),(r133,⟨70,42,42⟩),(r134,⟨70,42,42⟩),(r135,⟨70,42,42⟩)]
theorem checked16 : fastCheckList band b16=true := by decide +kernel

def b17 : List (Rectangle × FastWitness) := [(r136,⟨70,42,42⟩),(r137,⟨70,42,42⟩),(r138,⟨70,42,42⟩),(r139,⟨70,42,42⟩),(r140,⟨70,42,42⟩),(r141,⟨70,42,42⟩),(r142,⟨70,42,42⟩),(r143,⟨70,42,42⟩)]
theorem checked17 : fastCheckList band b17=true := by decide +kernel

def b18 : List (Rectangle × FastWitness) := [(r144,⟨70,42,42⟩),(r145,⟨70,42,42⟩),(r146,⟨70,42,42⟩),(r147,⟨70,42,42⟩),(r148,⟨70,42,42⟩),(r149,⟨70,42,42⟩),(r150,⟨70,42,42⟩),(r151,⟨70,42,42⟩)]
theorem checked18 : fastCheckList band b18=true := by decide +kernel

def b19 : List (Rectangle × FastWitness) := [(r152,⟨70,42,42⟩),(r153,⟨70,42,42⟩),(r154,⟨70,42,42⟩),(r155,⟨70,42,42⟩),(r156,⟨70,42,42⟩),(r157,⟨70,42,42⟩),(r158,⟨70,42,42⟩),(r159,⟨70,42,42⟩)]
theorem checked19 : fastCheckList band b19=true := by decide +kernel

def b20 : List (Rectangle × FastWitness) := [(r160,⟨70,42,42⟩),(r161,⟨70,42,42⟩),(r162,⟨70,42,42⟩),(r163,⟨70,42,42⟩),(r164,⟨70,42,42⟩),(r165,⟨70,42,42⟩),(r166,⟨70,42,42⟩),(r167,⟨70,42,42⟩)]
theorem checked20 : fastCheckList band b20=true := by decide +kernel

def b21 : List (Rectangle × FastWitness) := [(r168,⟨70,42,42⟩),(r169,⟨70,42,42⟩),(r170,⟨70,42,42⟩),(r171,⟨70,42,42⟩),(r172,⟨70,42,42⟩),(r173,⟨70,42,42⟩),(r174,⟨70,42,42⟩),(r175,⟨70,42,42⟩)]
theorem checked21 : fastCheckList band b21=true := by decide +kernel

def b22 : List (Rectangle × FastWitness) := [(r176,⟨70,42,42⟩),(r177,⟨70,42,42⟩),(r178,⟨70,42,42⟩),(r179,⟨70,42,42⟩),(r180,⟨70,42,42⟩),(r181,⟨70,42,42⟩),(r182,⟨70,42,42⟩),(r183,⟨70,42,42⟩)]
theorem checked22 : fastCheckList band b22=true := by decide +kernel

def b23 : List (Rectangle × FastWitness) := [(r184,⟨70,42,42⟩),(r185,⟨70,42,42⟩),(r186,⟨70,42,42⟩),(r187,⟨70,42,42⟩),(r188,⟨70,42,42⟩),(r189,⟨70,42,42⟩),(r190,⟨70,42,42⟩),(r191,⟨70,42,42⟩)]
theorem checked23 : fastCheckList band b23=true := by decide +kernel

def b24 : List (Rectangle × FastWitness) := [(r192,⟨70,42,42⟩),(r193,⟨70,42,42⟩),(r194,⟨70,42,42⟩),(r195,⟨70,42,42⟩),(r196,⟨70,42,42⟩),(r197,⟨70,42,42⟩),(r198,⟨70,42,42⟩),(r199,⟨70,42,42⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def b25 : List (Rectangle × FastWitness) := [(r200,⟨70,42,42⟩),(r201,⟨70,42,42⟩),(r202,⟨70,42,42⟩),(r203,⟨70,42,42⟩),(r204,⟨70,42,42⟩),(r205,⟨70,42,42⟩),(r206,⟨70,42,42⟩),(r207,⟨70,42,42⟩)]
theorem checked25 : fastCheckList band b25=true := by decide +kernel

def b26 : List (Rectangle × FastWitness) := [(r208,⟨70,42,42⟩),(r209,⟨70,42,42⟩),(r210,⟨70,42,42⟩),(r211,⟨70,42,42⟩),(r212,⟨70,42,42⟩),(r213,⟨70,42,42⟩),(r214,⟨70,42,42⟩),(r215,⟨70,42,42⟩)]
theorem checked26 : fastCheckList band b26=true := by decide +kernel

def b27 : List (Rectangle × FastWitness) := [(r216,⟨70,42,42⟩),(r217,⟨70,42,42⟩),(r218,⟨70,42,42⟩),(r219,⟨70,42,42⟩),(r220,⟨70,42,42⟩),(r221,⟨70,42,42⟩),(r222,⟨70,42,42⟩),(r223,⟨70,42,42⟩)]
theorem checked27 : fastCheckList band b27=true := by decide +kernel

def b28 : List (Rectangle × FastWitness) := [(r224,⟨70,42,42⟩),(r225,⟨70,42,42⟩),(r226,⟨70,42,42⟩),(r227,⟨70,42,42⟩),(r228,⟨70,42,42⟩),(r229,⟨70,42,42⟩),(r230,⟨70,42,42⟩),(r231,⟨70,42,42⟩)]
theorem checked28 : fastCheckList band b28=true := by decide +kernel

def b29 : List (Rectangle × FastWitness) := [(r232,⟨70,42,42⟩),(r233,⟨70,42,42⟩),(r234,⟨70,42,42⟩),(r235,⟨70,42,42⟩),(r236,⟨70,42,42⟩),(r237,⟨70,42,42⟩),(r238,⟨70,42,42⟩),(r239,⟨70,42,42⟩)]
theorem checked29 : fastCheckList band b29=true := by decide +kernel

def b30 : List (Rectangle × FastWitness) := [(r240,⟨70,42,42⟩),(r241,⟨70,42,42⟩),(r242,⟨70,42,42⟩),(r243,⟨70,42,42⟩),(r244,⟨70,42,42⟩),(r245,⟨70,42,42⟩),(r246,⟨70,42,42⟩),(r247,⟨70,42,42⟩)]
theorem checked30 : fastCheckList band b30=true := by decide +kernel

def b31 : List (Rectangle × FastWitness) := [(r248,⟨70,42,42⟩),(r249,⟨70,42,42⟩),(r250,⟨70,42,42⟩),(r251,⟨70,42,42⟩),(r252,⟨70,42,42⟩),(r253,⟨70,42,42⟩),(r254,⟨70,42,42⟩),(r255,⟨70,42,42⟩)]
theorem checked31 : fastCheckList band b31=true := by decide +kernel

def b32 : List (Rectangle × FastWitness) := [(r256,⟨70,42,42⟩),(r257,⟨70,42,42⟩),(r258,⟨70,42,42⟩),(r259,⟨70,42,42⟩),(r260,⟨70,42,42⟩),(r261,⟨70,42,42⟩),(r262,⟨70,42,42⟩),(r263,⟨70,42,42⟩)]
theorem checked32 : fastCheckList band b32=true := by decide +kernel

def b33 : List (Rectangle × FastWitness) := [(r264,⟨70,42,42⟩),(r265,⟨70,42,42⟩),(r266,⟨70,42,42⟩),(r267,⟨70,42,42⟩),(r268,⟨70,42,42⟩),(r269,⟨70,42,42⟩),(r270,⟨70,42,42⟩),(r271,⟨70,42,42⟩)]
theorem checked33 : fastCheckList band b33=true := by decide +kernel

def b34 : List (Rectangle × FastWitness) := [(r272,⟨70,42,42⟩),(r273,⟨70,42,42⟩),(r274,⟨70,42,42⟩),(r275,⟨70,42,42⟩),(r276,⟨70,42,42⟩),(r277,⟨70,42,42⟩),(r278,⟨70,42,42⟩),(r279,⟨70,42,42⟩)]
theorem checked34 : fastCheckList band b34=true := by decide +kernel

def b35 : List (Rectangle × FastWitness) := [(r280,⟨70,42,42⟩),(r281,⟨70,42,42⟩),(r282,⟨70,42,42⟩),(r283,⟨70,42,42⟩),(r284,⟨70,42,42⟩),(r285,⟨70,42,42⟩),(r286,⟨70,42,42⟩),(r287,⟨70,42,42⟩)]
theorem checked35 : fastCheckList band b35=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast


