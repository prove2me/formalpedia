-- Prove2me | Definitions.Def_Yukon_cc1c7b1db99a28de5ef11982
-- name    : Yukon_cc1c7b1db99a28de5ef11982
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:35:36.15697+00:00
-- url     : https://prove2.me/theorems/7f44ae1a-7861-4d86-a88d-bd6436258a43
-- title:
--   Relative certificate source part 1/3
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B52T3680To3840Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B52T3680To3840Fast.lean
--
--   yukon-proof-operation:certificate-b52-tail-module-Yukon_cc1c7b1db99a28de5ef11982
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiN2RkNzI5ZDdlNjI1ODViOTEyNmNkMDFmMTBjZmZhMjc1ZTJhN2M3MGI0Yjg1NDAyYjE4NmRlYTI2NWUwNGQyNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Mi10YWlsLW1vZHVsZS1ZdWtvbl9jYzFjN2IxZGI5OWEyOGRlNWVmMTE5ODIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jYzFjN2IxZGI5OWEyOGRlNWVmMTE5ODIiLCJ2IjoyfQ]

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

def b30 : List (Rectangle × FastWitness) := [(r240,⟨64,45,45⟩),(r241,⟨64,45,45⟩),(r242,⟨64,45,45⟩),(r243,⟨64,45,45⟩),(r244,⟨64,45,45⟩),(r245,⟨64,45,45⟩),(r246,⟨64,45,45⟩),(r247,⟨64,45,45⟩)]
theorem checked30 : fastCheckList band b30=true := by decide +kernel

def b31 : List (Rectangle × FastWitness) := [(r248,⟨64,45,45⟩),(r249,⟨64,45,45⟩),(r250,⟨64,45,45⟩),(r251,⟨64,45,45⟩),(r252,⟨64,45,45⟩),(r253,⟨64,45,45⟩),(r254,⟨64,45,45⟩),(r255,⟨64,45,45⟩)]
theorem checked31 : fastCheckList band b31=true := by decide +kernel

def b32 : List (Rectangle × FastWitness) := [(r256,⟨64,45,45⟩),(r257,⟨64,45,45⟩),(r258,⟨64,45,45⟩),(r259,⟨64,45,45⟩),(r260,⟨64,45,45⟩),(r261,⟨64,45,46⟩),(r262,⟨64,45,46⟩),(r263,⟨64,45,46⟩)]
theorem checked32 : fastCheckList band b32=true := by decide +kernel

def b33 : List (Rectangle × FastWitness) := [(r264,⟨64,45,46⟩),(r265,⟨64,45,46⟩),(r266,⟨64,45,46⟩),(r267,⟨64,45,46⟩),(r268,⟨64,45,46⟩),(r269,⟨64,45,46⟩),(r270,⟨64,45,46⟩),(r271,⟨64,45,46⟩)]
theorem checked33 : fastCheckList band b33=true := by decide +kernel

def b34 : List (Rectangle × FastWitness) := [(r272,⟨64,45,46⟩),(r273,⟨64,45,46⟩),(r274,⟨64,46,46⟩),(r275,⟨64,46,46⟩),(r276,⟨64,46,46⟩),(r277,⟨64,46,46⟩),(r278,⟨64,46,46⟩),(r279,⟨64,46,46⟩)]
theorem checked34 : fastCheckList band b34=true := by decide +kernel

def b35 : List (Rectangle × FastWitness) := [(r280,⟨64,46,46⟩),(r281,⟨64,46,46⟩),(r282,⟨64,46,46⟩),(r283,⟨64,46,46⟩),(r284,⟨64,46,46⟩),(r285,⟨64,46,46⟩),(r286,⟨64,46,46⟩),(r287,⟨64,46,46⟩)]
theorem checked35 : fastCheckList band b35=true := by decide +kernel

def b36 : List (Rectangle × FastWitness) := [(r288,⟨64,46,46⟩),(r289,⟨64,46,46⟩),(r290,⟨64,46,46⟩),(r291,⟨64,46,46⟩),(r292,⟨64,46,46⟩),(r293,⟨64,46,46⟩),(r294,⟨64,46,46⟩),(r295,⟨64,46,46⟩)]
theorem checked36 : fastCheckList band b36=true := by decide +kernel

def b37 : List (Rectangle × FastWitness) := [(r296,⟨64,46,46⟩),(r297,⟨64,46,46⟩),(r298,⟨64,46,46⟩),(r299,⟨64,46,46⟩),(r300,⟨64,46,46⟩),(r301,⟨64,46,46⟩),(r302,⟨64,46,46⟩),(r303,⟨64,46,46⟩)]
theorem checked37 : fastCheckList band b37=true := by decide +kernel

def b38 : List (Rectangle × FastWitness) := [(r304,⟨64,46,46⟩),(r305,⟨64,46,46⟩),(r306,⟨64,46,46⟩),(r307,⟨64,46,46⟩),(r308,⟨64,46,46⟩),(r309,⟨64,46,46⟩),(r310,⟨64,46,46⟩),(r311,⟨64,46,46⟩)]
theorem checked38 : fastCheckList band b38=true := by decide +kernel

def b39 : List (Rectangle × FastWitness) := [(r312,⟨64,46,46⟩),(r313,⟨64,46,46⟩),(r314,⟨64,46,46⟩),(r315,⟨64,46,46⟩),(r316,⟨64,46,46⟩),(r317,⟨64,48,48⟩),(r318,⟨64,48,48⟩),(r319,⟨64,48,48⟩)]
theorem checked39 : fastCheckList band b39=true := by decide +kernel

def b40 : List (Rectangle × FastWitness) := [(r320,⟨64,48,48⟩),(r321,⟨64,48,48⟩),(r322,⟨64,48,48⟩),(r323,⟨64,48,48⟩),(r324,⟨64,48,48⟩),(r325,⟨64,48,48⟩),(r326,⟨64,48,48⟩),(r327,⟨64,48,48⟩)]
theorem checked40 : fastCheckList band b40=true := by decide +kernel

def b41 : List (Rectangle × FastWitness) := [(r328,⟨64,48,48⟩),(r329,⟨64,48,48⟩),(r330,⟨64,48,48⟩),(r331,⟨64,48,48⟩),(r332,⟨64,48,48⟩),(r333,⟨64,48,48⟩),(r334,⟨64,48,48⟩),(r335,⟨64,48,48⟩)]
theorem checked41 : fastCheckList band b41=true := by decide +kernel

def b42 : List (Rectangle × FastWitness) := [(r336,⟨64,48,48⟩),(r337,⟨64,48,48⟩),(r338,⟨64,48,48⟩),(r339,⟨64,48,48⟩),(r340,⟨64,48,48⟩),(r341,⟨64,48,48⟩),(r342,⟨64,48,48⟩),(r343,⟨64,48,48⟩)]
theorem checked42 : fastCheckList band b42=true := by decide +kernel

def b43 : List (Rectangle × FastWitness) := [(r344,⟨64,48,48⟩),(r345,⟨64,48,48⟩),(r346,⟨64,48,48⟩),(r347,⟨64,48,48⟩),(r348,⟨64,48,48⟩),(r349,⟨64,48,48⟩),(r350,⟨64,48,48⟩),(r351,⟨64,48,48⟩)]
theorem checked43 : fastCheckList band b43=true := by decide +kernel

def b44 : List (Rectangle × FastWitness) := [(r352,⟨64,48,48⟩),(r353,⟨64,48,48⟩),(r354,⟨64,48,48⟩),(r355,⟨64,48,48⟩),(r356,⟨64,48,48⟩),(r357,⟨64,48,48⟩),(r358,⟨64,48,48⟩),(r359,⟨64,48,49⟩)]
theorem checked44 : fastCheckList band b44=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B52T3680To3840Fast


