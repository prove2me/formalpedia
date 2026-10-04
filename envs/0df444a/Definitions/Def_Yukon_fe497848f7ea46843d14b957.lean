-- Prove2me | Definitions.Def_Yukon_fe497848f7ea46843d14b957
-- name    : Yukon_fe497848f7ea46843d14b957
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:42:59.122231+00:00
-- url     : https://prove2.me/theorems/64e49abb-0404-4e9d-aa77-1c06e3072c1f
-- title:
--   Relative certificate source part 5/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_fe497848f7ea46843d14b957
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjk5Y2UwNDQ2ZjAxNzg0YjAzYjdhZGFlNDU1ZjRkOTljOWZjZjY5YmY5ZDJiZDgxZTE4YTEyMDJhOGJiMmIwYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2ZlNDk3ODQ4ZjdlYTQ2ODQzZDE0Yjk1NyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2ZlNDk3ODQ4ZjdlYTQ2ODQzZDE0Yjk1NyIsInYiOjJ9]

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

def b96 : List (Rectangle × FastWitness) := [(r768,⟨67,40,40⟩),(r769,⟨67,40,40⟩),(r770,⟨67,40,40⟩),(r771,⟨67,40,40⟩),(r772,⟨67,40,40⟩),(r773,⟨67,40,40⟩),(r774,⟨67,40,40⟩),(r775,⟨67,40,40⟩)]
theorem checked96 : fastCheckList band b96=true := by decide +kernel

def b97 : List (Rectangle × FastWitness) := [(r776,⟨67,40,40⟩),(r777,⟨67,40,40⟩),(r778,⟨67,40,40⟩),(r779,⟨67,40,40⟩),(r780,⟨67,40,40⟩),(r781,⟨67,40,40⟩),(r782,⟨67,40,40⟩),(r783,⟨67,40,40⟩)]
theorem checked97 : fastCheckList band b97=true := by decide +kernel

def b98 : List (Rectangle × FastWitness) := [(r784,⟨67,40,40⟩),(r785,⟨67,40,40⟩),(r786,⟨67,40,40⟩),(r787,⟨67,40,40⟩),(r788,⟨67,40,40⟩),(r789,⟨67,40,40⟩),(r790,⟨67,40,40⟩),(r791,⟨67,40,40⟩)]
theorem checked98 : fastCheckList band b98=true := by decide +kernel

def b99 : List (Rectangle × FastWitness) := [(r792,⟨67,40,40⟩),(r793,⟨67,40,40⟩),(r794,⟨67,40,40⟩),(r795,⟨67,40,40⟩),(r796,⟨67,40,40⟩),(r797,⟨67,40,40⟩),(r798,⟨67,40,40⟩),(r799,⟨67,40,40⟩)]
theorem checked99 : fastCheckList band b99=true := by decide +kernel

def b100 : List (Rectangle × FastWitness) := [(r800,⟨67,40,40⟩),(r801,⟨67,40,40⟩),(r802,⟨67,40,40⟩),(r803,⟨67,40,40⟩),(r804,⟨67,40,40⟩),(r805,⟨67,40,40⟩),(r806,⟨67,40,40⟩),(r807,⟨67,40,40⟩)]
theorem checked100 : fastCheckList band b100=true := by decide +kernel

def b101 : List (Rectangle × FastWitness) := [(r808,⟨67,40,40⟩),(r809,⟨67,40,40⟩),(r810,⟨67,40,40⟩),(r811,⟨67,40,40⟩),(r812,⟨67,40,40⟩),(r813,⟨67,40,40⟩),(r814,⟨67,40,40⟩),(r815,⟨67,40,40⟩)]
theorem checked101 : fastCheckList band b101=true := by decide +kernel

def b102 : List (Rectangle × FastWitness) := [(r816,⟨67,40,40⟩),(r817,⟨67,40,40⟩),(r818,⟨67,40,40⟩),(r819,⟨67,40,40⟩),(r820,⟨67,40,40⟩),(r821,⟨67,40,40⟩),(r822,⟨67,40,40⟩),(r823,⟨67,40,40⟩)]
theorem checked102 : fastCheckList band b102=true := by decide +kernel

def b103 : List (Rectangle × FastWitness) := [(r824,⟨67,40,40⟩),(r825,⟨67,40,40⟩),(r826,⟨67,40,40⟩),(r827,⟨67,40,40⟩),(r828,⟨67,40,40⟩),(r829,⟨67,40,40⟩),(r830,⟨67,40,40⟩),(r831,⟨67,40,40⟩)]
theorem checked103 : fastCheckList band b103=true := by decide +kernel

def b104 : List (Rectangle × FastWitness) := [(r832,⟨67,40,40⟩),(r833,⟨67,40,40⟩),(r834,⟨67,40,40⟩),(r835,⟨67,40,40⟩),(r836,⟨67,40,40⟩),(r837,⟨67,40,40⟩),(r838,⟨67,40,40⟩),(r839,⟨67,40,40⟩)]
theorem checked104 : fastCheckList band b104=true := by decide +kernel

def b105 : List (Rectangle × FastWitness) := [(r840,⟨67,40,40⟩),(r841,⟨67,40,40⟩),(r842,⟨67,40,40⟩),(r843,⟨67,40,40⟩),(r844,⟨67,40,40⟩),(r845,⟨67,40,40⟩),(r846,⟨67,40,40⟩),(r847,⟨67,40,40⟩)]
theorem checked105 : fastCheckList band b105=true := by decide +kernel

def b106 : List (Rectangle × FastWitness) := [(r848,⟨67,40,40⟩),(r849,⟨67,40,40⟩),(r850,⟨67,40,40⟩),(r851,⟨67,40,40⟩),(r852,⟨67,40,40⟩),(r853,⟨67,40,40⟩),(r854,⟨67,40,40⟩),(r855,⟨67,40,40⟩)]
theorem checked106 : fastCheckList band b106=true := by decide +kernel

def b107 : List (Rectangle × FastWitness) := [(r856,⟨67,40,40⟩),(r857,⟨67,40,40⟩),(r858,⟨67,40,40⟩),(r859,⟨67,40,40⟩),(r860,⟨67,40,40⟩),(r861,⟨67,40,40⟩),(r862,⟨67,40,40⟩),(r863,⟨67,40,40⟩)]
theorem checked107 : fastCheckList band b107=true := by decide +kernel

def b108 : List (Rectangle × FastWitness) := [(r864,⟨67,40,40⟩),(r865,⟨67,40,40⟩),(r866,⟨67,40,40⟩),(r867,⟨67,40,40⟩),(r868,⟨67,40,40⟩),(r869,⟨67,40,40⟩),(r870,⟨67,40,40⟩),(r871,⟨67,40,40⟩)]
theorem checked108 : fastCheckList band b108=true := by decide +kernel

def b109 : List (Rectangle × FastWitness) := [(r872,⟨67,40,40⟩),(r873,⟨67,40,40⟩),(r874,⟨67,40,40⟩),(r875,⟨67,40,40⟩),(r876,⟨67,40,40⟩),(r877,⟨67,40,40⟩),(r878,⟨67,40,40⟩),(r879,⟨67,40,40⟩)]
theorem checked109 : fastCheckList band b109=true := by decide +kernel

def b110 : List (Rectangle × FastWitness) := [(r880,⟨67,40,40⟩),(r881,⟨67,40,40⟩),(r882,⟨67,40,40⟩),(r883,⟨67,40,40⟩),(r884,⟨67,40,40⟩),(r885,⟨67,40,40⟩),(r886,⟨67,40,40⟩),(r887,⟨67,40,40⟩)]
theorem checked110 : fastCheckList band b110=true := by decide +kernel

def b111 : List (Rectangle × FastWitness) := [(r888,⟨67,40,40⟩),(r889,⟨67,40,40⟩),(r890,⟨67,40,40⟩),(r891,⟨67,40,40⟩),(r892,⟨67,40,40⟩),(r893,⟨67,40,40⟩),(r894,⟨67,40,40⟩),(r895,⟨67,40,40⟩)]
theorem checked111 : fastCheckList band b111=true := by decide +kernel

def b112 : List (Rectangle × FastWitness) := [(r896,⟨67,40,40⟩),(r897,⟨67,40,40⟩),(r898,⟨67,40,40⟩),(r899,⟨67,40,40⟩),(r900,⟨67,40,40⟩),(r901,⟨67,40,40⟩),(r902,⟨67,40,40⟩),(r903,⟨67,40,40⟩)]
theorem checked112 : fastCheckList band b112=true := by decide +kernel

def b113 : List (Rectangle × FastWitness) := [(r904,⟨67,40,40⟩),(r905,⟨67,40,40⟩),(r906,⟨67,40,40⟩),(r907,⟨67,40,40⟩),(r908,⟨67,40,40⟩),(r909,⟨67,40,40⟩),(r910,⟨67,40,40⟩),(r911,⟨67,40,40⟩)]
theorem checked113 : fastCheckList band b113=true := by decide +kernel

def b114 : List (Rectangle × FastWitness) := [(r912,⟨67,40,40⟩),(r913,⟨67,40,40⟩),(r914,⟨67,40,40⟩),(r915,⟨67,40,40⟩),(r916,⟨67,40,40⟩),(r917,⟨67,40,40⟩),(r918,⟨67,40,40⟩),(r919,⟨67,40,40⟩)]
theorem checked114 : fastCheckList band b114=true := by decide +kernel

def b115 : List (Rectangle × FastWitness) := [(r920,⟨67,40,40⟩),(r921,⟨67,40,40⟩),(r922,⟨67,40,40⟩),(r923,⟨67,40,40⟩),(r924,⟨67,40,40⟩),(r925,⟨67,40,40⟩),(r926,⟨67,40,40⟩),(r927,⟨67,40,40⟩)]
theorem checked115 : fastCheckList band b115=true := by decide +kernel

def b116 : List (Rectangle × FastWitness) := [(r928,⟨67,40,40⟩),(r929,⟨67,40,40⟩),(r930,⟨67,40,40⟩),(r931,⟨67,40,40⟩),(r932,⟨67,40,40⟩),(r933,⟨67,40,40⟩),(r934,⟨67,40,40⟩),(r935,⟨67,40,40⟩)]
theorem checked116 : fastCheckList band b116=true := by decide +kernel

def b117 : List (Rectangle × FastWitness) := [(r936,⟨67,40,40⟩),(r937,⟨67,40,40⟩),(r938,⟨67,40,40⟩),(r939,⟨67,40,40⟩),(r940,⟨67,40,40⟩),(r941,⟨67,40,40⟩),(r942,⟨67,40,40⟩),(r943,⟨67,40,40⟩)]
theorem checked117 : fastCheckList band b117=true := by decide +kernel

def b118 : List (Rectangle × FastWitness) := [(r944,⟨67,40,40⟩),(r945,⟨67,40,40⟩),(r946,⟨67,40,40⟩),(r947,⟨67,40,40⟩),(r948,⟨67,40,40⟩),(r949,⟨67,40,40⟩),(r950,⟨67,40,40⟩),(r951,⟨67,40,40⟩)]
theorem checked118 : fastCheckList band b118=true := by decide +kernel

def b119 : List (Rectangle × FastWitness) := [(r952,⟨67,40,40⟩),(r953,⟨67,40,40⟩),(r954,⟨67,40,40⟩),(r955,⟨67,40,40⟩),(r956,⟨67,40,40⟩),(r957,⟨67,40,40⟩),(r958,⟨67,40,40⟩),(r959,⟨67,40,40⟩)]
theorem checked119 : fastCheckList band b119=true := by decide +kernel

def b120 : List (Rectangle × FastWitness) := [(r960,⟨67,40,41⟩),(r961,⟨67,40,40⟩),(r962,⟨67,40,40⟩),(r963,⟨67,40,40⟩),(r964,⟨67,40,40⟩),(r965,⟨67,40,40⟩),(r966,⟨67,40,40⟩),(r967,⟨67,40,40⟩)]
theorem checked120 : fastCheckList band b120=true := by decide +kernel

def b121 : List (Rectangle × FastWitness) := [(r968,⟨67,40,40⟩),(r969,⟨67,40,40⟩),(r970,⟨67,40,40⟩),(r971,⟨67,40,40⟩),(r972,⟨67,40,40⟩),(r973,⟨67,40,40⟩),(r974,⟨67,40,40⟩),(r975,⟨67,40,40⟩)]
theorem checked121 : fastCheckList band b121=true := by decide +kernel

def b122 : List (Rectangle × FastWitness) := [(r976,⟨67,40,40⟩),(r977,⟨67,40,40⟩),(r978,⟨67,40,40⟩),(r979,⟨67,40,40⟩),(r980,⟨67,40,40⟩),(r981,⟨67,40,40⟩),(r982,⟨67,40,40⟩),(r983,⟨67,40,40⟩)]
theorem checked122 : fastCheckList band b122=true := by decide +kernel

def b123 : List (Rectangle × FastWitness) := [(r984,⟨67,40,40⟩),(r985,⟨67,40,40⟩),(r986,⟨67,40,40⟩),(r987,⟨67,40,40⟩),(r988,⟨67,40,40⟩),(r989,⟨67,40,40⟩),(r990,⟨67,40,40⟩),(r991,⟨67,40,40⟩)]
theorem checked123 : fastCheckList band b123=true := by decide +kernel

def b124 : List (Rectangle × FastWitness) := [(r992,⟨67,40,40⟩),(r993,⟨67,40,40⟩),(r994,⟨67,40,40⟩),(r995,⟨67,40,40⟩),(r996,⟨67,40,40⟩),(r997,⟨67,40,40⟩),(r998,⟨67,40,40⟩),(r999,⟨67,40,40⟩)]
theorem checked124 : fastCheckList band b124=true := by decide +kernel

def b125 : List (Rectangle × FastWitness) := [(r1000,⟨67,40,40⟩),(r1001,⟨67,40,40⟩),(r1002,⟨67,40,40⟩),(r1003,⟨67,40,40⟩),(r1004,⟨67,40,40⟩),(r1005,⟨67,40,40⟩),(r1006,⟨67,40,40⟩),(r1007,⟨67,40,40⟩)]
theorem checked125 : fastCheckList band b125=true := by decide +kernel

def b126 : List (Rectangle × FastWitness) := [(r1008,⟨67,40,40⟩),(r1009,⟨67,40,40⟩),(r1010,⟨67,40,40⟩),(r1011,⟨67,40,40⟩),(r1012,⟨67,40,40⟩),(r1013,⟨67,40,40⟩),(r1014,⟨67,40,40⟩),(r1015,⟨67,40,40⟩)]
theorem checked126 : fastCheckList band b126=true := by decide +kernel

def b127 : List (Rectangle × FastWitness) := [(r1016,⟨67,40,40⟩),(r1017,⟨67,40,40⟩),(r1018,⟨67,40,40⟩),(r1019,⟨67,40,40⟩),(r1020,⟨67,40,40⟩),(r1021,⟨67,40,40⟩),(r1022,⟨67,40,40⟩),(r1023,⟨67,40,40⟩)]
theorem checked127 : fastCheckList band b127=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


