-- Prove2me | Definitions.Def_Yukon_df96a6af7fa1e83b4131180f
-- name    : Yukon_df96a6af7fa1e83b4131180f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:38:15.815257+00:00
-- url     : https://prove2.me/theorems/01d96eac-ed33-4a8b-910c-723b5050f9e8
-- title:
--   Relative certificate source part 5/6
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
--
--   yukon-proof-operation:certificate-b56-ef41804a8ad6992799fbddef991c68662b54e9878152f11b0e83f91e033e9950
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTIyMGM1OWVlOTE5NzM5YjljMzNhNWYwNWU4MmFmMjM3YWFiMTIxYmJiZGIwYjQ4YmNjYTQwMzg4MzNjODQ4MiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni1lZjQxODA0YThhZDY5OTI3OTlmYmRkZWY5OTFjNjg2NjJiNTRlOTg3ODE1MmYxMWIwZTgzZjkxZTAzM2U5OTUwIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZGY5NmE2YWY3ZmExZTgzYjQxMzExODBmIiwidiI6Mn0]

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

def b105 : List (Rectangle × FastWitness) := [(r840,⟨68,46,46⟩),(r841,⟨68,46,46⟩),(r842,⟨68,46,46⟩),(r843,⟨68,46,46⟩),(r844,⟨68,46,46⟩),(r845,⟨68,46,46⟩),(r846,⟨68,46,46⟩),(r847,⟨68,46,46⟩)]
theorem checked105 : fastCheckList band b105=true := by decide +kernel

def b106 : List (Rectangle × FastWitness) := [(r848,⟨68,46,46⟩),(r849,⟨68,46,46⟩),(r850,⟨68,46,46⟩),(r851,⟨68,46,46⟩),(r852,⟨68,46,46⟩),(r853,⟨68,46,46⟩),(r854,⟨68,46,46⟩),(r855,⟨68,46,46⟩)]
theorem checked106 : fastCheckList band b106=true := by decide +kernel

def b107 : List (Rectangle × FastWitness) := [(r856,⟨68,46,46⟩),(r857,⟨68,46,46⟩),(r858,⟨68,46,46⟩),(r859,⟨68,46,46⟩),(r860,⟨68,46,46⟩),(r861,⟨68,46,46⟩),(r862,⟨68,46,46⟩),(r863,⟨68,46,46⟩)]
theorem checked107 : fastCheckList band b107=true := by decide +kernel

def b108 : List (Rectangle × FastWitness) := [(r864,⟨68,46,46⟩),(r865,⟨68,46,46⟩),(r866,⟨68,46,46⟩),(r867,⟨68,46,46⟩),(r868,⟨68,46,46⟩),(r869,⟨68,46,46⟩),(r870,⟨68,46,46⟩),(r871,⟨68,46,46⟩)]
theorem checked108 : fastCheckList band b108=true := by decide +kernel

def b109 : List (Rectangle × FastWitness) := [(r872,⟨68,46,46⟩),(r873,⟨68,46,46⟩),(r874,⟨68,46,46⟩),(r875,⟨68,46,46⟩),(r876,⟨68,46,46⟩),(r877,⟨68,46,46⟩),(r878,⟨68,46,46⟩),(r879,⟨68,46,46⟩)]
theorem checked109 : fastCheckList band b109=true := by decide +kernel

def b110 : List (Rectangle × FastWitness) := [(r880,⟨68,46,47⟩),(r881,⟨68,46,47⟩),(r882,⟨68,46,47⟩),(r883,⟨68,46,47⟩),(r884,⟨68,46,47⟩),(r885,⟨68,46,47⟩),(r886,⟨68,46,47⟩),(r887,⟨68,46,47⟩)]
theorem checked110 : fastCheckList band b110=true := by decide +kernel

def b111 : List (Rectangle × FastWitness) := [(r888,⟨68,46,47⟩),(r889,⟨68,46,47⟩),(r890,⟨68,46,47⟩),(r891,⟨68,47,47⟩),(r892,⟨68,47,47⟩),(r893,⟨68,47,47⟩),(r894,⟨68,47,47⟩),(r895,⟨68,47,47⟩)]
theorem checked111 : fastCheckList band b111=true := by decide +kernel

def b112 : List (Rectangle × FastWitness) := [(r896,⟨68,47,47⟩),(r897,⟨68,47,47⟩),(r898,⟨68,47,47⟩),(r899,⟨68,47,47⟩),(r900,⟨68,47,47⟩),(r901,⟨68,47,47⟩),(r902,⟨68,47,47⟩),(r903,⟨68,47,47⟩)]
theorem checked112 : fastCheckList band b112=true := by decide +kernel

def b113 : List (Rectangle × FastWitness) := [(r904,⟨68,47,47⟩),(r905,⟨68,47,47⟩),(r906,⟨68,47,47⟩),(r907,⟨68,47,47⟩),(r908,⟨68,47,47⟩),(r909,⟨68,47,47⟩),(r910,⟨68,47,47⟩),(r911,⟨68,47,47⟩)]
theorem checked113 : fastCheckList band b113=true := by decide +kernel

def b114 : List (Rectangle × FastWitness) := [(r912,⟨68,47,47⟩),(r913,⟨68,47,47⟩),(r914,⟨68,47,47⟩),(r915,⟨68,47,47⟩),(r916,⟨68,47,47⟩),(r917,⟨68,47,47⟩),(r918,⟨68,47,47⟩),(r919,⟨68,47,47⟩)]
theorem checked114 : fastCheckList band b114=true := by decide +kernel

def b115 : List (Rectangle × FastWitness) := [(r920,⟨68,47,47⟩),(r921,⟨68,47,47⟩),(r922,⟨68,47,47⟩),(r923,⟨68,47,47⟩),(r924,⟨68,48,49⟩),(r925,⟨68,48,49⟩),(r926,⟨68,48,49⟩),(r927,⟨68,48,49⟩)]
theorem checked115 : fastCheckList band b115=true := by decide +kernel

def b116 : List (Rectangle × FastWitness) := [(r928,⟨68,48,49⟩),(r929,⟨68,48,49⟩),(r930,⟨68,48,49⟩),(r931,⟨68,48,49⟩),(r932,⟨68,48,49⟩),(r933,⟨68,48,49⟩),(r934,⟨68,48,49⟩),(r935,⟨68,48,49⟩)]
theorem checked116 : fastCheckList band b116=true := by decide +kernel

def b117 : List (Rectangle × FastWitness) := [(r936,⟨68,48,49⟩),(r937,⟨68,49,49⟩),(r938,⟨68,49,49⟩),(r939,⟨68,49,49⟩),(r940,⟨68,49,49⟩),(r941,⟨68,49,49⟩),(r942,⟨68,49,49⟩),(r943,⟨68,49,49⟩)]
theorem checked117 : fastCheckList band b117=true := by decide +kernel

def b118 : List (Rectangle × FastWitness) := [(r944,⟨68,49,49⟩),(r945,⟨68,49,49⟩),(r946,⟨68,49,49⟩),(r947,⟨68,49,49⟩),(r948,⟨68,49,49⟩),(r949,⟨68,49,49⟩),(r950,⟨68,49,49⟩),(r951,⟨68,49,49⟩)]
theorem checked118 : fastCheckList band b118=true := by decide +kernel

def b119 : List (Rectangle × FastWitness) := [(r952,⟨68,49,49⟩),(r953,⟨68,49,49⟩),(r954,⟨68,49,49⟩),(r955,⟨68,49,49⟩),(r956,⟨68,49,49⟩),(r957,⟨68,49,49⟩),(r958,⟨68,49,49⟩),(r959,⟨68,49,49⟩)]
theorem checked119 : fastCheckList band b119=true := by decide +kernel

def b120 : List (Rectangle × FastWitness) := [(r960,⟨68,49,49⟩),(r961,⟨68,49,49⟩),(r962,⟨68,49,49⟩),(r963,⟨68,49,49⟩),(r964,⟨68,49,49⟩),(r965,⟨68,49,49⟩),(r966,⟨68,49,49⟩),(r967,⟨68,49,49⟩)]
theorem checked120 : fastCheckList band b120=true := by decide +kernel

def b121 : List (Rectangle × FastWitness) := [(r968,⟨68,49,49⟩),(r969,⟨68,49,49⟩),(r970,⟨68,49,49⟩),(r971,⟨68,49,49⟩),(r972,⟨68,49,50⟩),(r973,⟨68,49,50⟩),(r974,⟨68,49,50⟩),(r975,⟨68,50,50⟩)]
theorem checked121 : fastCheckList band b121=true := by decide +kernel

def b122 : List (Rectangle × FastWitness) := [(r976,⟨68,50,50⟩),(r977,⟨68,50,50⟩),(r978,⟨68,50,50⟩),(r979,⟨68,50,50⟩),(r980,⟨68,50,50⟩),(r981,⟨68,50,50⟩),(r982,⟨68,50,50⟩),(r983,⟨68,50,50⟩)]
theorem checked122 : fastCheckList band b122=true := by decide +kernel

def b123 : List (Rectangle × FastWitness) := [(r984,⟨68,50,50⟩),(r985,⟨68,50,50⟩),(r986,⟨68,50,50⟩),(r987,⟨68,50,50⟩),(r988,⟨68,50,50⟩),(r989,⟨68,50,50⟩),(r990,⟨68,50,50⟩),(r991,⟨68,50,50⟩)]
theorem checked123 : fastCheckList band b123=true := by decide +kernel

def b124 : List (Rectangle × FastWitness) := [(r992,⟨68,50,50⟩),(r993,⟨68,50,50⟩),(r994,⟨68,50,50⟩),(r995,⟨68,50,50⟩),(r996,⟨68,50,50⟩),(r997,⟨68,50,50⟩),(r998,⟨68,50,50⟩),(r999,⟨68,50,50⟩)]
theorem checked124 : fastCheckList band b124=true := by decide +kernel

def b125 : List (Rectangle × FastWitness) := [(r1000,⟨68,50,50⟩),(r1001,⟨68,52,53⟩),(r1002,⟨68,52,53⟩),(r1003,⟨68,52,52⟩),(r1004,⟨68,52,52⟩),(r1005,⟨68,52,52⟩),(r1006,⟨68,52,52⟩),(r1007,⟨68,52,52⟩)]
theorem checked125 : fastCheckList band b125=true := by decide +kernel

def b126 : List (Rectangle × FastWitness) := [(r1008,⟨68,52,52⟩),(r1009,⟨68,52,53⟩),(r1010,⟨68,52,53⟩),(r1011,⟨68,52,53⟩),(r1012,⟨68,52,53⟩),(r1013,⟨68,53,53⟩),(r1014,⟨68,53,53⟩),(r1015,⟨68,53,53⟩)]
theorem checked126 : fastCheckList band b126=true := by decide +kernel

def b127 : List (Rectangle × FastWitness) := [(r1016,⟨68,53,53⟩),(r1017,⟨68,53,53⟩),(r1018,⟨68,53,53⟩),(r1019,⟨68,53,53⟩),(r1020,⟨68,53,53⟩),(r1021,⟨68,53,53⟩),(r1022,⟨68,53,53⟩),(r1023,⟨68,53,53⟩)]
theorem checked127 : fastCheckList band b127=true := by decide +kernel

def b128 : List (Rectangle × FastWitness) := [(r1024,⟨68,53,53⟩),(r1025,⟨68,53,53⟩),(r1026,⟨68,53,53⟩),(r1027,⟨68,53,53⟩),(r1028,⟨68,53,53⟩),(r1029,⟨68,53,53⟩),(r1030,⟨68,53,53⟩),(r1031,⟨68,53,54⟩)]
theorem checked128 : fastCheckList band b128=true := by decide +kernel

def b129 : List (Rectangle × FastWitness) := [(r1032,⟨68,54,54⟩),(r1033,⟨68,54,54⟩),(r1034,⟨68,54,54⟩),(r1035,⟨68,54,54⟩),(r1036,⟨68,54,54⟩),(r1037,⟨68,54,54⟩),(r1038,⟨68,54,54⟩),(r1039,⟨68,54,54⟩)]
theorem checked129 : fastCheckList band b129=true := by decide +kernel

def b130 : List (Rectangle × FastWitness) := [(r1040,⟨68,54,54⟩),(r1041,⟨68,54,54⟩),(r1042,⟨68,54,54⟩),(r1043,⟨68,54,54⟩),(r1044,⟨68,54,54⟩),(r1045,⟨68,54,54⟩),(r1046,⟨68,54,54⟩),(r1047,⟨68,54,54⟩)]
theorem checked130 : fastCheckList band b130=true := by decide +kernel

def b131 : List (Rectangle × FastWitness) := [(r1048,⟨68,54,55⟩),(r1049,⟨68,55,55⟩),(r1050,⟨68,55,55⟩),(r1051,⟨68,55,55⟩),(r1052,⟨68,58,58⟩),(r1053,⟨68,58,58⟩),(r1054,⟨68,58,58⟩),(r1055,⟨68,58,58⟩)]
theorem checked131 : fastCheckList band b131=true := by decide +kernel

def b132 : List (Rectangle × FastWitness) := [(r1056,⟨68,58,58⟩),(r1057,⟨68,58,58⟩),(r1058,⟨68,58,58⟩),(r1059,⟨68,58,58⟩),(r1060,⟨68,58,58⟩),(r1061,⟨68,58,58⟩),(r1062,⟨68,58,58⟩),(r1063,⟨68,58,58⟩)]
theorem checked132 : fastCheckList band b132=true := by decide +kernel

def b133 : List (Rectangle × FastWitness) := [(r1064,⟨68,58,58⟩),(r1065,⟨68,58,58⟩),(r1066,⟨68,58,58⟩),(r1067,⟨68,58,58⟩),(r1068,⟨68,59,59⟩),(r1069,⟨68,59,59⟩),(r1070,⟨68,59,59⟩),(r1071,⟨68,59,59⟩)]
theorem checked133 : fastCheckList band b133=true := by decide +kernel

def b134 : List (Rectangle × FastWitness) := [(r1072,⟨68,59,59⟩),(r1073,⟨68,59,59⟩),(r1074,⟨68,59,59⟩),(r1075,⟨68,59,59⟩),(r1076,⟨68,59,59⟩),(r1077,⟨68,60,60⟩),(r1078,⟨68,60,60⟩),(r1079,⟨68,60,60⟩)]
theorem checked134 : fastCheckList band b134=true := by decide +kernel

def b135 : List (Rectangle × FastWitness) := [(r1080,⟨68,60,60⟩),(r1081,⟨68,60,60⟩),(r1082,⟨68,60,60⟩),(r1083,⟨68,60,60⟩),(r1084,⟨68,60,60⟩),(r1085,⟨68,61,61⟩),(r1086,⟨68,61,61⟩),(r1087,⟨68,64,64⟩)]
theorem checked135 : fastCheckList band b135=true := by decide +kernel

def b136 : List (Rectangle × FastWitness) := [(r1088,⟨68,64,64⟩),(r1089,⟨68,64,64⟩),(r1090,⟨68,62,62⟩),(r1091,⟨68,62,62⟩),(r1092,⟨68,62,62⟩),(r1093,⟨68,62,62⟩),(r1094,⟨68,62,62⟩),(r1095,⟨68,62,62⟩)]
theorem checked136 : fastCheckList band b136=true := by decide +kernel

def b137 : List (Rectangle × FastWitness) := [(r1096,⟨68,62,62⟩),(r1097,⟨68,63,63⟩)]
theorem checked137 : fastCheckList band b137=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast


