-- Prove2me | Definitions.Def_Yukon_8004ff7cd4208865a812356b
-- name    : Yukon_8004ff7cd4208865a812356b
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:33:58.965566+00:00
-- url     : https://prove2.me/theorems/8b80d23a-8ab5-42c4-9ce9-d7d58e762edc
-- title:
--   Relative certificate source part 4/6
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B56T3579To3720Fast.lean
--
--   yukon-proof-operation:certificate-b56-55551e75c65fd36ac703d93e7e4de75392cd0a15f0f56e6151c123fd8e10b52b
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzhmZGY5ZGEyMmFiZGE2MWE3ZTIzY2VlMjRlYTY5MDA3Nzk1ZjQ2YjgxZDJhZDI1YTgyOGM2ZmFlMDQ5ZTQ0YSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni01NTU1MWU3NWM2NWZkMzZhYzcwM2Q5M2U3ZTRkZTc1MzkyY2QwYTE1ZjBmNTZlNjE1MWMxMjNmZDhlMTBiNTJiIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fODAwNGZmN2NkNDIwODg2NWE4MTIzNTZiIiwidiI6Mn0]

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

def b70 : List (Rectangle × FastWitness) := [(r560,⟨68,43,43⟩),(r561,⟨68,43,43⟩),(r562,⟨68,43,43⟩),(r563,⟨68,43,43⟩),(r564,⟨68,43,43⟩),(r565,⟨68,43,43⟩),(r566,⟨68,43,43⟩),(r567,⟨68,43,43⟩)]
theorem checked70 : fastCheckList band b70=true := by decide +kernel

def b71 : List (Rectangle × FastWitness) := [(r568,⟨68,43,43⟩),(r569,⟨68,43,43⟩),(r570,⟨68,43,43⟩),(r571,⟨68,43,43⟩),(r572,⟨68,43,43⟩),(r573,⟨68,43,43⟩),(r574,⟨68,43,43⟩),(r575,⟨68,43,43⟩)]
theorem checked71 : fastCheckList band b71=true := by decide +kernel

def b72 : List (Rectangle × FastWitness) := [(r576,⟨68,43,43⟩),(r577,⟨68,43,43⟩),(r578,⟨68,43,43⟩),(r579,⟨68,43,43⟩),(r580,⟨68,43,43⟩),(r581,⟨68,43,43⟩),(r582,⟨68,43,43⟩),(r583,⟨68,43,43⟩)]
theorem checked72 : fastCheckList band b72=true := by decide +kernel

def b73 : List (Rectangle × FastWitness) := [(r584,⟨68,43,43⟩),(r585,⟨68,43,43⟩),(r586,⟨68,43,43⟩),(r587,⟨68,43,43⟩),(r588,⟨68,43,43⟩),(r589,⟨68,43,43⟩),(r590,⟨68,43,43⟩),(r591,⟨68,43,43⟩)]
theorem checked73 : fastCheckList band b73=true := by decide +kernel

def b74 : List (Rectangle × FastWitness) := [(r592,⟨68,43,43⟩),(r593,⟨68,43,43⟩),(r594,⟨68,43,43⟩),(r595,⟨68,43,43⟩),(r596,⟨68,43,43⟩),(r597,⟨68,43,43⟩),(r598,⟨68,43,43⟩),(r599,⟨68,43,43⟩)]
theorem checked74 : fastCheckList band b74=true := by decide +kernel

def b75 : List (Rectangle × FastWitness) := [(r600,⟨68,43,43⟩),(r601,⟨68,43,43⟩),(r602,⟨68,43,43⟩),(r603,⟨68,43,43⟩),(r604,⟨68,43,43⟩),(r605,⟨68,43,43⟩),(r606,⟨68,43,43⟩),(r607,⟨68,43,43⟩)]
theorem checked75 : fastCheckList band b75=true := by decide +kernel

def b76 : List (Rectangle × FastWitness) := [(r608,⟨68,43,43⟩),(r609,⟨68,43,43⟩),(r610,⟨68,43,43⟩),(r611,⟨68,43,43⟩),(r612,⟨68,43,43⟩),(r613,⟨68,43,43⟩),(r614,⟨68,43,43⟩),(r615,⟨68,43,43⟩)]
theorem checked76 : fastCheckList band b76=true := by decide +kernel

def b77 : List (Rectangle × FastWitness) := [(r616,⟨68,43,43⟩),(r617,⟨68,43,43⟩),(r618,⟨68,43,43⟩),(r619,⟨68,43,43⟩),(r620,⟨68,43,43⟩),(r621,⟨68,43,43⟩),(r622,⟨68,43,43⟩),(r623,⟨68,43,43⟩)]
theorem checked77 : fastCheckList band b77=true := by decide +kernel

def b78 : List (Rectangle × FastWitness) := [(r624,⟨68,43,43⟩),(r625,⟨68,43,43⟩),(r626,⟨68,43,43⟩),(r627,⟨68,43,43⟩),(r628,⟨68,43,43⟩),(r629,⟨68,43,43⟩),(r630,⟨68,43,43⟩),(r631,⟨68,43,43⟩)]
theorem checked78 : fastCheckList band b78=true := by decide +kernel

def b79 : List (Rectangle × FastWitness) := [(r632,⟨68,43,43⟩),(r633,⟨68,43,43⟩),(r634,⟨68,43,43⟩),(r635,⟨68,43,43⟩),(r636,⟨68,43,43⟩),(r637,⟨68,43,43⟩),(r638,⟨68,43,43⟩),(r639,⟨68,43,43⟩)]
theorem checked79 : fastCheckList band b79=true := by decide +kernel

def b80 : List (Rectangle × FastWitness) := [(r640,⟨68,43,43⟩),(r641,⟨68,43,43⟩),(r642,⟨68,43,43⟩),(r643,⟨68,43,43⟩),(r644,⟨68,43,43⟩),(r645,⟨68,43,43⟩),(r646,⟨68,43,43⟩),(r647,⟨68,43,43⟩)]
theorem checked80 : fastCheckList band b80=true := by decide +kernel

def b81 : List (Rectangle × FastWitness) := [(r648,⟨68,43,43⟩),(r649,⟨68,43,43⟩),(r650,⟨68,43,43⟩),(r651,⟨68,43,43⟩),(r652,⟨68,43,43⟩),(r653,⟨68,43,43⟩),(r654,⟨68,43,43⟩),(r655,⟨68,43,43⟩)]
theorem checked81 : fastCheckList band b81=true := by decide +kernel

def b82 : List (Rectangle × FastWitness) := [(r656,⟨68,43,43⟩),(r657,⟨68,43,43⟩),(r658,⟨68,43,43⟩),(r659,⟨68,43,43⟩),(r660,⟨68,43,43⟩),(r661,⟨68,43,43⟩),(r662,⟨68,43,43⟩),(r663,⟨68,43,43⟩)]
theorem checked82 : fastCheckList band b82=true := by decide +kernel

def b83 : List (Rectangle × FastWitness) := [(r664,⟨68,43,43⟩),(r665,⟨68,43,43⟩),(r666,⟨68,43,43⟩),(r667,⟨68,43,43⟩),(r668,⟨68,43,43⟩),(r669,⟨68,44,44⟩),(r670,⟨68,44,44⟩),(r671,⟨68,44,44⟩)]
theorem checked83 : fastCheckList band b83=true := by decide +kernel

def b84 : List (Rectangle × FastWitness) := [(r672,⟨68,44,44⟩),(r673,⟨68,44,44⟩),(r674,⟨68,44,44⟩),(r675,⟨68,44,44⟩),(r676,⟨68,44,44⟩),(r677,⟨68,44,44⟩),(r678,⟨68,44,44⟩),(r679,⟨68,44,44⟩)]
theorem checked84 : fastCheckList band b84=true := by decide +kernel

def b85 : List (Rectangle × FastWitness) := [(r680,⟨68,44,44⟩),(r681,⟨68,44,44⟩),(r682,⟨68,44,44⟩),(r683,⟨68,44,44⟩),(r684,⟨68,44,44⟩),(r685,⟨68,44,44⟩),(r686,⟨68,44,44⟩),(r687,⟨68,44,44⟩)]
theorem checked85 : fastCheckList band b85=true := by decide +kernel

def b86 : List (Rectangle × FastWitness) := [(r688,⟨68,44,44⟩),(r689,⟨68,44,44⟩),(r690,⟨68,44,44⟩),(r691,⟨68,44,44⟩),(r692,⟨68,44,44⟩),(r693,⟨68,44,44⟩),(r694,⟨68,44,44⟩),(r695,⟨68,44,44⟩)]
theorem checked86 : fastCheckList band b86=true := by decide +kernel

def b87 : List (Rectangle × FastWitness) := [(r696,⟨68,44,44⟩),(r697,⟨68,44,44⟩),(r698,⟨68,44,44⟩),(r699,⟨68,44,44⟩),(r700,⟨68,44,44⟩),(r701,⟨68,44,44⟩),(r702,⟨68,44,44⟩),(r703,⟨68,44,44⟩)]
theorem checked87 : fastCheckList band b87=true := by decide +kernel

def b88 : List (Rectangle × FastWitness) := [(r704,⟨68,44,44⟩),(r705,⟨68,44,44⟩),(r706,⟨68,44,44⟩),(r707,⟨68,44,44⟩),(r708,⟨68,44,44⟩),(r709,⟨68,44,44⟩),(r710,⟨68,44,44⟩),(r711,⟨68,44,44⟩)]
theorem checked88 : fastCheckList band b88=true := by decide +kernel

def b89 : List (Rectangle × FastWitness) := [(r712,⟨68,44,44⟩),(r713,⟨68,44,44⟩),(r714,⟨68,44,44⟩),(r715,⟨68,44,44⟩),(r716,⟨68,44,44⟩),(r717,⟨68,44,44⟩),(r718,⟨68,44,44⟩),(r719,⟨68,44,44⟩)]
theorem checked89 : fastCheckList band b89=true := by decide +kernel

def b90 : List (Rectangle × FastWitness) := [(r720,⟨68,44,44⟩),(r721,⟨68,44,44⟩),(r722,⟨68,44,44⟩),(r723,⟨68,44,44⟩),(r724,⟨68,44,44⟩),(r725,⟨68,44,44⟩),(r726,⟨68,44,44⟩),(r727,⟨68,44,44⟩)]
theorem checked90 : fastCheckList band b90=true := by decide +kernel

def b91 : List (Rectangle × FastWitness) := [(r728,⟨68,44,44⟩),(r729,⟨68,44,44⟩),(r730,⟨68,44,44⟩),(r731,⟨68,44,44⟩),(r732,⟨68,44,44⟩),(r733,⟨68,44,44⟩),(r734,⟨68,44,44⟩),(r735,⟨68,44,44⟩)]
theorem checked91 : fastCheckList band b91=true := by decide +kernel

def b92 : List (Rectangle × FastWitness) := [(r736,⟨68,44,44⟩),(r737,⟨68,44,44⟩),(r738,⟨68,44,44⟩),(r739,⟨68,44,44⟩),(r740,⟨68,44,44⟩),(r741,⟨68,44,44⟩),(r742,⟨68,44,44⟩),(r743,⟨68,44,44⟩)]
theorem checked92 : fastCheckList band b92=true := by decide +kernel

def b93 : List (Rectangle × FastWitness) := [(r744,⟨68,44,44⟩),(r745,⟨68,44,44⟩),(r746,⟨68,44,44⟩),(r747,⟨68,44,44⟩),(r748,⟨68,44,44⟩),(r749,⟨68,44,44⟩),(r750,⟨68,44,44⟩),(r751,⟨68,44,44⟩)]
theorem checked93 : fastCheckList band b93=true := by decide +kernel

def b94 : List (Rectangle × FastWitness) := [(r752,⟨68,44,44⟩),(r753,⟨68,44,44⟩),(r754,⟨68,44,44⟩),(r755,⟨68,44,44⟩),(r756,⟨68,44,44⟩),(r757,⟨68,44,44⟩),(r758,⟨68,44,45⟩),(r759,⟨68,44,45⟩)]
theorem checked94 : fastCheckList band b94=true := by decide +kernel

def b95 : List (Rectangle × FastWitness) := [(r760,⟨68,44,45⟩),(r761,⟨68,44,45⟩),(r762,⟨68,44,45⟩),(r763,⟨68,44,45⟩),(r764,⟨68,44,45⟩),(r765,⟨68,44,45⟩),(r766,⟨68,44,45⟩),(r767,⟨68,44,45⟩)]
theorem checked95 : fastCheckList band b95=true := by decide +kernel

def b96 : List (Rectangle × FastWitness) := [(r768,⟨68,44,45⟩),(r769,⟨68,44,45⟩),(r770,⟨68,44,45⟩),(r771,⟨68,44,45⟩),(r772,⟨68,44,45⟩),(r773,⟨68,44,45⟩),(r774,⟨68,44,45⟩),(r775,⟨68,44,45⟩)]
theorem checked96 : fastCheckList band b96=true := by decide +kernel

def b97 : List (Rectangle × FastWitness) := [(r776,⟨68,44,45⟩),(r777,⟨68,44,45⟩),(r778,⟨68,44,45⟩),(r779,⟨68,44,45⟩),(r780,⟨68,44,45⟩),(r781,⟨68,44,45⟩),(r782,⟨68,44,45⟩),(r783,⟨68,44,45⟩)]
theorem checked97 : fastCheckList band b97=true := by decide +kernel

def b98 : List (Rectangle × FastWitness) := [(r784,⟨68,44,45⟩),(r785,⟨68,44,45⟩),(r786,⟨68,44,45⟩),(r787,⟨68,44,45⟩),(r788,⟨68,44,45⟩),(r789,⟨68,44,45⟩),(r790,⟨68,45,45⟩),(r791,⟨68,45,45⟩)]
theorem checked98 : fastCheckList band b98=true := by decide +kernel

def b99 : List (Rectangle × FastWitness) := [(r792,⟨68,45,45⟩),(r793,⟨68,45,45⟩),(r794,⟨68,45,45⟩),(r795,⟨68,45,45⟩),(r796,⟨68,45,45⟩),(r797,⟨68,45,45⟩),(r798,⟨68,45,45⟩),(r799,⟨68,45,45⟩)]
theorem checked99 : fastCheckList band b99=true := by decide +kernel

def b100 : List (Rectangle × FastWitness) := [(r800,⟨68,45,45⟩),(r801,⟨68,45,45⟩),(r802,⟨68,45,45⟩),(r803,⟨68,45,45⟩),(r804,⟨68,45,45⟩),(r805,⟨68,45,45⟩),(r806,⟨68,45,45⟩),(r807,⟨68,45,45⟩)]
theorem checked100 : fastCheckList band b100=true := by decide +kernel

def b101 : List (Rectangle × FastWitness) := [(r808,⟨68,45,45⟩),(r809,⟨68,45,45⟩),(r810,⟨68,45,45⟩),(r811,⟨68,45,45⟩),(r812,⟨68,45,45⟩),(r813,⟨68,45,45⟩),(r814,⟨68,46,46⟩),(r815,⟨68,46,46⟩)]
theorem checked101 : fastCheckList band b101=true := by decide +kernel

def b102 : List (Rectangle × FastWitness) := [(r816,⟨68,46,46⟩),(r817,⟨68,46,46⟩),(r818,⟨68,46,46⟩),(r819,⟨68,46,46⟩),(r820,⟨68,46,46⟩),(r821,⟨68,46,46⟩),(r822,⟨68,46,46⟩),(r823,⟨68,46,46⟩)]
theorem checked102 : fastCheckList band b102=true := by decide +kernel

def b103 : List (Rectangle × FastWitness) := [(r824,⟨68,46,46⟩),(r825,⟨68,46,46⟩),(r826,⟨68,46,46⟩),(r827,⟨68,46,46⟩),(r828,⟨68,46,46⟩),(r829,⟨68,46,46⟩),(r830,⟨68,46,46⟩),(r831,⟨68,46,46⟩)]
theorem checked103 : fastCheckList band b103=true := by decide +kernel

def b104 : List (Rectangle × FastWitness) := [(r832,⟨68,46,46⟩),(r833,⟨68,46,46⟩),(r834,⟨68,46,46⟩),(r835,⟨68,46,46⟩),(r836,⟨68,46,46⟩),(r837,⟨68,46,46⟩),(r838,⟨68,46,46⟩),(r839,⟨68,46,46⟩)]
theorem checked104 : fastCheckList band b104=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B56T3579To3720Fast


