-- Prove2me | Definitions.Def_Yukon_af74c4beea8bf8e77d9f8c06
-- name    : Yukon_af74c4beea8bf8e77d9f8c06
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:05:14.665401+00:00
-- url     : https://prove2.me/theorems/49d36717-8273-4c43-97b5-098f364dfcc8
-- title:
--   Relative certificate source part 4/8
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
--
--   yukon-proof-operation:certificate-b58-module-Yukon_af74c4beea8bf8e77d9f8c06
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzJhMjJmNjE3YTNhNTAyYmY0NGFlMTU0ZmM5M2QzNTU2ZjMyOTIzNTYxODY5NjVmMThiZTA3NzlmNDUwZDBlNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1OC1tb2R1bGUtWXVrb25fYWY3NGM0YmVlYThiZjhlNzdkOWY4YzA2IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fYWY3NGM0YmVlYThiZjhlNzdkOWY4YzA2IiwidiI6Mn0]

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

def b72 : List (Rectangle × FastWitness) := [(r576,⟨70,42,42⟩),(r577,⟨70,42,42⟩),(r578,⟨70,42,42⟩),(r579,⟨70,42,42⟩),(r580,⟨70,42,42⟩),(r581,⟨70,42,42⟩),(r582,⟨70,42,42⟩),(r583,⟨70,42,42⟩)]
theorem checked72 : fastCheckList band b72=true := by decide +kernel

def b73 : List (Rectangle × FastWitness) := [(r584,⟨70,42,42⟩),(r585,⟨70,42,42⟩),(r586,⟨70,42,42⟩),(r587,⟨70,42,42⟩),(r588,⟨70,42,42⟩),(r589,⟨70,42,42⟩),(r590,⟨70,42,42⟩),(r591,⟨70,42,42⟩)]
theorem checked73 : fastCheckList band b73=true := by decide +kernel

def b74 : List (Rectangle × FastWitness) := [(r592,⟨70,42,42⟩),(r593,⟨70,42,42⟩),(r594,⟨70,42,42⟩),(r595,⟨70,42,42⟩),(r596,⟨70,42,42⟩),(r597,⟨70,42,42⟩),(r598,⟨70,42,42⟩),(r599,⟨70,42,42⟩)]
theorem checked74 : fastCheckList band b74=true := by decide +kernel

def b75 : List (Rectangle × FastWitness) := [(r600,⟨70,42,42⟩),(r601,⟨70,42,42⟩),(r602,⟨70,42,42⟩),(r603,⟨70,42,42⟩),(r604,⟨70,42,42⟩),(r605,⟨70,42,42⟩),(r606,⟨70,42,42⟩),(r607,⟨70,42,42⟩)]
theorem checked75 : fastCheckList band b75=true := by decide +kernel

def b76 : List (Rectangle × FastWitness) := [(r608,⟨70,42,42⟩),(r609,⟨70,42,42⟩),(r610,⟨70,42,42⟩),(r611,⟨70,42,42⟩),(r612,⟨70,42,42⟩),(r613,⟨70,42,42⟩),(r614,⟨70,42,42⟩),(r615,⟨70,42,42⟩)]
theorem checked76 : fastCheckList band b76=true := by decide +kernel

def b77 : List (Rectangle × FastWitness) := [(r616,⟨70,42,42⟩),(r617,⟨70,42,42⟩),(r618,⟨70,42,42⟩),(r619,⟨70,42,42⟩),(r620,⟨70,42,42⟩),(r621,⟨70,42,42⟩),(r622,⟨70,42,42⟩),(r623,⟨70,42,42⟩)]
theorem checked77 : fastCheckList band b77=true := by decide +kernel

def b78 : List (Rectangle × FastWitness) := [(r624,⟨70,42,42⟩),(r625,⟨70,42,42⟩),(r626,⟨70,42,42⟩),(r627,⟨70,42,42⟩),(r628,⟨70,42,42⟩),(r629,⟨70,42,42⟩),(r630,⟨70,42,42⟩),(r631,⟨70,42,42⟩)]
theorem checked78 : fastCheckList band b78=true := by decide +kernel

def b79 : List (Rectangle × FastWitness) := [(r632,⟨70,42,42⟩),(r633,⟨70,42,42⟩),(r634,⟨70,42,42⟩),(r635,⟨70,42,42⟩),(r636,⟨70,42,42⟩),(r637,⟨70,42,42⟩),(r638,⟨70,42,42⟩),(r639,⟨70,42,42⟩)]
theorem checked79 : fastCheckList band b79=true := by decide +kernel

def b80 : List (Rectangle × FastWitness) := [(r640,⟨70,42,42⟩),(r641,⟨70,42,42⟩),(r642,⟨70,42,42⟩),(r643,⟨70,42,42⟩),(r644,⟨70,42,42⟩),(r645,⟨70,42,42⟩),(r646,⟨70,42,42⟩),(r647,⟨70,42,42⟩)]
theorem checked80 : fastCheckList band b80=true := by decide +kernel

def b81 : List (Rectangle × FastWitness) := [(r648,⟨70,42,42⟩),(r649,⟨70,42,42⟩),(r650,⟨70,42,42⟩),(r651,⟨70,42,42⟩),(r652,⟨70,42,42⟩),(r653,⟨70,42,42⟩),(r654,⟨70,42,42⟩),(r655,⟨70,42,42⟩)]
theorem checked81 : fastCheckList band b81=true := by decide +kernel

def b82 : List (Rectangle × FastWitness) := [(r656,⟨70,42,42⟩),(r657,⟨70,42,42⟩),(r658,⟨70,42,42⟩),(r659,⟨70,42,42⟩),(r660,⟨70,42,42⟩),(r661,⟨70,42,42⟩),(r662,⟨70,42,42⟩),(r663,⟨70,42,42⟩)]
theorem checked82 : fastCheckList band b82=true := by decide +kernel

def b83 : List (Rectangle × FastWitness) := [(r664,⟨70,42,42⟩),(r665,⟨70,42,42⟩),(r666,⟨70,42,42⟩),(r667,⟨70,42,42⟩),(r668,⟨70,42,42⟩),(r669,⟨70,42,42⟩),(r670,⟨70,42,42⟩),(r671,⟨70,42,42⟩)]
theorem checked83 : fastCheckList band b83=true := by decide +kernel

def b84 : List (Rectangle × FastWitness) := [(r672,⟨70,42,42⟩),(r673,⟨70,42,42⟩),(r674,⟨70,42,42⟩),(r675,⟨70,42,42⟩),(r676,⟨70,42,42⟩),(r677,⟨70,42,42⟩),(r678,⟨70,42,42⟩),(r679,⟨70,42,42⟩)]
theorem checked84 : fastCheckList band b84=true := by decide +kernel

def b85 : List (Rectangle × FastWitness) := [(r680,⟨70,42,42⟩),(r681,⟨70,42,42⟩),(r682,⟨70,42,42⟩),(r683,⟨70,42,42⟩),(r684,⟨70,42,42⟩),(r685,⟨70,42,42⟩),(r686,⟨70,42,42⟩),(r687,⟨70,42,42⟩)]
theorem checked85 : fastCheckList band b85=true := by decide +kernel

def b86 : List (Rectangle × FastWitness) := [(r688,⟨70,42,42⟩),(r689,⟨70,42,42⟩),(r690,⟨70,42,42⟩),(r691,⟨70,42,42⟩),(r692,⟨70,42,42⟩),(r693,⟨70,42,42⟩),(r694,⟨70,42,42⟩),(r695,⟨70,42,42⟩)]
theorem checked86 : fastCheckList band b86=true := by decide +kernel

def b87 : List (Rectangle × FastWitness) := [(r696,⟨70,42,42⟩),(r697,⟨70,42,42⟩),(r698,⟨70,42,42⟩),(r699,⟨70,42,42⟩),(r700,⟨70,42,42⟩),(r701,⟨70,42,42⟩),(r702,⟨70,42,42⟩),(r703,⟨70,42,42⟩)]
theorem checked87 : fastCheckList band b87=true := by decide +kernel

def b88 : List (Rectangle × FastWitness) := [(r704,⟨70,42,42⟩),(r705,⟨70,42,42⟩),(r706,⟨70,42,42⟩),(r707,⟨70,42,42⟩),(r708,⟨70,42,42⟩),(r709,⟨70,42,42⟩),(r710,⟨70,42,42⟩),(r711,⟨70,42,42⟩)]
theorem checked88 : fastCheckList band b88=true := by decide +kernel

def b89 : List (Rectangle × FastWitness) := [(r712,⟨70,42,42⟩),(r713,⟨70,42,42⟩),(r714,⟨70,42,42⟩),(r715,⟨70,42,42⟩),(r716,⟨70,42,42⟩),(r717,⟨70,42,42⟩),(r718,⟨70,42,42⟩),(r719,⟨70,42,42⟩)]
theorem checked89 : fastCheckList band b89=true := by decide +kernel

def b90 : List (Rectangle × FastWitness) := [(r720,⟨70,42,42⟩),(r721,⟨70,42,42⟩),(r722,⟨70,42,42⟩),(r723,⟨70,42,42⟩),(r724,⟨70,42,42⟩),(r725,⟨70,42,42⟩),(r726,⟨70,42,42⟩),(r727,⟨70,42,42⟩)]
theorem checked90 : fastCheckList band b90=true := by decide +kernel

def b91 : List (Rectangle × FastWitness) := [(r728,⟨70,42,42⟩),(r729,⟨70,42,42⟩),(r730,⟨70,42,42⟩),(r731,⟨70,42,42⟩),(r732,⟨70,42,42⟩),(r733,⟨70,42,42⟩),(r734,⟨70,42,42⟩),(r735,⟨70,42,42⟩)]
theorem checked91 : fastCheckList band b91=true := by decide +kernel

def b92 : List (Rectangle × FastWitness) := [(r736,⟨70,42,42⟩),(r737,⟨70,42,42⟩),(r738,⟨70,42,42⟩),(r739,⟨70,42,42⟩),(r740,⟨70,42,42⟩),(r741,⟨70,42,42⟩),(r742,⟨70,42,42⟩),(r743,⟨70,42,42⟩)]
theorem checked92 : fastCheckList band b92=true := by decide +kernel

def b93 : List (Rectangle × FastWitness) := [(r744,⟨70,42,42⟩),(r745,⟨70,42,42⟩),(r746,⟨70,42,42⟩),(r747,⟨70,42,42⟩),(r748,⟨70,42,42⟩),(r749,⟨70,42,42⟩),(r750,⟨70,42,42⟩),(r751,⟨70,42,42⟩)]
theorem checked93 : fastCheckList band b93=true := by decide +kernel

def b94 : List (Rectangle × FastWitness) := [(r752,⟨70,42,42⟩),(r753,⟨70,42,42⟩),(r754,⟨70,42,42⟩),(r755,⟨70,42,42⟩),(r756,⟨70,42,42⟩),(r757,⟨70,42,42⟩),(r758,⟨70,42,42⟩),(r759,⟨70,42,42⟩)]
theorem checked94 : fastCheckList band b94=true := by decide +kernel

def b95 : List (Rectangle × FastWitness) := [(r760,⟨70,42,42⟩),(r761,⟨70,42,42⟩),(r762,⟨70,42,42⟩),(r763,⟨70,42,42⟩),(r764,⟨70,42,42⟩),(r765,⟨70,42,42⟩),(r766,⟨70,42,42⟩),(r767,⟨70,42,42⟩)]
theorem checked95 : fastCheckList band b95=true := by decide +kernel

def b96 : List (Rectangle × FastWitness) := [(r768,⟨70,42,42⟩),(r769,⟨70,42,42⟩),(r770,⟨70,42,42⟩),(r771,⟨70,42,42⟩),(r772,⟨70,42,42⟩),(r773,⟨70,42,42⟩),(r774,⟨70,42,42⟩),(r775,⟨70,42,42⟩)]
theorem checked96 : fastCheckList band b96=true := by decide +kernel

def b97 : List (Rectangle × FastWitness) := [(r776,⟨70,42,42⟩),(r777,⟨70,42,42⟩),(r778,⟨70,42,42⟩),(r779,⟨70,42,42⟩),(r780,⟨70,42,42⟩),(r781,⟨70,42,42⟩),(r782,⟨70,42,42⟩),(r783,⟨70,42,42⟩)]
theorem checked97 : fastCheckList band b97=true := by decide +kernel

def b98 : List (Rectangle × FastWitness) := [(r784,⟨70,42,42⟩),(r785,⟨70,42,42⟩),(r786,⟨70,42,42⟩),(r787,⟨70,42,42⟩),(r788,⟨70,42,42⟩),(r789,⟨70,42,42⟩),(r790,⟨70,42,42⟩),(r791,⟨70,42,42⟩)]
theorem checked98 : fastCheckList band b98=true := by decide +kernel

def b99 : List (Rectangle × FastWitness) := [(r792,⟨70,42,42⟩),(r793,⟨70,42,42⟩),(r794,⟨70,42,42⟩),(r795,⟨70,42,42⟩),(r796,⟨70,42,42⟩),(r797,⟨70,42,42⟩),(r798,⟨70,42,42⟩),(r799,⟨70,42,42⟩)]
theorem checked99 : fastCheckList band b99=true := by decide +kernel

def b100 : List (Rectangle × FastWitness) := [(r800,⟨70,42,42⟩),(r801,⟨70,42,42⟩),(r802,⟨70,42,42⟩),(r803,⟨70,42,42⟩),(r804,⟨70,42,42⟩),(r805,⟨70,42,42⟩),(r806,⟨70,42,42⟩),(r807,⟨70,42,42⟩)]
theorem checked100 : fastCheckList band b100=true := by decide +kernel

def b101 : List (Rectangle × FastWitness) := [(r808,⟨70,42,42⟩),(r809,⟨70,42,42⟩),(r810,⟨70,42,42⟩),(r811,⟨70,42,42⟩),(r812,⟨70,42,42⟩),(r813,⟨70,42,42⟩),(r814,⟨70,42,42⟩),(r815,⟨70,43,43⟩)]
theorem checked101 : fastCheckList band b101=true := by decide +kernel

def b102 : List (Rectangle × FastWitness) := [(r816,⟨70,43,43⟩),(r817,⟨70,43,43⟩),(r818,⟨70,43,43⟩),(r819,⟨70,43,43⟩),(r820,⟨70,43,43⟩),(r821,⟨70,43,43⟩),(r822,⟨70,43,43⟩),(r823,⟨70,43,43⟩)]
theorem checked102 : fastCheckList band b102=true := by decide +kernel

def b103 : List (Rectangle × FastWitness) := [(r824,⟨70,43,43⟩),(r825,⟨70,43,43⟩),(r826,⟨70,43,43⟩),(r827,⟨70,43,43⟩),(r828,⟨70,43,43⟩),(r829,⟨70,43,43⟩),(r830,⟨70,43,43⟩),(r831,⟨70,43,43⟩)]
theorem checked103 : fastCheckList band b103=true := by decide +kernel

def b104 : List (Rectangle × FastWitness) := [(r832,⟨70,43,43⟩),(r833,⟨70,43,43⟩),(r834,⟨70,43,43⟩),(r835,⟨70,43,43⟩),(r836,⟨70,43,43⟩),(r837,⟨70,43,43⟩),(r838,⟨70,43,43⟩),(r839,⟨70,43,43⟩)]
theorem checked104 : fastCheckList band b104=true := by decide +kernel

def b105 : List (Rectangle × FastWitness) := [(r840,⟨70,43,43⟩),(r841,⟨70,43,43⟩),(r842,⟨70,43,43⟩),(r843,⟨70,43,43⟩),(r844,⟨70,43,43⟩),(r845,⟨70,43,43⟩),(r846,⟨70,43,43⟩),(r847,⟨70,43,43⟩)]
theorem checked105 : fastCheckList band b105=true := by decide +kernel

def b106 : List (Rectangle × FastWitness) := [(r848,⟨70,43,43⟩),(r849,⟨70,43,43⟩),(r850,⟨70,43,43⟩),(r851,⟨70,43,43⟩),(r852,⟨70,43,43⟩),(r853,⟨70,43,43⟩),(r854,⟨70,43,43⟩),(r855,⟨70,43,43⟩)]
theorem checked106 : fastCheckList band b106=true := by decide +kernel

def b107 : List (Rectangle × FastWitness) := [(r856,⟨70,43,43⟩),(r857,⟨70,43,43⟩),(r858,⟨70,43,43⟩),(r859,⟨70,43,43⟩),(r860,⟨70,43,43⟩),(r861,⟨70,43,43⟩),(r862,⟨70,43,43⟩),(r863,⟨70,43,43⟩)]
theorem checked107 : fastCheckList band b107=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast


