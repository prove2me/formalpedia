-- Prove2me | Definitions.Def_Yukon_b0501efd7bb2b6402d7e3aa0
-- name    : Yukon_b0501efd7bb2b6402d7e3aa0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T15:16:33.892068+00:00
-- url     : https://prove2.me/theorems/3468e6aa-cad9-4919-b323-8f8b203a47c5
-- title:
--   Relative certificate source part 2/2
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR11B57T3594To3792Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR11B57T3594To3792Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR11B57T3594To3792Fast.lean
--
--   yukon-proof-operation:certificate-split-module-Yukon_b0501efd7bb2b6402d7e3aa0
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTZlMjRhYzJkYzlhMTcwZGUyZTFkNTA2MjA3NzYxNTdmMmNmZGNlZWFkMTQ3NzZiNzlhZWM5YzRhMWViMmRmMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LW1vZHVsZS1ZdWtvbl9iMDUwMWVmZDdiYjJiNjQwMmQ3ZTNhYTAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iMDUwMWVmZDdiYjJiNjQwMmQ3ZTNhYTAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9359a01235ff7e09f797aa21
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_a8c84e8128694a4d90f4fef9











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 075dc6d6ab233ef2e942c040a95e7cc0d9f9428b7b6997e34e4fecdd40910d9d.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR11B57T3594To3792Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b64 : List (Rectangle × FastWitness) := [(r512,⟨68,43,43⟩),(r513,⟨68,43,43⟩),(r514,⟨68,43,43⟩),(r515,⟨68,43,43⟩),(r516,⟨68,43,43⟩),(r517,⟨68,43,43⟩),(r518,⟨68,43,43⟩),(r519,⟨68,43,43⟩)]
theorem checked64 : fastCheckList band b64=true := by decide +kernel

def b65 : List (Rectangle × FastWitness) := [(r520,⟨68,43,43⟩),(r521,⟨68,43,44⟩),(r522,⟨68,43,44⟩),(r523,⟨68,43,44⟩),(r524,⟨68,43,44⟩),(r525,⟨68,43,44⟩),(r526,⟨68,43,44⟩),(r527,⟨68,43,44⟩)]
theorem checked65 : fastCheckList band b65=true := by decide +kernel

def b66 : List (Rectangle × FastWitness) := [(r528,⟨68,43,44⟩),(r529,⟨68,43,44⟩),(r530,⟨68,43,44⟩),(r531,⟨68,43,44⟩),(r532,⟨68,43,44⟩),(r533,⟨68,43,44⟩),(r534,⟨68,43,44⟩),(r535,⟨68,43,44⟩)]
theorem checked66 : fastCheckList band b66=true := by decide +kernel

def b67 : List (Rectangle × FastWitness) := [(r536,⟨68,43,44⟩),(r537,⟨68,43,44⟩),(r538,⟨68,43,44⟩),(r539,⟨68,43,44⟩),(r540,⟨68,43,44⟩),(r541,⟨68,43,44⟩),(r542,⟨68,43,44⟩),(r543,⟨68,43,44⟩)]
theorem checked67 : fastCheckList band b67=true := by decide +kernel

def b68 : List (Rectangle × FastWitness) := [(r544,⟨68,43,44⟩),(r545,⟨68,43,44⟩),(r546,⟨68,43,44⟩),(r547,⟨68,43,44⟩),(r548,⟨68,43,44⟩),(r549,⟨68,43,44⟩),(r550,⟨68,43,44⟩),(r551,⟨68,43,44⟩)]
theorem checked68 : fastCheckList band b68=true := by decide +kernel

def b69 : List (Rectangle × FastWitness) := [(r552,⟨68,43,44⟩),(r553,⟨68,43,44⟩),(r554,⟨68,43,44⟩),(r555,⟨68,43,44⟩),(r556,⟨68,43,44⟩),(r557,⟨68,43,44⟩),(r558,⟨68,43,44⟩),(r559,⟨68,43,44⟩)]
theorem checked69 : fastCheckList band b69=true := by decide +kernel

def b70 : List (Rectangle × FastWitness) := [(r560,⟨68,43,44⟩),(r561,⟨68,43,44⟩),(r562,⟨68,43,44⟩),(r563,⟨68,43,44⟩),(r564,⟨68,43,44⟩),(r565,⟨68,43,44⟩),(r566,⟨68,43,44⟩),(r567,⟨68,43,44⟩)]
theorem checked70 : fastCheckList band b70=true := by decide +kernel

def b71 : List (Rectangle × FastWitness) := [(r568,⟨68,43,44⟩),(r569,⟨68,43,44⟩),(r570,⟨68,43,44⟩),(r571,⟨68,43,44⟩),(r572,⟨68,43,44⟩),(r573,⟨68,43,44⟩),(r574,⟨68,43,44⟩),(r575,⟨68,43,44⟩)]
theorem checked71 : fastCheckList band b71=true := by decide +kernel

def b72 : List (Rectangle × FastWitness) := [(r576,⟨68,43,44⟩),(r577,⟨68,43,44⟩),(r578,⟨68,43,44⟩),(r579,⟨68,43,44⟩),(r580,⟨68,43,44⟩),(r581,⟨68,43,44⟩),(r582,⟨68,43,44⟩),(r583,⟨68,43,44⟩)]
theorem checked72 : fastCheckList band b72=true := by decide +kernel

def b73 : List (Rectangle × FastWitness) := [(r584,⟨68,43,44⟩),(r585,⟨68,43,44⟩),(r586,⟨68,43,44⟩),(r587,⟨68,43,44⟩),(r588,⟨68,43,44⟩),(r589,⟨68,43,44⟩),(r590,⟨68,43,44⟩),(r591,⟨68,43,44⟩)]
theorem checked73 : fastCheckList band b73=true := by decide +kernel

def b74 : List (Rectangle × FastWitness) := [(r592,⟨68,43,44⟩),(r593,⟨68,43,44⟩),(r594,⟨68,43,44⟩),(r595,⟨68,43,44⟩),(r596,⟨68,43,44⟩),(r597,⟨68,43,44⟩),(r598,⟨68,43,44⟩),(r599,⟨68,43,44⟩)]
theorem checked74 : fastCheckList band b74=true := by decide +kernel

def b75 : List (Rectangle × FastWitness) := [(r600,⟨68,43,44⟩),(r601,⟨68,43,44⟩),(r602,⟨68,43,44⟩),(r603,⟨68,43,44⟩),(r604,⟨68,43,44⟩),(r605,⟨68,43,44⟩),(r606,⟨68,43,44⟩),(r607,⟨68,43,44⟩)]
theorem checked75 : fastCheckList band b75=true := by decide +kernel

def b76 : List (Rectangle × FastWitness) := [(r608,⟨68,43,44⟩),(r609,⟨68,43,44⟩),(r610,⟨68,43,44⟩),(r611,⟨68,43,44⟩),(r612,⟨68,43,44⟩),(r613,⟨68,43,44⟩),(r614,⟨68,43,44⟩),(r615,⟨68,43,44⟩)]
theorem checked76 : fastCheckList band b76=true := by decide +kernel

def b77 : List (Rectangle × FastWitness) := [(r616,⟨68,43,44⟩),(r617,⟨68,43,44⟩),(r618,⟨68,43,44⟩),(r619,⟨68,43,44⟩),(r620,⟨68,43,44⟩),(r621,⟨68,43,44⟩),(r622,⟨68,43,44⟩),(r623,⟨68,43,44⟩)]
theorem checked77 : fastCheckList band b77=true := by decide +kernel

def b78 : List (Rectangle × FastWitness) := [(r624,⟨68,43,44⟩),(r625,⟨68,43,44⟩),(r626,⟨68,43,44⟩),(r627,⟨68,43,44⟩),(r628,⟨68,43,44⟩),(r629,⟨68,43,44⟩),(r630,⟨68,43,44⟩),(r631,⟨68,43,44⟩)]
theorem checked78 : fastCheckList band b78=true := by decide +kernel

def b79 : List (Rectangle × FastWitness) := [(r632,⟨68,43,44⟩),(r633,⟨68,43,44⟩),(r634,⟨68,43,44⟩),(r635,⟨68,43,44⟩),(r636,⟨68,43,44⟩),(r637,⟨68,43,44⟩),(r638,⟨68,43,44⟩),(r639,⟨68,44,44⟩)]
theorem checked79 : fastCheckList band b79=true := by decide +kernel

def b80 : List (Rectangle × FastWitness) := [(r640,⟨68,44,44⟩),(r641,⟨68,44,44⟩),(r642,⟨68,44,44⟩),(r643,⟨68,44,44⟩),(r644,⟨68,44,44⟩),(r645,⟨68,44,44⟩),(r646,⟨68,44,44⟩),(r647,⟨68,44,44⟩)]
theorem checked80 : fastCheckList band b80=true := by decide +kernel

def b81 : List (Rectangle × FastWitness) := [(r648,⟨68,44,44⟩),(r649,⟨68,44,44⟩),(r650,⟨68,44,44⟩),(r651,⟨68,44,44⟩),(r652,⟨68,44,44⟩),(r653,⟨68,44,44⟩),(r654,⟨68,44,44⟩),(r655,⟨68,44,44⟩)]
theorem checked81 : fastCheckList band b81=true := by decide +kernel

def b82 : List (Rectangle × FastWitness) := [(r656,⟨68,44,44⟩),(r657,⟨68,44,44⟩),(r658,⟨68,44,44⟩),(r659,⟨68,44,44⟩),(r660,⟨68,44,44⟩),(r661,⟨68,44,44⟩),(r662,⟨68,44,44⟩),(r663,⟨68,44,44⟩)]
theorem checked82 : fastCheckList band b82=true := by decide +kernel

def b83 : List (Rectangle × FastWitness) := [(r664,⟨68,44,44⟩),(r665,⟨68,44,44⟩),(r666,⟨68,44,44⟩),(r667,⟨68,44,44⟩),(r668,⟨68,44,44⟩),(r669,⟨68,44,44⟩),(r670,⟨68,44,44⟩),(r671,⟨68,44,44⟩)]
theorem checked83 : fastCheckList band b83=true := by decide +kernel

def b84 : List (Rectangle × FastWitness) := [(r672,⟨68,44,44⟩),(r673,⟨68,44,44⟩),(r674,⟨68,44,44⟩),(r675,⟨68,44,44⟩),(r676,⟨68,44,44⟩),(r677,⟨68,44,44⟩),(r678,⟨68,44,44⟩),(r679,⟨68,44,44⟩)]
theorem checked84 : fastCheckList band b84=true := by decide +kernel

def b85 : List (Rectangle × FastWitness) := [(r680,⟨68,44,44⟩),(r681,⟨68,44,44⟩),(r682,⟨68,44,44⟩),(r683,⟨68,44,44⟩),(r684,⟨68,44,44⟩),(r685,⟨68,44,44⟩),(r686,⟨68,44,44⟩),(r687,⟨68,44,44⟩)]
theorem checked85 : fastCheckList band b85=true := by decide +kernel

def b86 : List (Rectangle × FastWitness) := [(r688,⟨68,44,45⟩),(r689,⟨68,44,45⟩),(r690,⟨68,44,45⟩),(r691,⟨68,44,45⟩),(r692,⟨68,44,45⟩),(r693,⟨68,44,45⟩),(r694,⟨68,44,45⟩),(r695,⟨68,44,45⟩)]
theorem checked86 : fastCheckList band b86=true := by decide +kernel

def b87 : List (Rectangle × FastWitness) := [(r696,⟨68,44,45⟩),(r697,⟨68,44,45⟩),(r698,⟨68,44,45⟩),(r699,⟨68,44,45⟩),(r700,⟨68,44,45⟩),(r701,⟨68,44,45⟩),(r702,⟨68,44,45⟩),(r703,⟨68,44,45⟩)]
theorem checked87 : fastCheckList band b87=true := by decide +kernel

def b88 : List (Rectangle × FastWitness) := [(r704,⟨68,44,45⟩),(r705,⟨68,44,45⟩),(r706,⟨68,44,45⟩),(r707,⟨68,44,45⟩),(r708,⟨68,44,45⟩),(r709,⟨68,44,45⟩),(r710,⟨68,44,45⟩),(r711,⟨68,44,45⟩)]
theorem checked88 : fastCheckList band b88=true := by decide +kernel

def b89 : List (Rectangle × FastWitness) := [(r712,⟨68,44,45⟩),(r713,⟨68,44,45⟩),(r714,⟨68,44,45⟩),(r715,⟨68,44,45⟩),(r716,⟨68,44,45⟩),(r717,⟨68,44,45⟩),(r718,⟨68,44,45⟩),(r719,⟨68,44,45⟩)]
theorem checked89 : fastCheckList band b89=true := by decide +kernel

def b90 : List (Rectangle × FastWitness) := [(r720,⟨68,44,45⟩),(r721,⟨68,44,45⟩),(r722,⟨68,44,45⟩),(r723,⟨68,44,45⟩),(r724,⟨68,44,45⟩),(r725,⟨68,44,45⟩),(r726,⟨68,44,45⟩),(r727,⟨68,44,45⟩)]
theorem checked90 : fastCheckList band b90=true := by decide +kernel

def b91 : List (Rectangle × FastWitness) := [(r728,⟨68,44,45⟩),(r729,⟨68,44,45⟩),(r730,⟨68,44,45⟩),(r731,⟨68,44,45⟩),(r732,⟨68,44,45⟩),(r733,⟨68,44,45⟩),(r734,⟨68,44,45⟩),(r735,⟨68,44,45⟩)]
theorem checked91 : fastCheckList band b91=true := by decide +kernel

def b92 : List (Rectangle × FastWitness) := [(r736,⟨68,44,45⟩),(r737,⟨68,44,45⟩),(r738,⟨68,44,45⟩),(r739,⟨68,44,45⟩),(r740,⟨68,44,45⟩),(r741,⟨68,44,45⟩),(r742,⟨68,45,45⟩),(r743,⟨68,45,45⟩)]
theorem checked92 : fastCheckList band b92=true := by decide +kernel

def b93 : List (Rectangle × FastWitness) := [(r744,⟨68,45,45⟩),(r745,⟨68,45,45⟩),(r746,⟨68,45,45⟩),(r747,⟨68,45,45⟩),(r748,⟨68,45,45⟩),(r749,⟨68,45,45⟩),(r750,⟨68,45,45⟩),(r751,⟨68,45,45⟩)]
theorem checked93 : fastCheckList band b93=true := by decide +kernel

def b94 : List (Rectangle × FastWitness) := [(r752,⟨68,45,45⟩),(r753,⟨68,45,45⟩),(r754,⟨68,45,45⟩),(r755,⟨68,45,45⟩),(r756,⟨68,45,46⟩),(r757,⟨68,45,46⟩),(r758,⟨68,45,46⟩),(r759,⟨68,45,46⟩)]
theorem checked94 : fastCheckList band b94=true := by decide +kernel

def b95 : List (Rectangle × FastWitness) := [(r760,⟨68,45,46⟩),(r761,⟨68,45,46⟩),(r762,⟨68,45,46⟩),(r763,⟨68,45,46⟩),(r764,⟨68,45,46⟩),(r765,⟨68,45,46⟩),(r766,⟨68,45,46⟩),(r767,⟨68,45,46⟩)]
theorem checked95 : fastCheckList band b95=true := by decide +kernel

def b96 : List (Rectangle × FastWitness) := [(r768,⟨68,45,46⟩),(r769,⟨68,46,46⟩),(r770,⟨68,46,46⟩),(r771,⟨68,46,46⟩),(r772,⟨68,46,46⟩),(r773,⟨68,46,46⟩),(r774,⟨68,46,46⟩),(r775,⟨68,46,46⟩)]
theorem checked96 : fastCheckList band b96=true := by decide +kernel

def b97 : List (Rectangle × FastWitness) := [(r776,⟨68,46,46⟩),(r777,⟨68,46,46⟩),(r778,⟨68,46,46⟩),(r779,⟨68,46,46⟩),(r780,⟨68,46,46⟩),(r781,⟨68,46,46⟩),(r782,⟨68,46,46⟩),(r783,⟨68,46,46⟩)]
theorem checked97 : fastCheckList band b97=true := by decide +kernel

def b98 : List (Rectangle × FastWitness) := [(r784,⟨68,46,46⟩),(r785,⟨68,46,46⟩),(r786,⟨68,46,46⟩),(r787,⟨68,46,46⟩),(r788,⟨68,46,46⟩),(r789,⟨68,46,46⟩),(r790,⟨68,46,46⟩),(r791,⟨68,46,46⟩)]
theorem checked98 : fastCheckList band b98=true := by decide +kernel

def b99 : List (Rectangle × FastWitness) := [(r792,⟨68,46,46⟩),(r793,⟨68,46,46⟩),(r794,⟨68,46,46⟩),(r795,⟨68,46,46⟩),(r796,⟨68,46,46⟩),(r797,⟨68,46,46⟩),(r798,⟨68,46,46⟩),(r799,⟨68,46,46⟩)]
theorem checked99 : fastCheckList band b99=true := by decide +kernel

def b100 : List (Rectangle × FastWitness) := [(r800,⟨68,46,46⟩),(r801,⟨68,46,46⟩),(r802,⟨68,46,46⟩),(r803,⟨68,46,46⟩),(r804,⟨68,46,46⟩),(r805,⟨68,46,46⟩),(r806,⟨68,46,46⟩),(r807,⟨68,46,46⟩)]
theorem checked100 : fastCheckList band b100=true := by decide +kernel

def b101 : List (Rectangle × FastWitness) := [(r808,⟨68,46,46⟩),(r809,⟨68,46,46⟩),(r810,⟨68,46,46⟩),(r811,⟨68,46,46⟩),(r812,⟨68,46,46⟩),(r813,⟨68,46,46⟩),(r814,⟨68,46,46⟩),(r815,⟨68,46,46⟩)]
theorem checked101 : fastCheckList band b101=true := by decide +kernel

def b102 : List (Rectangle × FastWitness) := [(r816,⟨68,46,46⟩),(r817,⟨68,46,46⟩),(r818,⟨68,46,46⟩),(r819,⟨68,46,46⟩),(r820,⟨68,46,46⟩),(r821,⟨68,46,46⟩),(r822,⟨68,46,46⟩),(r823,⟨68,46,46⟩)]
theorem checked102 : fastCheckList band b102=true := by decide +kernel

def b103 : List (Rectangle × FastWitness) := [(r824,⟨68,46,46⟩),(r825,⟨68,46,46⟩),(r826,⟨68,46,46⟩),(r827,⟨68,46,47⟩),(r828,⟨68,46,47⟩),(r829,⟨68,46,47⟩),(r830,⟨68,46,47⟩),(r831,⟨68,46,47⟩)]
theorem checked103 : fastCheckList band b103=true := by decide +kernel

def b104 : List (Rectangle × FastWitness) := [(r832,⟨68,46,47⟩),(r833,⟨68,46,47⟩),(r834,⟨68,46,47⟩),(r835,⟨68,46,47⟩),(r836,⟨68,46,47⟩),(r837,⟨68,46,47⟩),(r838,⟨68,46,47⟩),(r839,⟨68,46,47⟩)]
theorem checked104 : fastCheckList band b104=true := by decide +kernel

def b105 : List (Rectangle × FastWitness) := [(r840,⟨68,46,47⟩),(r841,⟨68,47,47⟩),(r842,⟨68,47,47⟩),(r843,⟨68,47,47⟩),(r844,⟨68,47,47⟩),(r845,⟨68,47,47⟩),(r846,⟨68,47,47⟩),(r847,⟨68,47,47⟩)]
theorem checked105 : fastCheckList band b105=true := by decide +kernel

def b106 : List (Rectangle × FastWitness) := [(r848,⟨68,47,47⟩),(r849,⟨68,47,47⟩),(r850,⟨68,47,47⟩),(r851,⟨68,47,47⟩),(r852,⟨68,47,47⟩),(r853,⟨68,47,47⟩),(r854,⟨68,47,47⟩),(r855,⟨68,48,49⟩)]
theorem checked106 : fastCheckList band b106=true := by decide +kernel

def b107 : List (Rectangle × FastWitness) := [(r856,⟨68,48,48⟩),(r857,⟨68,48,48⟩),(r858,⟨68,48,48⟩),(r859,⟨68,48,48⟩),(r860,⟨68,48,48⟩),(r861,⟨68,48,48⟩),(r862,⟨68,48,48⟩),(r863,⟨68,48,48⟩)]
theorem checked107 : fastCheckList band b107=true := by decide +kernel

def b108 : List (Rectangle × FastWitness) := [(r864,⟨68,48,48⟩),(r865,⟨68,48,48⟩),(r866,⟨68,48,48⟩),(r867,⟨68,48,48⟩),(r868,⟨68,48,48⟩),(r869,⟨68,48,48⟩),(r870,⟨68,48,48⟩),(r871,⟨68,48,48⟩)]
theorem checked108 : fastCheckList band b108=true := by decide +kernel

def b109 : List (Rectangle × FastWitness) := [(r872,⟨68,48,49⟩),(r873,⟨68,48,49⟩),(r874,⟨68,48,49⟩),(r875,⟨68,48,49⟩),(r876,⟨68,48,49⟩),(r877,⟨68,48,49⟩),(r878,⟨68,48,49⟩),(r879,⟨68,48,49⟩)]
theorem checked109 : fastCheckList band b109=true := by decide +kernel

def b110 : List (Rectangle × FastWitness) := [(r880,⟨68,48,49⟩),(r881,⟨68,48,49⟩),(r882,⟨68,48,49⟩),(r883,⟨68,49,49⟩),(r884,⟨68,49,49⟩),(r885,⟨68,49,49⟩),(r886,⟨68,49,49⟩),(r887,⟨68,49,49⟩)]
theorem checked110 : fastCheckList band b110=true := by decide +kernel

def b111 : List (Rectangle × FastWitness) := [(r888,⟨68,49,49⟩),(r889,⟨68,49,49⟩),(r890,⟨68,49,49⟩),(r891,⟨68,49,49⟩),(r892,⟨68,49,49⟩),(r893,⟨68,49,49⟩),(r894,⟨68,49,49⟩),(r895,⟨68,49,49⟩)]
theorem checked111 : fastCheckList band b111=true := by decide +kernel

def b112 : List (Rectangle × FastWitness) := [(r896,⟨68,49,49⟩),(r897,⟨68,49,49⟩),(r898,⟨68,49,49⟩),(r899,⟨68,49,49⟩),(r900,⟨68,49,49⟩),(r901,⟨68,49,49⟩),(r902,⟨68,49,49⟩),(r903,⟨68,49,49⟩)]
theorem checked112 : fastCheckList band b112=true := by decide +kernel

def b113 : List (Rectangle × FastWitness) := [(r904,⟨68,49,49⟩),(r905,⟨68,49,49⟩),(r906,⟨68,49,49⟩),(r907,⟨68,49,49⟩),(r908,⟨68,49,49⟩),(r909,⟨68,49,49⟩),(r910,⟨68,49,49⟩),(r911,⟨68,49,49⟩)]
theorem checked113 : fastCheckList band b113=true := by decide +kernel

def b114 : List (Rectangle × FastWitness) := [(r912,⟨68,49,50⟩),(r913,⟨68,49,50⟩),(r914,⟨68,49,50⟩),(r915,⟨68,49,50⟩),(r916,⟨68,50,50⟩),(r917,⟨68,50,50⟩),(r918,⟨68,50,50⟩),(r919,⟨68,50,50⟩)]
theorem checked114 : fastCheckList band b114=true := by decide +kernel

def b115 : List (Rectangle × FastWitness) := [(r920,⟨68,50,50⟩),(r921,⟨68,50,50⟩),(r922,⟨68,50,50⟩),(r923,⟨68,50,50⟩),(r924,⟨68,50,50⟩),(r925,⟨68,52,52⟩),(r926,⟨68,52,52⟩),(r927,⟨68,52,52⟩)]
theorem checked115 : fastCheckList band b115=true := by decide +kernel

def b116 : List (Rectangle × FastWitness) := [(r928,⟨68,52,52⟩),(r929,⟨68,52,52⟩),(r930,⟨68,52,52⟩),(r931,⟨68,52,52⟩),(r932,⟨68,52,52⟩),(r933,⟨68,52,52⟩),(r934,⟨68,52,52⟩),(r935,⟨68,52,52⟩)]
theorem checked116 : fastCheckList band b116=true := by decide +kernel

def b117 : List (Rectangle × FastWitness) := [(r936,⟨68,52,52⟩),(r937,⟨68,52,52⟩),(r938,⟨68,52,52⟩),(r939,⟨68,52,52⟩),(r940,⟨68,52,52⟩),(r941,⟨68,52,52⟩),(r942,⟨68,52,52⟩),(r943,⟨68,52,52⟩)]
theorem checked117 : fastCheckList band b117=true := by decide +kernel

def b118 : List (Rectangle × FastWitness) := [(r944,⟨68,52,52⟩),(r945,⟨68,52,53⟩),(r946,⟨68,52,53⟩),(r947,⟨68,53,53⟩),(r948,⟨68,53,53⟩),(r949,⟨68,53,53⟩),(r950,⟨68,53,53⟩),(r951,⟨68,53,53⟩)]
theorem checked118 : fastCheckList band b118=true := by decide +kernel

def b119 : List (Rectangle × FastWitness) := [(r952,⟨68,53,53⟩),(r953,⟨68,53,53⟩),(r954,⟨68,53,53⟩),(r955,⟨68,53,53⟩),(r956,⟨68,53,53⟩),(r957,⟨68,53,53⟩),(r958,⟨68,53,53⟩),(r959,⟨68,53,53⟩)]
theorem checked119 : fastCheckList band b119=true := by decide +kernel

def b120 : List (Rectangle × FastWitness) := [(r960,⟨68,53,53⟩),(r961,⟨68,53,53⟩),(r962,⟨68,53,53⟩),(r963,⟨68,53,54⟩),(r964,⟨68,54,54⟩),(r965,⟨68,54,54⟩),(r966,⟨68,54,54⟩),(r967,⟨68,54,54⟩)]
theorem checked120 : fastCheckList band b120=true := by decide +kernel

def b121 : List (Rectangle × FastWitness) := [(r968,⟨68,54,54⟩),(r969,⟨68,54,54⟩),(r970,⟨68,54,54⟩),(r971,⟨68,54,54⟩),(r972,⟨68,54,54⟩),(r973,⟨68,54,54⟩),(r974,⟨68,54,54⟩),(r975,⟨68,54,54⟩)]
theorem checked121 : fastCheckList band b121=true := by decide +kernel

def b122 : List (Rectangle × FastWitness) := [(r976,⟨68,54,54⟩),(r977,⟨68,57,57⟩),(r978,⟨68,57,57⟩),(r979,⟨68,57,57⟩),(r980,⟨68,57,57⟩),(r981,⟨68,57,57⟩),(r982,⟨68,57,57⟩),(r983,⟨68,57,57⟩)]
theorem checked122 : fastCheckList band b122=true := by decide +kernel

def b123 : List (Rectangle × FastWitness) := [(r984,⟨68,57,57⟩),(r985,⟨68,57,57⟩),(r986,⟨68,57,58⟩),(r987,⟨68,58,58⟩),(r988,⟨68,58,58⟩),(r989,⟨68,58,58⟩),(r990,⟨68,58,58⟩),(r991,⟨68,58,58⟩)]
theorem checked123 : fastCheckList band b123=true := by decide +kernel

def b124 : List (Rectangle × FastWitness) := [(r992,⟨68,58,58⟩),(r993,⟨68,58,58⟩),(r994,⟨68,58,58⟩),(r995,⟨68,58,58⟩),(r996,⟨68,58,59⟩),(r997,⟨68,59,59⟩),(r998,⟨68,59,59⟩),(r999,⟨68,59,59⟩)]
theorem checked124 : fastCheckList band b124=true := by decide +kernel

def b125 : List (Rectangle × FastWitness) := [(r1000,⟨68,59,59⟩),(r1001,⟨68,59,59⟩),(r1002,⟨68,59,59⟩),(r1003,⟨68,59,59⟩),(r1004,⟨68,59,59⟩),(r1005,⟨68,60,60⟩),(r1006,⟨68,60,60⟩),(r1007,⟨68,60,60⟩)]
theorem checked125 : fastCheckList band b125=true := by decide +kernel

def b126 : List (Rectangle × FastWitness) := [(r1008,⟨68,60,60⟩),(r1009,⟨68,60,60⟩),(r1010,⟨68,64,64⟩),(r1011,⟨68,64,64⟩),(r1012,⟨68,64,64⟩),(r1013,⟨68,64,64⟩),(r1014,⟨68,64,64⟩),(r1015,⟨68,64,64⟩)]
theorem checked126 : fastCheckList band b126=true := by decide +kernel

def b127 : List (Rectangle × FastWitness) := [(r1016,⟨68,64,64⟩),(r1017,⟨68,65,65⟩)]
theorem checked127 : fastCheckList band b127=true := by decide +kernel

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24++b25++b26++b27++b28++b29++b30++b31++b32++b33++b34++b35++b36++b37++b38++b39++b40++b41++b42++b43++b44++b45++b46++b47++b48++b49++b50++b51++b52++b53++b54++b55++b56++b57++b58++b59++b60++b61++b62++b63++b64++b65++b66++b67++b68++b69++b70++b71++b72++b73++b74++b75++b76++b77++b78++b79++b80++b81++b82++b83++b84++b85++b86++b87++b88++b89++b90++b91++b92++b93++b94++b95++b96++b97++b98++b99++b100++b101++b102++b103++b104++b105++b106++b107++b108++b109++b110++b111++b112++b113++b114++b115++b116++b117++b118++b119++b120++b121++b122++b123++b124++b125++b126++b127
def rows : List Rectangle := witnessedRows.map Prod.fst
theorem all_fast_checked : fastCheckList band witnessedRows=true := by
  have joinChecked (xs ys : List (Rectangle × FastWitness)) (hx : fastCheckList band xs = true) (hy : fastCheckList band ys = true) : fastCheckList band (xs ++ ys) = true := by
    rw [fastCheckList_append, hx, hy]
    rfl
  have joined1 := joinChecked _ _ checked0 checked1
  have joined2 := joinChecked _ _ joined1 checked2
  have joined3 := joinChecked _ _ joined2 checked3
  have joined4 := joinChecked _ _ joined3 checked4
  have joined5 := joinChecked _ _ joined4 checked5
  have joined6 := joinChecked _ _ joined5 checked6
  have joined7 := joinChecked _ _ joined6 checked7
  have joined8 := joinChecked _ _ joined7 checked8
  have joined9 := joinChecked _ _ joined8 checked9
  have joined10 := joinChecked _ _ joined9 checked10
  have joined11 := joinChecked _ _ joined10 checked11
  have joined12 := joinChecked _ _ joined11 checked12
  have joined13 := joinChecked _ _ joined12 checked13
  have joined14 := joinChecked _ _ joined13 checked14
  have joined15 := joinChecked _ _ joined14 checked15
  have joined16 := joinChecked _ _ joined15 checked16
  have joined17 := joinChecked _ _ joined16 checked17
  have joined18 := joinChecked _ _ joined17 checked18
  have joined19 := joinChecked _ _ joined18 checked19
  have joined20 := joinChecked _ _ joined19 checked20
  have joined21 := joinChecked _ _ joined20 checked21
  have joined22 := joinChecked _ _ joined21 checked22
  have joined23 := joinChecked _ _ joined22 checked23
  have joined24 := joinChecked _ _ joined23 checked24
  have joined25 := joinChecked _ _ joined24 checked25
  have joined26 := joinChecked _ _ joined25 checked26
  have joined27 := joinChecked _ _ joined26 checked27
  have joined28 := joinChecked _ _ joined27 checked28
  have joined29 := joinChecked _ _ joined28 checked29
  have joined30 := joinChecked _ _ joined29 checked30
  have joined31 := joinChecked _ _ joined30 checked31
  have joined32 := joinChecked _ _ joined31 checked32
  have joined33 := joinChecked _ _ joined32 checked33
  have joined34 := joinChecked _ _ joined33 checked34
  have joined35 := joinChecked _ _ joined34 checked35
  have joined36 := joinChecked _ _ joined35 checked36
  have joined37 := joinChecked _ _ joined36 checked37
  have joined38 := joinChecked _ _ joined37 checked38
  have joined39 := joinChecked _ _ joined38 checked39
  have joined40 := joinChecked _ _ joined39 checked40
  have joined41 := joinChecked _ _ joined40 checked41
  have joined42 := joinChecked _ _ joined41 checked42
  have joined43 := joinChecked _ _ joined42 checked43
  have joined44 := joinChecked _ _ joined43 checked44
  have joined45 := joinChecked _ _ joined44 checked45
  have joined46 := joinChecked _ _ joined45 checked46
  have joined47 := joinChecked _ _ joined46 checked47
  have joined48 := joinChecked _ _ joined47 checked48
  have joined49 := joinChecked _ _ joined48 checked49
  have joined50 := joinChecked _ _ joined49 checked50
  have joined51 := joinChecked _ _ joined50 checked51
  have joined52 := joinChecked _ _ joined51 checked52
  have joined53 := joinChecked _ _ joined52 checked53
  have joined54 := joinChecked _ _ joined53 checked54
  have joined55 := joinChecked _ _ joined54 checked55
  have joined56 := joinChecked _ _ joined55 checked56
  have joined57 := joinChecked _ _ joined56 checked57
  have joined58 := joinChecked _ _ joined57 checked58
  have joined59 := joinChecked _ _ joined58 checked59
  have joined60 := joinChecked _ _ joined59 checked60
  have joined61 := joinChecked _ _ joined60 checked61
  have joined62 := joinChecked _ _ joined61 checked62
  have joined63 := joinChecked _ _ joined62 checked63
  have joined64 := joinChecked _ _ joined63 checked64
  have joined65 := joinChecked _ _ joined64 checked65
  have joined66 := joinChecked _ _ joined65 checked66
  have joined67 := joinChecked _ _ joined66 checked67
  have joined68 := joinChecked _ _ joined67 checked68
  have joined69 := joinChecked _ _ joined68 checked69
  have joined70 := joinChecked _ _ joined69 checked70
  have joined71 := joinChecked _ _ joined70 checked71
  have joined72 := joinChecked _ _ joined71 checked72
  have joined73 := joinChecked _ _ joined72 checked73
  have joined74 := joinChecked _ _ joined73 checked74
  have joined75 := joinChecked _ _ joined74 checked75
  have joined76 := joinChecked _ _ joined75 checked76
  have joined77 := joinChecked _ _ joined76 checked77
  have joined78 := joinChecked _ _ joined77 checked78
  have joined79 := joinChecked _ _ joined78 checked79
  have joined80 := joinChecked _ _ joined79 checked80
  have joined81 := joinChecked _ _ joined80 checked81
  have joined82 := joinChecked _ _ joined81 checked82
  have joined83 := joinChecked _ _ joined82 checked83
  have joined84 := joinChecked _ _ joined83 checked84
  have joined85 := joinChecked _ _ joined84 checked85
  have joined86 := joinChecked _ _ joined85 checked86
  have joined87 := joinChecked _ _ joined86 checked87
  have joined88 := joinChecked _ _ joined87 checked88
  have joined89 := joinChecked _ _ joined88 checked89
  have joined90 := joinChecked _ _ joined89 checked90
  have joined91 := joinChecked _ _ joined90 checked91
  have joined92 := joinChecked _ _ joined91 checked92
  have joined93 := joinChecked _ _ joined92 checked93
  have joined94 := joinChecked _ _ joined93 checked94
  have joined95 := joinChecked _ _ joined94 checked95
  have joined96 := joinChecked _ _ joined95 checked96
  have joined97 := joinChecked _ _ joined96 checked97
  have joined98 := joinChecked _ _ joined97 checked98
  have joined99 := joinChecked _ _ joined98 checked99
  have joined100 := joinChecked _ _ joined99 checked100
  have joined101 := joinChecked _ _ joined100 checked101
  have joined102 := joinChecked _ _ joined101 checked102
  have joined103 := joinChecked _ _ joined102 checked103
  have joined104 := joinChecked _ _ joined103 checked104
  have joined105 := joinChecked _ _ joined104 checked105
  have joined106 := joinChecked _ _ joined105 checked106
  have joined107 := joinChecked _ _ joined106 checked107
  have joined108 := joinChecked _ _ joined107 checked108
  have joined109 := joinChecked _ _ joined108 checked109
  have joined110 := joinChecked _ _ joined109 checked110
  have joined111 := joinChecked _ _ joined110 checked111
  have joined112 := joinChecked _ _ joined111 checked112
  have joined113 := joinChecked _ _ joined112 checked113
  have joined114 := joinChecked _ _ joined113 checked114
  have joined115 := joinChecked _ _ joined114 checked115
  have joined116 := joinChecked _ _ joined115 checked116
  have joined117 := joinChecked _ _ joined116 checked117
  have joined118 := joinChecked _ _ joined117 checked118
  have joined119 := joinChecked _ _ joined118 checked119
  have joined120 := joinChecked _ _ joined119 checked120
  have joined121 := joinChecked _ _ joined120 checked121
  have joined122 := joinChecked _ _ joined121 checked122
  have joined123 := joinChecked _ _ joined122 checked123
  have joined124 := joinChecked _ _ joined123 checked124
  have joined125 := joinChecked _ _ joined124 checked125
  have joined126 := joinChecked _ _ joined125 checked126
  have joined127 := joinChecked _ _ joined126 checked127
  exact joined127
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR11B57T3594To3792Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤57)
    (hT0 : 3594≤T) (hT1 : T≤3792) (hnu : 7471036≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤29852491993091276 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR11B57T3594To3792Fast


