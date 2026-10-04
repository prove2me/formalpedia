-- Prove2me | Definitions.Def_Yukon_cf1cadc6a49ad306715d7fad
-- name    : Yukon_cf1cadc6a49ad306715d7fad
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:42:15.124896+00:00
-- url     : https://prove2.me/theorems/075dfcf6-93eb-4e0e-ab35-2f2a1e63df32
-- title:
--   Relative certificate source part 4/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_cf1cadc6a49ad306715d7fad
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjFiNmRiYzE0Y2QyYWJkZGIyNTY4YTA4OTAyMzUxOTA1NGIxMjg3NjM0MWY2YjE4ZjIzZGMwY2U5OGJiNTcxZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2NmMWNhZGM2YTQ5YWQzMDY3MTVkN2ZhZCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2NmMWNhZGM2YTQ5YWQzMDY3MTVkN2ZhZCIsInYiOjJ9]

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

def b64 : List (Rectangle × FastWitness) := [(r512,⟨67,40,40⟩),(r513,⟨67,40,40⟩),(r514,⟨67,40,40⟩),(r515,⟨67,40,40⟩),(r516,⟨67,40,40⟩),(r517,⟨67,40,40⟩),(r518,⟨67,40,40⟩),(r519,⟨67,40,40⟩)]
theorem checked64 : fastCheckList band b64=true := by decide +kernel

def b65 : List (Rectangle × FastWitness) := [(r520,⟨67,40,40⟩),(r521,⟨67,40,40⟩),(r522,⟨67,40,40⟩),(r523,⟨67,40,40⟩),(r524,⟨67,40,40⟩),(r525,⟨67,40,40⟩),(r526,⟨67,40,40⟩),(r527,⟨67,40,40⟩)]
theorem checked65 : fastCheckList band b65=true := by decide +kernel

def b66 : List (Rectangle × FastWitness) := [(r528,⟨67,40,40⟩),(r529,⟨67,40,40⟩),(r530,⟨67,40,40⟩),(r531,⟨67,40,40⟩),(r532,⟨67,40,40⟩),(r533,⟨67,40,40⟩),(r534,⟨67,40,40⟩),(r535,⟨67,40,40⟩)]
theorem checked66 : fastCheckList band b66=true := by decide +kernel

def b67 : List (Rectangle × FastWitness) := [(r536,⟨67,40,40⟩),(r537,⟨67,40,40⟩),(r538,⟨67,40,40⟩),(r539,⟨67,40,40⟩),(r540,⟨67,40,40⟩),(r541,⟨67,40,40⟩),(r542,⟨67,40,40⟩),(r543,⟨67,40,40⟩)]
theorem checked67 : fastCheckList band b67=true := by decide +kernel

def b68 : List (Rectangle × FastWitness) := [(r544,⟨67,40,40⟩),(r545,⟨67,40,40⟩),(r546,⟨67,40,40⟩),(r547,⟨67,40,40⟩),(r548,⟨67,40,40⟩),(r549,⟨67,40,40⟩),(r550,⟨67,40,40⟩),(r551,⟨67,40,40⟩)]
theorem checked68 : fastCheckList band b68=true := by decide +kernel

def b69 : List (Rectangle × FastWitness) := [(r552,⟨67,40,40⟩),(r553,⟨67,40,40⟩),(r554,⟨67,40,40⟩),(r555,⟨67,40,40⟩),(r556,⟨67,40,40⟩),(r557,⟨67,40,40⟩),(r558,⟨67,40,40⟩),(r559,⟨67,40,40⟩)]
theorem checked69 : fastCheckList band b69=true := by decide +kernel

def b70 : List (Rectangle × FastWitness) := [(r560,⟨67,40,40⟩),(r561,⟨67,40,40⟩),(r562,⟨67,40,40⟩),(r563,⟨67,40,40⟩),(r564,⟨67,40,40⟩),(r565,⟨67,40,40⟩),(r566,⟨67,40,40⟩),(r567,⟨67,40,40⟩)]
theorem checked70 : fastCheckList band b70=true := by decide +kernel

def b71 : List (Rectangle × FastWitness) := [(r568,⟨67,40,40⟩),(r569,⟨67,40,40⟩),(r570,⟨67,40,40⟩),(r571,⟨67,40,40⟩),(r572,⟨67,40,40⟩),(r573,⟨67,40,40⟩),(r574,⟨67,40,40⟩),(r575,⟨67,40,40⟩)]
theorem checked71 : fastCheckList band b71=true := by decide +kernel

def b72 : List (Rectangle × FastWitness) := [(r576,⟨67,40,40⟩),(r577,⟨67,40,40⟩),(r578,⟨67,40,40⟩),(r579,⟨67,40,40⟩),(r580,⟨67,40,40⟩),(r581,⟨67,40,40⟩),(r582,⟨67,40,40⟩),(r583,⟨67,40,40⟩)]
theorem checked72 : fastCheckList band b72=true := by decide +kernel

def b73 : List (Rectangle × FastWitness) := [(r584,⟨67,40,40⟩),(r585,⟨67,40,40⟩),(r586,⟨67,40,40⟩),(r587,⟨67,40,40⟩),(r588,⟨67,40,40⟩),(r589,⟨67,40,40⟩),(r590,⟨67,40,40⟩),(r591,⟨67,40,40⟩)]
theorem checked73 : fastCheckList band b73=true := by decide +kernel

def b74 : List (Rectangle × FastWitness) := [(r592,⟨67,40,40⟩),(r593,⟨67,40,40⟩),(r594,⟨67,40,40⟩),(r595,⟨67,40,40⟩),(r596,⟨67,40,40⟩),(r597,⟨67,40,40⟩),(r598,⟨67,40,40⟩),(r599,⟨67,40,40⟩)]
theorem checked74 : fastCheckList band b74=true := by decide +kernel

def b75 : List (Rectangle × FastWitness) := [(r600,⟨67,40,40⟩),(r601,⟨67,40,40⟩),(r602,⟨67,40,40⟩),(r603,⟨67,40,40⟩),(r604,⟨67,40,40⟩),(r605,⟨67,40,40⟩),(r606,⟨67,40,40⟩),(r607,⟨67,40,40⟩)]
theorem checked75 : fastCheckList band b75=true := by decide +kernel

def b76 : List (Rectangle × FastWitness) := [(r608,⟨67,40,40⟩),(r609,⟨67,40,40⟩),(r610,⟨67,40,40⟩),(r611,⟨67,40,40⟩),(r612,⟨67,40,40⟩),(r613,⟨67,40,40⟩),(r614,⟨67,40,40⟩),(r615,⟨67,40,40⟩)]
theorem checked76 : fastCheckList band b76=true := by decide +kernel

def b77 : List (Rectangle × FastWitness) := [(r616,⟨67,40,40⟩),(r617,⟨67,40,40⟩),(r618,⟨67,40,40⟩),(r619,⟨67,40,40⟩),(r620,⟨67,40,40⟩),(r621,⟨67,40,40⟩),(r622,⟨67,40,40⟩),(r623,⟨67,40,40⟩)]
theorem checked77 : fastCheckList band b77=true := by decide +kernel

def b78 : List (Rectangle × FastWitness) := [(r624,⟨67,40,40⟩),(r625,⟨67,40,40⟩),(r626,⟨67,40,40⟩),(r627,⟨67,40,40⟩),(r628,⟨67,40,40⟩),(r629,⟨67,40,40⟩),(r630,⟨67,40,40⟩),(r631,⟨67,40,40⟩)]
theorem checked78 : fastCheckList band b78=true := by decide +kernel

def b79 : List (Rectangle × FastWitness) := [(r632,⟨67,40,40⟩),(r633,⟨67,40,40⟩),(r634,⟨67,40,40⟩),(r635,⟨67,40,40⟩),(r636,⟨67,40,40⟩),(r637,⟨67,40,40⟩),(r638,⟨67,40,40⟩),(r639,⟨67,40,40⟩)]
theorem checked79 : fastCheckList band b79=true := by decide +kernel

def b80 : List (Rectangle × FastWitness) := [(r640,⟨67,40,40⟩),(r641,⟨67,40,40⟩),(r642,⟨67,40,40⟩),(r643,⟨67,40,40⟩),(r644,⟨67,40,40⟩),(r645,⟨67,40,40⟩),(r646,⟨67,40,40⟩),(r647,⟨67,40,40⟩)]
theorem checked80 : fastCheckList band b80=true := by decide +kernel

def b81 : List (Rectangle × FastWitness) := [(r648,⟨67,40,40⟩),(r649,⟨67,40,40⟩),(r650,⟨67,40,40⟩),(r651,⟨67,40,40⟩),(r652,⟨67,40,40⟩),(r653,⟨67,40,40⟩),(r654,⟨67,40,40⟩),(r655,⟨67,40,40⟩)]
theorem checked81 : fastCheckList band b81=true := by decide +kernel

def b82 : List (Rectangle × FastWitness) := [(r656,⟨67,40,40⟩),(r657,⟨67,40,40⟩),(r658,⟨67,40,40⟩),(r659,⟨67,40,40⟩),(r660,⟨67,40,40⟩),(r661,⟨67,40,40⟩),(r662,⟨67,40,40⟩),(r663,⟨67,40,40⟩)]
theorem checked82 : fastCheckList band b82=true := by decide +kernel

def b83 : List (Rectangle × FastWitness) := [(r664,⟨67,40,40⟩),(r665,⟨67,40,40⟩),(r666,⟨67,40,40⟩),(r667,⟨67,40,40⟩),(r668,⟨67,40,40⟩),(r669,⟨67,40,40⟩),(r670,⟨67,40,40⟩),(r671,⟨67,40,40⟩)]
theorem checked83 : fastCheckList band b83=true := by decide +kernel

def b84 : List (Rectangle × FastWitness) := [(r672,⟨67,40,40⟩),(r673,⟨67,40,40⟩),(r674,⟨67,40,40⟩),(r675,⟨67,40,40⟩),(r676,⟨67,40,40⟩),(r677,⟨67,40,40⟩),(r678,⟨67,40,40⟩),(r679,⟨67,40,40⟩)]
theorem checked84 : fastCheckList band b84=true := by decide +kernel

def b85 : List (Rectangle × FastWitness) := [(r680,⟨67,40,40⟩),(r681,⟨67,40,40⟩),(r682,⟨67,40,40⟩),(r683,⟨67,40,40⟩),(r684,⟨67,40,40⟩),(r685,⟨67,40,40⟩),(r686,⟨67,40,40⟩),(r687,⟨67,40,40⟩)]
theorem checked85 : fastCheckList band b85=true := by decide +kernel

def b86 : List (Rectangle × FastWitness) := [(r688,⟨67,40,40⟩),(r689,⟨67,40,40⟩),(r690,⟨67,40,40⟩),(r691,⟨67,40,40⟩),(r692,⟨67,40,40⟩),(r693,⟨67,40,40⟩),(r694,⟨67,40,40⟩),(r695,⟨67,40,40⟩)]
theorem checked86 : fastCheckList band b86=true := by decide +kernel

def b87 : List (Rectangle × FastWitness) := [(r696,⟨67,40,40⟩),(r697,⟨67,40,40⟩),(r698,⟨67,40,40⟩),(r699,⟨67,40,40⟩),(r700,⟨67,40,40⟩),(r701,⟨67,40,40⟩),(r702,⟨67,40,40⟩),(r703,⟨67,40,40⟩)]
theorem checked87 : fastCheckList band b87=true := by decide +kernel

def b88 : List (Rectangle × FastWitness) := [(r704,⟨67,40,40⟩),(r705,⟨67,40,40⟩),(r706,⟨67,40,40⟩),(r707,⟨67,40,40⟩),(r708,⟨67,40,40⟩),(r709,⟨67,40,40⟩),(r710,⟨67,40,40⟩),(r711,⟨67,40,40⟩)]
theorem checked88 : fastCheckList band b88=true := by decide +kernel

def b89 : List (Rectangle × FastWitness) := [(r712,⟨67,40,40⟩),(r713,⟨67,40,40⟩),(r714,⟨67,40,40⟩),(r715,⟨67,40,40⟩),(r716,⟨67,40,40⟩),(r717,⟨67,40,40⟩),(r718,⟨67,40,40⟩),(r719,⟨67,40,40⟩)]
theorem checked89 : fastCheckList band b89=true := by decide +kernel

def b90 : List (Rectangle × FastWitness) := [(r720,⟨67,40,40⟩),(r721,⟨67,40,40⟩),(r722,⟨67,40,40⟩),(r723,⟨67,40,40⟩),(r724,⟨67,40,40⟩),(r725,⟨67,40,40⟩),(r726,⟨67,40,40⟩),(r727,⟨67,40,40⟩)]
theorem checked90 : fastCheckList band b90=true := by decide +kernel

def b91 : List (Rectangle × FastWitness) := [(r728,⟨67,40,40⟩),(r729,⟨67,40,40⟩),(r730,⟨67,40,40⟩),(r731,⟨67,40,40⟩),(r732,⟨67,40,40⟩),(r733,⟨67,40,40⟩),(r734,⟨67,40,40⟩),(r735,⟨67,40,40⟩)]
theorem checked91 : fastCheckList band b91=true := by decide +kernel

def b92 : List (Rectangle × FastWitness) := [(r736,⟨67,40,40⟩),(r737,⟨67,40,40⟩),(r738,⟨67,40,40⟩),(r739,⟨67,40,40⟩),(r740,⟨67,40,40⟩),(r741,⟨67,40,40⟩),(r742,⟨67,40,40⟩),(r743,⟨67,40,40⟩)]
theorem checked92 : fastCheckList band b92=true := by decide +kernel

def b93 : List (Rectangle × FastWitness) := [(r744,⟨67,40,40⟩),(r745,⟨67,40,40⟩),(r746,⟨67,40,40⟩),(r747,⟨67,40,40⟩),(r748,⟨67,40,40⟩),(r749,⟨67,40,40⟩),(r750,⟨67,40,40⟩),(r751,⟨67,40,40⟩)]
theorem checked93 : fastCheckList band b93=true := by decide +kernel

def b94 : List (Rectangle × FastWitness) := [(r752,⟨67,40,40⟩),(r753,⟨67,40,40⟩),(r754,⟨67,40,40⟩),(r755,⟨67,40,40⟩),(r756,⟨67,40,40⟩),(r757,⟨67,40,40⟩),(r758,⟨67,40,40⟩),(r759,⟨67,40,40⟩)]
theorem checked94 : fastCheckList band b94=true := by decide +kernel

def b95 : List (Rectangle × FastWitness) := [(r760,⟨67,40,40⟩),(r761,⟨67,40,40⟩),(r762,⟨67,40,40⟩),(r763,⟨67,40,40⟩),(r764,⟨67,40,40⟩),(r765,⟨67,40,40⟩),(r766,⟨67,40,40⟩),(r767,⟨67,40,40⟩)]
theorem checked95 : fastCheckList band b95=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


