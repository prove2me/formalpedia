-- Prove2me | Definitions.Def_Yukon_c3389a5df070c5d10eff425f
-- name    : Yukon_c3389a5df070c5d10eff425f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:41:19.96432+00:00
-- url     : https://prove2.me/theorems/8530667b-9015-4382-9df2-83b1189ad7c1
-- title:
--   Relative certificate source part 12/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_c3389a5df070c5d10eff425f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMWNlZmJlZTU4OTY1MGZhMTQwMWY4Mzc1NTEwYzc5MGE2MmYzNTBjNGVkY2I3NjU0OTk2Mzg1MDNmZWRmODhiOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2MzMzg5YTVkZjA3MGM1ZDEwZWZmNDI1ZiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2MzMzg5YTVkZjA3MGM1ZDEwZWZmNDI1ZiIsInYiOjJ9]

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

def b320 : List (Rectangle × FastWitness) := [(r2560,⟨67,51,51⟩),(r2561,⟨67,51,51⟩),(r2562,⟨67,51,51⟩),(r2563,⟨67,51,51⟩),(r2564,⟨67,51,51⟩),(r2565,⟨67,51,51⟩),(r2566,⟨67,51,51⟩),(r2567,⟨67,51,51⟩)]
theorem checked320 : fastCheckList band b320=true := by decide +kernel

def b321 : List (Rectangle × FastWitness) := [(r2568,⟨67,51,51⟩),(r2569,⟨67,51,51⟩),(r2570,⟨67,51,51⟩),(r2571,⟨67,51,51⟩),(r2572,⟨67,51,51⟩),(r2573,⟨67,51,51⟩),(r2574,⟨67,51,51⟩),(r2575,⟨67,51,51⟩)]
theorem checked321 : fastCheckList band b321=true := by decide +kernel

def b322 : List (Rectangle × FastWitness) := [(r2576,⟨67,51,51⟩),(r2577,⟨67,51,51⟩),(r2578,⟨67,51,51⟩),(r2579,⟨67,51,52⟩),(r2580,⟨67,52,52⟩),(r2581,⟨67,54,54⟩),(r2582,⟨67,54,54⟩),(r2583,⟨67,54,54⟩)]
theorem checked322 : fastCheckList band b322=true := by decide +kernel

def b323 : List (Rectangle × FastWitness) := [(r2584,⟨67,54,54⟩),(r2585,⟨67,54,54⟩),(r2586,⟨67,54,54⟩),(r2587,⟨67,54,54⟩),(r2588,⟨67,54,54⟩),(r2589,⟨67,54,54⟩),(r2590,⟨67,54,54⟩),(r2591,⟨67,54,54⟩)]
theorem checked323 : fastCheckList band b323=true := by decide +kernel

def b324 : List (Rectangle × FastWitness) := [(r2592,⟨67,54,54⟩),(r2593,⟨67,54,54⟩),(r2594,⟨67,54,54⟩),(r2595,⟨67,54,54⟩),(r2596,⟨67,54,54⟩),(r2597,⟨67,54,54⟩),(r2598,⟨67,54,54⟩),(r2599,⟨67,54,54⟩)]
theorem checked324 : fastCheckList band b324=true := by decide +kernel

def b325 : List (Rectangle × FastWitness) := [(r2600,⟨67,54,54⟩),(r2601,⟨67,54,54⟩),(r2602,⟨67,54,54⟩),(r2603,⟨67,54,54⟩),(r2604,⟨67,54,54⟩),(r2605,⟨67,54,54⟩),(r2606,⟨67,54,54⟩),(r2607,⟨67,55,55⟩)]
theorem checked325 : fastCheckList band b325=true := by decide +kernel

def b326 : List (Rectangle × FastWitness) := [(r2608,⟨67,55,55⟩),(r2609,⟨67,55,55⟩),(r2610,⟨67,55,55⟩),(r2611,⟨67,55,55⟩),(r2612,⟨67,55,55⟩),(r2613,⟨67,55,55⟩),(r2614,⟨67,55,55⟩),(r2615,⟨67,55,55⟩)]
theorem checked326 : fastCheckList band b326=true := by decide +kernel

def b327 : List (Rectangle × FastWitness) := [(r2616,⟨67,55,55⟩),(r2617,⟨67,55,55⟩),(r2618,⟨67,55,55⟩),(r2619,⟨67,55,55⟩),(r2620,⟨67,55,55⟩),(r2621,⟨67,55,55⟩),(r2622,⟨67,55,55⟩),(r2623,⟨67,56,56⟩)]
theorem checked327 : fastCheckList band b327=true := by decide +kernel

def b328 : List (Rectangle × FastWitness) := [(r2624,⟨67,56,56⟩),(r2625,⟨67,56,56⟩),(r2626,⟨67,56,56⟩),(r2627,⟨67,56,56⟩),(r2628,⟨67,56,56⟩),(r2629,⟨67,56,56⟩),(r2630,⟨67,59,59⟩),(r2631,⟨67,59,59⟩)]
theorem checked328 : fastCheckList band b328=true := by decide +kernel

def b329 : List (Rectangle × FastWitness) := [(r2632,⟨67,59,59⟩),(r2633,⟨67,59,59⟩),(r2634,⟨67,59,59⟩),(r2635,⟨67,59,59⟩),(r2636,⟨67,59,59⟩),(r2637,⟨67,59,59⟩),(r2638,⟨67,59,59⟩),(r2639,⟨67,59,59⟩)]
theorem checked329 : fastCheckList band b329=true := by decide +kernel

def b330 : List (Rectangle × FastWitness) := [(r2640,⟨67,59,59⟩),(r2641,⟨67,59,59⟩),(r2642,⟨67,59,59⟩),(r2643,⟨67,59,59⟩),(r2644,⟨67,60,60⟩),(r2645,⟨67,60,60⟩),(r2646,⟨67,60,60⟩),(r2647,⟨67,60,60⟩)]
theorem checked330 : fastCheckList band b330=true := by decide +kernel

def b331 : List (Rectangle × FastWitness) := [(r2648,⟨67,60,60⟩),(r2649,⟨67,60,60⟩),(r2650,⟨67,60,60⟩),(r2651,⟨67,60,60⟩),(r2652,⟨67,60,60⟩),(r2653,⟨67,61,61⟩),(r2654,⟨67,61,61⟩),(r2655,⟨67,61,61⟩)]
theorem checked331 : fastCheckList band b331=true := by decide +kernel

def b332 : List (Rectangle × FastWitness) := [(r2656,⟨67,61,61⟩),(r2657,⟨67,61,61⟩),(r2658,⟨67,61,61⟩),(r2659,⟨67,61,61⟩),(r2660,⟨67,61,61⟩),(r2661,⟨67,62,62⟩),(r2662,⟨67,62,62⟩),(r2663,⟨67,62,62⟩)]
theorem checked332 : fastCheckList band b332=true := by decide +kernel

def b333 : List (Rectangle × FastWitness) := [(r2664,⟨67,62,62⟩),(r2665,⟨67,62,62⟩),(r2666,⟨67,62,62⟩)]
theorem checked333 : fastCheckList band b333=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


