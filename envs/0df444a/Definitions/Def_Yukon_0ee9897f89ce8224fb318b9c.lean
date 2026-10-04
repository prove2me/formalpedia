-- Prove2me | Definitions.Def_Yukon_0ee9897f89ce8224fb318b9c
-- name    : Yukon_0ee9897f89ce8224fb318b9c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:41:56.379383+00:00
-- url     : https://prove2.me/theorems/f9d5f5e6-abf3-4711-b3fd-8a4288e2c50b
-- title:
--   Relative certificate source part 11/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_0ee9897f89ce8224fb318b9c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2M4ZTcwNTQyN2ZkMTdiOGE0YzNkZmM2YjgwMDEwMzkyY2U4ZGVkMTVmNzc1NTY1YTBhMDFhN2NkNGEwNzBhMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uXzBlZTk4OTdmODljZTgyMjRmYjMxOGI5YyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzBlZTk4OTdmODljZTgyMjRmYjMxOGI5YyIsInYiOjJ9]

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

def b288 : List (Rectangle × FastWitness) := [(r2304,⟨67,45,45⟩),(r2305,⟨67,45,45⟩),(r2306,⟨67,45,45⟩),(r2307,⟨67,45,45⟩),(r2308,⟨67,45,45⟩),(r2309,⟨67,45,45⟩),(r2310,⟨67,45,45⟩),(r2311,⟨67,45,45⟩)]
theorem checked288 : fastCheckList band b288=true := by decide +kernel

def b289 : List (Rectangle × FastWitness) := [(r2312,⟨67,45,45⟩),(r2313,⟨67,45,45⟩),(r2314,⟨67,45,45⟩),(r2315,⟨67,45,45⟩),(r2316,⟨67,45,45⟩),(r2317,⟨67,45,45⟩),(r2318,⟨67,45,45⟩),(r2319,⟨67,45,45⟩)]
theorem checked289 : fastCheckList band b289=true := by decide +kernel

def b290 : List (Rectangle × FastWitness) := [(r2320,⟨67,45,45⟩),(r2321,⟨67,45,45⟩),(r2322,⟨67,45,45⟩),(r2323,⟨67,45,45⟩),(r2324,⟨67,45,45⟩),(r2325,⟨67,45,45⟩),(r2326,⟨67,45,45⟩),(r2327,⟨67,45,45⟩)]
theorem checked290 : fastCheckList band b290=true := by decide +kernel

def b291 : List (Rectangle × FastWitness) := [(r2328,⟨67,45,45⟩),(r2329,⟨67,45,45⟩),(r2330,⟨67,45,45⟩),(r2331,⟨67,45,45⟩),(r2332,⟨67,45,45⟩),(r2333,⟨67,45,45⟩),(r2334,⟨67,45,45⟩),(r2335,⟨67,45,45⟩)]
theorem checked291 : fastCheckList band b291=true := by decide +kernel

def b292 : List (Rectangle × FastWitness) := [(r2336,⟨67,45,45⟩),(r2337,⟨67,45,45⟩),(r2338,⟨67,45,45⟩),(r2339,⟨67,45,45⟩),(r2340,⟨67,45,45⟩),(r2341,⟨67,45,45⟩),(r2342,⟨67,45,45⟩),(r2343,⟨67,45,45⟩)]
theorem checked292 : fastCheckList band b292=true := by decide +kernel

def b293 : List (Rectangle × FastWitness) := [(r2344,⟨67,45,45⟩),(r2345,⟨67,45,45⟩),(r2346,⟨67,45,45⟩),(r2347,⟨67,45,45⟩),(r2348,⟨67,45,45⟩),(r2349,⟨67,45,45⟩),(r2350,⟨67,45,45⟩),(r2351,⟨67,45,45⟩)]
theorem checked293 : fastCheckList band b293=true := by decide +kernel

def b294 : List (Rectangle × FastWitness) := [(r2352,⟨67,45,45⟩),(r2353,⟨67,45,45⟩),(r2354,⟨67,45,45⟩),(r2355,⟨67,45,45⟩),(r2356,⟨67,45,45⟩),(r2357,⟨67,45,45⟩),(r2358,⟨67,45,45⟩),(r2359,⟨67,45,45⟩)]
theorem checked294 : fastCheckList band b294=true := by decide +kernel

def b295 : List (Rectangle × FastWitness) := [(r2360,⟨67,45,45⟩),(r2361,⟨67,45,45⟩),(r2362,⟨67,45,45⟩),(r2363,⟨67,45,46⟩),(r2364,⟨67,45,46⟩),(r2365,⟨67,46,46⟩),(r2366,⟨67,46,46⟩),(r2367,⟨67,46,46⟩)]
theorem checked295 : fastCheckList band b295=true := by decide +kernel

def b296 : List (Rectangle × FastWitness) := [(r2368,⟨67,46,46⟩),(r2369,⟨67,46,46⟩),(r2370,⟨67,46,46⟩),(r2371,⟨67,46,46⟩),(r2372,⟨67,46,46⟩),(r2373,⟨67,46,46⟩),(r2374,⟨67,46,46⟩),(r2375,⟨67,46,46⟩)]
theorem checked296 : fastCheckList band b296=true := by decide +kernel

def b297 : List (Rectangle × FastWitness) := [(r2376,⟨67,46,46⟩),(r2377,⟨67,46,46⟩),(r2378,⟨67,46,46⟩),(r2379,⟨67,46,46⟩),(r2380,⟨67,46,46⟩),(r2381,⟨67,46,46⟩),(r2382,⟨67,46,46⟩),(r2383,⟨67,46,46⟩)]
theorem checked297 : fastCheckList band b297=true := by decide +kernel

def b298 : List (Rectangle × FastWitness) := [(r2384,⟨67,46,46⟩),(r2385,⟨67,46,46⟩),(r2386,⟨67,46,46⟩),(r2387,⟨67,46,46⟩),(r2388,⟨67,47,47⟩),(r2389,⟨67,47,47⟩),(r2390,⟨67,47,47⟩),(r2391,⟨67,47,47⟩)]
theorem checked298 : fastCheckList band b298=true := by decide +kernel

def b299 : List (Rectangle × FastWitness) := [(r2392,⟨67,47,47⟩),(r2393,⟨67,47,47⟩),(r2394,⟨67,47,47⟩),(r2395,⟨67,47,47⟩),(r2396,⟨67,47,47⟩),(r2397,⟨67,47,47⟩),(r2398,⟨67,47,47⟩),(r2399,⟨67,47,47⟩)]
theorem checked299 : fastCheckList band b299=true := by decide +kernel

def b300 : List (Rectangle × FastWitness) := [(r2400,⟨67,47,47⟩),(r2401,⟨67,47,47⟩),(r2402,⟨67,47,47⟩),(r2403,⟨67,47,47⟩),(r2404,⟨67,47,47⟩),(r2405,⟨67,47,47⟩),(r2406,⟨67,47,47⟩),(r2407,⟨67,47,47⟩)]
theorem checked300 : fastCheckList band b300=true := by decide +kernel

def b301 : List (Rectangle × FastWitness) := [(r2408,⟨67,47,47⟩),(r2409,⟨67,47,47⟩),(r2410,⟨67,47,47⟩),(r2411,⟨67,47,47⟩),(r2412,⟨67,47,47⟩),(r2413,⟨67,47,47⟩),(r2414,⟨67,47,47⟩),(r2415,⟨67,47,47⟩)]
theorem checked301 : fastCheckList band b301=true := by decide +kernel

def b302 : List (Rectangle × FastWitness) := [(r2416,⟨67,47,47⟩),(r2417,⟨67,47,47⟩),(r2418,⟨67,47,47⟩),(r2419,⟨67,47,47⟩),(r2420,⟨67,47,47⟩),(r2421,⟨67,47,47⟩),(r2422,⟨67,47,47⟩),(r2423,⟨67,47,47⟩)]
theorem checked302 : fastCheckList band b302=true := by decide +kernel

def b303 : List (Rectangle × FastWitness) := [(r2424,⟨67,47,47⟩),(r2425,⟨67,47,47⟩),(r2426,⟨67,47,47⟩),(r2427,⟨67,47,47⟩),(r2428,⟨67,47,47⟩),(r2429,⟨67,47,47⟩),(r2430,⟨67,47,47⟩),(r2431,⟨67,47,47⟩)]
theorem checked303 : fastCheckList band b303=true := by decide +kernel

def b304 : List (Rectangle × FastWitness) := [(r2432,⟨67,47,47⟩),(r2433,⟨67,47,47⟩),(r2434,⟨67,47,47⟩),(r2435,⟨67,47,47⟩),(r2436,⟨67,47,47⟩),(r2437,⟨67,47,47⟩),(r2438,⟨67,47,47⟩),(r2439,⟨67,47,47⟩)]
theorem checked304 : fastCheckList band b304=true := by decide +kernel

def b305 : List (Rectangle × FastWitness) := [(r2440,⟨67,47,47⟩),(r2441,⟨67,47,47⟩),(r2442,⟨67,47,47⟩),(r2443,⟨67,47,47⟩),(r2444,⟨67,47,47⟩),(r2445,⟨67,47,47⟩),(r2446,⟨67,47,47⟩),(r2447,⟨67,47,47⟩)]
theorem checked305 : fastCheckList band b305=true := by decide +kernel

def b306 : List (Rectangle × FastWitness) := [(r2448,⟨67,47,47⟩),(r2449,⟨67,47,47⟩),(r2450,⟨67,47,47⟩),(r2451,⟨67,47,47⟩),(r2452,⟨67,47,47⟩),(r2453,⟨67,47,48⟩),(r2454,⟨67,47,48⟩),(r2455,⟨67,47,48⟩)]
theorem checked306 : fastCheckList band b306=true := by decide +kernel

def b307 : List (Rectangle × FastWitness) := [(r2456,⟨67,47,48⟩),(r2457,⟨67,47,48⟩),(r2458,⟨67,47,48⟩),(r2459,⟨67,48,48⟩),(r2460,⟨67,48,48⟩),(r2461,⟨67,48,48⟩),(r2462,⟨67,48,48⟩),(r2463,⟨67,48,48⟩)]
theorem checked307 : fastCheckList band b307=true := by decide +kernel

def b308 : List (Rectangle × FastWitness) := [(r2464,⟨67,48,48⟩),(r2465,⟨67,48,48⟩),(r2466,⟨67,48,48⟩),(r2467,⟨67,48,48⟩),(r2468,⟨67,48,48⟩),(r2469,⟨67,48,48⟩),(r2470,⟨67,48,48⟩),(r2471,⟨67,48,48⟩)]
theorem checked308 : fastCheckList band b308=true := by decide +kernel

def b309 : List (Rectangle × FastWitness) := [(r2472,⟨67,48,48⟩),(r2473,⟨67,48,48⟩),(r2474,⟨67,48,48⟩),(r2475,⟨67,48,48⟩),(r2476,⟨67,48,48⟩),(r2477,⟨67,48,48⟩),(r2478,⟨67,48,48⟩),(r2479,⟨67,48,48⟩)]
theorem checked309 : fastCheckList band b309=true := by decide +kernel

def b310 : List (Rectangle × FastWitness) := [(r2480,⟨67,48,48⟩),(r2481,⟨67,48,48⟩),(r2482,⟨67,48,48⟩),(r2483,⟨67,48,48⟩),(r2484,⟨67,48,48⟩),(r2485,⟨67,48,48⟩),(r2486,⟨67,48,48⟩),(r2487,⟨67,48,48⟩)]
theorem checked310 : fastCheckList band b310=true := by decide +kernel

def b311 : List (Rectangle × FastWitness) := [(r2488,⟨67,48,48⟩),(r2489,⟨67,48,48⟩),(r2490,⟨67,48,48⟩),(r2491,⟨67,48,48⟩),(r2492,⟨67,48,48⟩),(r2493,⟨67,48,48⟩),(r2494,⟨67,48,48⟩),(r2495,⟨67,48,48⟩)]
theorem checked311 : fastCheckList band b311=true := by decide +kernel

def b312 : List (Rectangle × FastWitness) := [(r2496,⟨67,48,48⟩),(r2497,⟨67,48,48⟩),(r2498,⟨67,48,48⟩),(r2499,⟨67,48,48⟩),(r2500,⟨67,48,48⟩),(r2501,⟨67,48,48⟩),(r2502,⟨67,48,48⟩),(r2503,⟨67,48,48⟩)]
theorem checked312 : fastCheckList band b312=true := by decide +kernel

def b313 : List (Rectangle × FastWitness) := [(r2504,⟨67,48,48⟩),(r2505,⟨67,48,48⟩),(r2506,⟨67,48,48⟩),(r2507,⟨67,50,50⟩),(r2508,⟨67,50,50⟩),(r2509,⟨67,50,50⟩),(r2510,⟨67,50,50⟩),(r2511,⟨67,50,50⟩)]
theorem checked313 : fastCheckList band b313=true := by decide +kernel

def b314 : List (Rectangle × FastWitness) := [(r2512,⟨67,50,50⟩),(r2513,⟨67,50,50⟩),(r2514,⟨67,50,50⟩),(r2515,⟨67,50,50⟩),(r2516,⟨67,50,50⟩),(r2517,⟨67,50,50⟩),(r2518,⟨67,50,50⟩),(r2519,⟨67,50,50⟩)]
theorem checked314 : fastCheckList band b314=true := by decide +kernel

def b315 : List (Rectangle × FastWitness) := [(r2520,⟨67,50,50⟩),(r2521,⟨67,50,50⟩),(r2522,⟨67,50,50⟩),(r2523,⟨67,50,50⟩),(r2524,⟨67,50,50⟩),(r2525,⟨67,50,50⟩),(r2526,⟨67,50,50⟩),(r2527,⟨67,50,50⟩)]
theorem checked315 : fastCheckList band b315=true := by decide +kernel

def b316 : List (Rectangle × FastWitness) := [(r2528,⟨67,50,50⟩),(r2529,⟨67,50,50⟩),(r2530,⟨67,50,50⟩),(r2531,⟨67,50,50⟩),(r2532,⟨67,50,50⟩),(r2533,⟨67,50,50⟩),(r2534,⟨67,50,50⟩),(r2535,⟨67,50,50⟩)]
theorem checked316 : fastCheckList band b316=true := by decide +kernel

def b317 : List (Rectangle × FastWitness) := [(r2536,⟨67,50,50⟩),(r2537,⟨67,50,50⟩),(r2538,⟨67,50,50⟩),(r2539,⟨67,50,50⟩),(r2540,⟨67,50,50⟩),(r2541,⟨67,50,50⟩),(r2542,⟨67,50,50⟩),(r2543,⟨67,50,50⟩)]
theorem checked317 : fastCheckList band b317=true := by decide +kernel

def b318 : List (Rectangle × FastWitness) := [(r2544,⟨67,50,50⟩),(r2545,⟨67,50,50⟩),(r2546,⟨67,50,51⟩),(r2547,⟨67,50,51⟩),(r2548,⟨67,51,51⟩),(r2549,⟨67,51,51⟩),(r2550,⟨67,51,51⟩),(r2551,⟨67,51,51⟩)]
theorem checked318 : fastCheckList band b318=true := by decide +kernel

def b319 : List (Rectangle × FastWitness) := [(r2552,⟨67,51,51⟩),(r2553,⟨67,51,51⟩),(r2554,⟨67,51,51⟩),(r2555,⟨67,51,51⟩),(r2556,⟨67,51,51⟩),(r2557,⟨67,51,51⟩),(r2558,⟨67,51,51⟩),(r2559,⟨67,51,51⟩)]
theorem checked319 : fastCheckList band b319=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


