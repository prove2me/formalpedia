-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans025
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans025
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:48.857055+00:00
-- url     : https://prove2.me/theorems/a65fd3c1-c52e-404e-b560-53f8c2129283
-- title:
--   Endpoint22 Reach Plans025 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans025 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2470`, `ThreeBoundEndpoint22Reachable.plan2471`, `ThreeBoundEndpoint22Reachable.plan2472`, `ThreeBoundEndpoint22Reachable.plan2406`, `ThreeBoundEndpoint22Reachable.plan2473`, `ThreeBoundEndpoint22Reachable.plan2474`, `ThreeBoundEndpoint22Reachable.plan2475`, `ThreeBoundEndpoint22Reachable.plan2476`, `ThreeBoundEndpoint22Reachable.plan2477`, `ThreeBoundEndpoint22Reachable.plan2478`, `ThreeBoundEndpoint22Reachable.plan2479`, `ThreeBoundEndpoint22Reachable.plan2480`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans025.lean, lines 1–203.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
def plan2401 : Plan := .step choices104 bits860 plan1204

def plan2402 : Plan := .step choices104 bits859 plan1205

def plan2403 : Plan := .step choices104 bits860 plan1206

def plan2404 : Plan := .step choices104 bits861 plan1207

def plan2405 : Plan := .step choices104 bits861 plan1208

def plan2406 : Plan := .step choices104 bits862 plan1209

def plan2407 : Plan := .step choices104 bits862 plan1210

def plan2408 : Plan := .step choices104 bits862 plan1211

def plan2409 : Plan := .step choices104 bits862 plan1212

def plan2410 : Plan := .step choices104 bits862 plan1213

def plan2411 : Plan := .step choices104 bits862 plan1214

def plan2412 : Plan := .step choices104 bits862 plan1215

def plan2413 : Plan := .step choices104 bits861 plan1234

def plan2414 : Plan := .step choices104 bits861 plan1235

def plan2415 : Plan := .step choices104 bits861 plan1236

def plan2416 : Plan := .step choices104 bits861 plan1237

def plan2417 : Plan := .step choices104 bits860 plan1238

def plan2418 : Plan := .step choices104 bits860 plan1239

def plan2419 : Plan := .step choices104 bits859 plan1240

def plan2420 : Plan := .step choices104 bits860 plan1241

def plan2421 : Plan := .step choices104 bits861 plan1242

def plan2422 : Plan := .step choices104 bits861 plan1243

def plan2423 : Plan := .step choices104 bits862 plan1244

def plan2424 : Plan := .step choices104 bits862 plan1245

def plan2425 : Plan := .step choices104 bits862 plan1246

def plan2426 : Plan := .step choices105 bits863 plan1209

def plan2427 : Plan := .step choices105 bits863 plan1210

def plan2428 : Plan := .step choices105 bits863 plan1211

def plan2429 : Plan := .step choices105 bits863 plan1212

def plan2430 : Plan := .step choices105 bits863 plan1213

def plan2431 : Plan := .step choices105 bits863 plan1214

def plan2432 : Plan := .step choices105 bits863 plan1215

def plan2433 : Plan := .step choices105 bits863 plan1244

def plan2434 : Plan := .step choices105 bits863 plan1245

def plan2435 : Plan := .step choices105 bits863 plan1246

def plan2436 : Plan := .step choices106 bits863 plan1215

def plan2437 : Plan := .step choices107 bits858 plan1194

def plan2438 : Plan := .step choices107 bits859 plan1195

def plan2439 : Plan := .step choices107 bits859 plan1196

def plan2440 : Plan := .step choices107 bits858 plan1197

def plan2441 : Plan := .step choices107 bits859 plan1198

def plan2442 : Plan := .step choices107 bits860 plan1199

def plan2443 : Plan := .step choices107 bits860 plan1200

def plan2444 : Plan := .step choices107 bits860 plan1201

def plan2445 : Plan := .step choices107 bits860 plan1202

def plan2446 : Plan := .step choices107 bits859 plan1203

def plan2447 : Plan := .step choices107 bits859 plan1204

def plan2448 : Plan := .step choices107 bits858 plan1205

def plan2449 : Plan := .step choices107 bits859 plan1206

def plan2450 : Plan := .step choices107 bits860 plan1207

def plan2451 : Plan := .step choices107 bits860 plan1208

def plan2452 : Plan := .step choices107 bits861 plan1209

def plan2453 : Plan := .step choices107 bits861 plan1210

def plan2454 : Plan := .step choices107 bits861 plan1211

def plan2455 : Plan := .step choices107 bits861 plan1212

def plan2456 : Plan := .step choices107 bits861 plan1213

def plan2457 : Plan := .step choices107 bits861 plan1214

def plan2458 : Plan := .step choices107 bits861 plan1215

def plan2459 : Plan := .step choices107 bits857 plan1216

def plan2460 : Plan := .step choices107 bits858 plan1217

def plan2461 : Plan := .step choices107 bits858 plan1218

def plan2462 : Plan := .step choices107 bits857 plan1219

def plan2463 : Plan := .step choices107 bits858 plan1220

def plan2464 : Plan := .step choices107 bits859 plan1221

def plan2465 : Plan := .step choices107 bits859 plan1222

def plan2466 : Plan := .step choices107 bits859 plan1223

def plan2467 : Plan := .step choices107 bits859 plan1224

def plan2468 : Plan := .step choices107 bits857 plan1225

def plan2469 : Plan := .step choices107 bits857 plan1226

def plan2470 : Plan := .step choices107 bits857 plan1227

def plan2471 : Plan := .step choices107 bits858 plan1228

def plan2472 : Plan := .step choices107 bits858 plan1229

def plan2473 : Plan := .step choices107 bits857 plan1230

def plan2474 : Plan := .step choices107 bits858 plan1231

def plan2475 : Plan := .step choices107 bits859 plan1232

def plan2476 : Plan := .step choices107 bits859 plan1233

def plan2477 : Plan := .step choices107 bits860 plan1234

def plan2478 : Plan := .step choices107 bits860 plan1235

def plan2479 : Plan := .step choices107 bits860 plan1236

def plan2480 : Plan := .step choices107 bits860 plan1237

def plan2481 : Plan := .step choices107 bits859 plan1238

def plan2482 : Plan := .step choices107 bits859 plan1239

def plan2483 : Plan := .step choices107 bits858 plan1240

def plan2484 : Plan := .step choices107 bits859 plan1241

def plan2485 : Plan := .step choices107 bits860 plan1242

def plan2486 : Plan := .step choices107 bits860 plan1243

def plan2487 : Plan := .step choices107 bits861 plan1244

def plan2488 : Plan := .step choices107 bits861 plan1245

def plan2489 : Plan := .step choices107 bits861 plan1246

def plan2490 : Plan := .step choices108 bits862 plan1209

def plan2491 : Plan := .step choices108 bits862 plan1210

def plan2492 : Plan := .step choices108 bits862 plan1211

def plan2493 : Plan := .step choices108 bits862 plan1212

def plan2494 : Plan := .step choices108 bits862 plan1213

def plan2495 : Plan := .step choices108 bits862 plan1214

def plan2496 : Plan := .step choices108 bits862 plan1215

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


