-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans024
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans024
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:54.971623+00:00
-- url     : https://prove2.me/theorems/835defd5-d8b7-4eba-afde-f1d71e38d3f9
-- title:
--   Endpoint22 Reach Plans024 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans024 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2373`, `ThreeBoundEndpoint22Reachable.plan2374`, `ThreeBoundEndpoint22Reachable.plan2375`, `ThreeBoundEndpoint22Reachable.plan2376`, `ThreeBoundEndpoint22Reachable.plan2377`, `ThreeBoundEndpoint22Reachable.plan2378`, `ThreeBoundEndpoint22Reachable.plan2379`, `ThreeBoundEndpoint22Reachable.plan2380`, `ThreeBoundEndpoint22Reachable.plan2310`, `ThreeBoundEndpoint22Reachable.plan2381`, `ThreeBoundEndpoint22Reachable.plan2382`, `ThreeBoundEndpoint22Reachable.plan2383`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans024.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
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
def plan2305 : Plan := .step choices100 bits668 plan1158

def plan2306 : Plan := .step choices100 bits667 plan1163

def plan2307 : Plan := .step choices101 bits672 plan1061

def plan2308 : Plan := .step choices101 bits672 plan1062

def plan2309 : Plan := .step choices101 bits672 plan1063

def plan2310 : Plan := .step choices101 bits672 plan1064

def plan2311 : Plan := .step choices101 bits672 plan1065

def plan2312 : Plan := .step choices101 bits672 plan1066

def plan2313 : Plan := .step choices101 bits671 plan1156

def plan2314 : Plan := .step choices101 bits671 plan1157

def plan2315 : Plan := .step choices101 bits671 plan1158

def plan2316 : Plan := .step choices101 bits670 plan1163

def plan2317 : Plan := .step choices103 bits857 plan1173

def plan2318 : Plan := .step choices103 bits857 plan1174

def plan2319 : Plan := .step choices103 bits857 plan1175

def plan2320 : Plan := .step choices103 bits857 plan1176

def plan2321 : Plan := .step choices103 bits858 plan1177

def plan2322 : Plan := .step choices103 bits858 plan1178

def plan2323 : Plan := .step choices103 bits857 plan1179

def plan2324 : Plan := .step choices103 bits858 plan1180

def plan2325 : Plan := .step choices103 bits859 plan1181

def plan2326 : Plan := .step choices103 bits859 plan1182

def plan2327 : Plan := .step choices103 bits859 plan1183

def plan2328 : Plan := .step choices103 bits859 plan1184

def plan2329 : Plan := .step choices103 bits857 plan1185

def plan2330 : Plan := .step choices103 bits857 plan1186

def plan2331 : Plan := .step choices103 bits857 plan1187

def plan2332 : Plan := .step choices103 bits858 plan1188

def plan2333 : Plan := .step choices103 bits858 plan1189

def plan2334 : Plan := .step choices103 bits857 plan1190

def plan2335 : Plan := .step choices103 bits858 plan1191

def plan2336 : Plan := .step choices103 bits859 plan1192

def plan2337 : Plan := .step choices103 bits859 plan1193

def plan2338 : Plan := .step choices103 bits858 plan1194

def plan2339 : Plan := .step choices103 bits859 plan1195

def plan2340 : Plan := .step choices103 bits859 plan1196

def plan2341 : Plan := .step choices103 bits858 plan1197

def plan2342 : Plan := .step choices103 bits859 plan1198

def plan2343 : Plan := .step choices103 bits860 plan1199

def plan2344 : Plan := .step choices103 bits860 plan1200

def plan2345 : Plan := .step choices103 bits860 plan1201

def plan2346 : Plan := .step choices103 bits860 plan1202

def plan2347 : Plan := .step choices103 bits859 plan1203

def plan2348 : Plan := .step choices103 bits859 plan1204

def plan2349 : Plan := .step choices103 bits858 plan1205

def plan2350 : Plan := .step choices103 bits859 plan1206

def plan2351 : Plan := .step choices103 bits860 plan1207

def plan2352 : Plan := .step choices103 bits860 plan1208

def plan2353 : Plan := .step choices103 bits861 plan1209

def plan2354 : Plan := .step choices103 bits861 plan1210

def plan2355 : Plan := .step choices103 bits861 plan1211

def plan2356 : Plan := .step choices103 bits861 plan1212

def plan2357 : Plan := .step choices103 bits861 plan1213

def plan2358 : Plan := .step choices103 bits861 plan1214

def plan2359 : Plan := .step choices103 bits861 plan1215

def plan2360 : Plan := .step choices103 bits857 plan1216

def plan2361 : Plan := .step choices103 bits858 plan1217

def plan2362 : Plan := .step choices103 bits858 plan1218

def plan2363 : Plan := .step choices103 bits857 plan1219

def plan2364 : Plan := .step choices103 bits858 plan1220

def plan2365 : Plan := .step choices103 bits859 plan1221

def plan2366 : Plan := .step choices103 bits859 plan1222

def plan2367 : Plan := .step choices103 bits859 plan1223

def plan2368 : Plan := .step choices103 bits859 plan1224

def plan2369 : Plan := .step choices103 bits857 plan1225

def plan2370 : Plan := .step choices103 bits857 plan1226

def plan2371 : Plan := .step choices103 bits857 plan1227

def plan2372 : Plan := .step choices103 bits858 plan1228

def plan2373 : Plan := .step choices103 bits858 plan1229

def plan2374 : Plan := .step choices103 bits857 plan1230

def plan2375 : Plan := .step choices103 bits858 plan1231

def plan2376 : Plan := .step choices103 bits859 plan1232

def plan2377 : Plan := .step choices103 bits859 plan1233

def plan2378 : Plan := .step choices103 bits860 plan1234

def plan2379 : Plan := .step choices103 bits860 plan1235

def plan2380 : Plan := .step choices103 bits860 plan1236

def plan2381 : Plan := .step choices103 bits860 plan1237

def plan2382 : Plan := .step choices103 bits859 plan1238

def plan2383 : Plan := .step choices103 bits859 plan1239

def plan2384 : Plan := .step choices103 bits858 plan1240

def plan2385 : Plan := .step choices103 bits859 plan1241

def plan2386 : Plan := .step choices103 bits860 plan1242

def plan2387 : Plan := .step choices103 bits860 plan1243

def plan2388 : Plan := .step choices103 bits861 plan1244

def plan2389 : Plan := .step choices103 bits861 plan1245

def plan2390 : Plan := .step choices103 bits861 plan1246

def plan2391 : Plan := .step choices104 bits859 plan1194

def plan2392 : Plan := .step choices104 bits860 plan1195

def plan2393 : Plan := .step choices104 bits860 plan1196

def plan2394 : Plan := .step choices104 bits859 plan1197

def plan2395 : Plan := .step choices104 bits860 plan1198

def plan2396 : Plan := .step choices104 bits861 plan1199

def plan2397 : Plan := .step choices104 bits861 plan1200

def plan2398 : Plan := .step choices104 bits861 plan1201

def plan2399 : Plan := .step choices104 bits861 plan1202

def plan2400 : Plan := .step choices104 bits860 plan1203

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


