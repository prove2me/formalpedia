-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans056
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:51:08.705985+00:00
-- url     : https://prove2.me/theorems/5767aaee-0597-498b-90eb-8bc12be79a66
-- title:
--   Endpoint22 Reach Plans056 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans056 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5445`, `ThreeBoundEndpoint22Reachable.plan5446`, `ThreeBoundEndpoint22Reachable.plan5447`, `ThreeBoundEndpoint22Reachable.plan5448`, `ThreeBoundEndpoint22Reachable.plan5449`, `ThreeBoundEndpoint22Reachable.plan5450`, `ThreeBoundEndpoint22Reachable.plan5451`, `ThreeBoundEndpoint22Reachable.plan5452`, `ThreeBoundEndpoint22Reachable.plan5453`, `ThreeBoundEndpoint22Reachable.plan5382`, `ThreeBoundEndpoint22Reachable.plan5454`, `ThreeBoundEndpoint22Reachable.plan5455`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans056.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
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
def plan5377 : Plan := .step choices182 bits843 plan3263

def plan5378 : Plan := .step choices182 bits919 plan3265

def plan5379 : Plan := .step choices182 bits920 plan3266

def plan5380 : Plan := .step choices182 bits919 plan3267

def plan5381 : Plan := .step choices182 bits849 plan3268

def plan5382 : Plan := .step choices182 bits850 plan3269

def plan5383 : Plan := .step choices182 bits849 plan3270

def plan5384 : Plan := .step choices182 bits851 plan3271

def plan5385 : Plan := .step choices182 bits850 plan3272

def plan5386 : Plan := .step choices182 bits849 plan3273

def plan5387 : Plan := .step choices182 bits848 plan3275

def plan5388 : Plan := .step choices182 bits849 plan3276

def plan5389 : Plan := .step choices182 bits848 plan3277

def plan5390 : Plan := .step choices182 bits848 plan3279

def plan5391 : Plan := .step choices182 bits849 plan3280

def plan5392 : Plan := .step choices182 bits848 plan3281

def plan5393 : Plan := .step choices183 bits922 plan3265

def plan5394 : Plan := .step choices183 bits923 plan3266

def plan5395 : Plan := .step choices183 bits922 plan3267

def plan5396 : Plan := .step choices183 bits854 plan3268

def plan5397 : Plan := .step choices183 bits855 plan3269

def plan5398 : Plan := .step choices183 bits854 plan3270

def plan5399 : Plan := .step choices183 bits856 plan3271

def plan5400 : Plan := .step choices183 bits855 plan3272

def plan5401 : Plan := .step choices183 bits854 plan3273

def plan5402 : Plan := .step choices184 bits853 plan3266

def plan5403 : Plan := .step choices185 bits921 plan3264

def plan5404 : Plan := .step choices185 bits853 plan3265

def plan5405 : Plan := .step choices185 bits854 plan3266

def plan5406 : Plan := .step choices185 bits853 plan3267

def plan5407 : Plan := .step choices185 bits852 plan3274

def plan5408 : Plan := .step choices185 bits852 plan3278

def plan5409 : Plan := .step choices188 bits853 plan3266

def plan5410 : Plan := .step choices189 bits921 plan3264

def plan5411 : Plan := .step choices189 bits853 plan3265

def plan5412 : Plan := .step choices189 bits854 plan3266

def plan5413 : Plan := .step choices189 bits853 plan3267

def plan5414 : Plan := .step choices189 bits852 plan3278

def plan5415 : Plan := .step choices192 bits1041 plan3282

def plan5416 : Plan := .step choices192 bits1052 plan3293

def plan5417 : Plan := .step choices192 bits1053 plan3296

def plan5418 : Plan := .step choices192 bits1052 plan3300

def plan5419 : Plan := .step choices192 bits1054 plan3313

def plan5420 : Plan := .step choices192 bits1055 plan3315

def plan5421 : Plan := .step choices192 bits1054 plan3316

def plan5422 : Plan := .step choices192 bits1056 plan3318

def plan5423 : Plan := .step choices192 bits1055 plan3319

def plan5424 : Plan := .step choices192 bits1054 plan3320

def plan5425 : Plan := .step choices192 bits1052 plan3329

def plan5426 : Plan := .step choices192 bits1052 plan3341

def plan5427 : Plan := .step choices193 bits1100 plan3283

def plan5428 : Plan := .step choices193 bits1103 plan3284

def plan5429 : Plan := .step choices193 bits1104 plan3285

def plan5430 : Plan := .step choices193 bits1103 plan3286

def plan5431 : Plan := .step choices193 bits1057 plan3287

def plan5432 : Plan := .step choices193 bits1059 plan3288

def plan5433 : Plan := .step choices193 bits1057 plan3289

def plan5434 : Plan := .step choices193 bits1060 plan3290

def plan5435 : Plan := .step choices193 bits1063 plan3291

def plan5436 : Plan := .step choices193 bits1060 plan3292

def plan5437 : Plan := .step choices193 bits1064 plan3293

def plan5438 : Plan := .step choices193 bits1063 plan3294

def plan5439 : Plan := .step choices193 bits1060 plan3295

def plan5440 : Plan := .step choices193 bits1065 plan3296

def plan5441 : Plan := .step choices193 bits1057 plan3297

def plan5442 : Plan := .step choices193 bits1059 plan3298

def plan5443 : Plan := .step choices193 bits1057 plan3299

def plan5444 : Plan := .step choices193 bits1064 plan3300

def plan5445 : Plan := .step choices193 bits1063 plan3301

def plan5446 : Plan := .step choices193 bits1060 plan3302

def plan5447 : Plan := .step choices193 bits1105 plan3306

def plan5448 : Plan := .step choices193 bits1106 plan3307

def plan5449 : Plan := .step choices193 bits1105 plan3308

def plan5450 : Plan := .step choices193 bits1107 plan3309

def plan5451 : Plan := .step choices193 bits1106 plan3310

def plan5452 : Plan := .step choices193 bits1105 plan3311

def plan5453 : Plan := .step choices193 bits1066 plan3312

def plan5454 : Plan := .step choices193 bits1067 plan3313

def plan5455 : Plan := .step choices193 bits1066 plan3314

def plan5456 : Plan := .step choices193 bits1068 plan3315

def plan5457 : Plan := .step choices193 bits1067 plan3316

def plan5458 : Plan := .step choices193 bits1066 plan3317

def plan5459 : Plan := .step choices193 bits1069 plan3318

def plan5460 : Plan := .step choices193 bits1068 plan3319

def plan5461 : Plan := .step choices193 bits1067 plan3320

def plan5462 : Plan := .step choices193 bits1066 plan3321

def plan5463 : Plan := .step choices193 bits1103 plan3324

def plan5464 : Plan := .step choices193 bits1060 plan3326

def plan5465 : Plan := .step choices193 bits1063 plan3327

def plan5466 : Plan := .step choices193 bits1060 plan3328

def plan5467 : Plan := .step choices193 bits1064 plan3329

def plan5468 : Plan := .step choices193 bits1063 plan3330

def plan5469 : Plan := .step choices193 bits1060 plan3331

def plan5470 : Plan := .step choices193 bits1057 plan3332

def plan5471 : Plan := .step choices193 bits1057 plan3333

def plan5472 : Plan := .step choices193 bits1103 plan3336

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


