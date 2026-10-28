-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans057
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:50:24.557992+00:00
-- url     : https://prove2.me/theorems/18676424-d2b7-4b4b-9889-611f41082ccc
-- title:
--   Endpoint22 Reach Plans057 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans057 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5540`, `ThreeBoundEndpoint22Reachable.plan5541`, `ThreeBoundEndpoint22Reachable.plan5542`, `ThreeBoundEndpoint22Reachable.plan5543`, `ThreeBoundEndpoint22Reachable.plan5544`, `ThreeBoundEndpoint22Reachable.plan5545`, `ThreeBoundEndpoint22Reachable.plan5546`, `ThreeBoundEndpoint22Reachable.plan5547`, `ThreeBoundEndpoint22Reachable.plan5548`, `ThreeBoundEndpoint22Reachable.plan5549`, `ThreeBoundEndpoint22Reachable.plan5478`, `ThreeBoundEndpoint22Reachable.plan5550`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans057.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
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
def plan5473 : Plan := .step choices193 bits1060 plan3338

def plan5474 : Plan := .step choices193 bits1063 plan3339

def plan5475 : Plan := .step choices193 bits1060 plan3340

def plan5476 : Plan := .step choices193 bits1064 plan3341

def plan5477 : Plan := .step choices193 bits1063 plan3342

def plan5478 : Plan := .step choices193 bits1060 plan3343

def plan5479 : Plan := .step choices193 bits1057 plan3344

def plan5480 : Plan := .step choices194 bits1108 plan3306

def plan5481 : Plan := .step choices194 bits1109 plan3307

def plan5482 : Plan := .step choices194 bits1108 plan3308

def plan5483 : Plan := .step choices194 bits1110 plan3309

def plan5484 : Plan := .step choices194 bits1109 plan3310

def plan5485 : Plan := .step choices194 bits1108 plan3311

def plan5486 : Plan := .step choices194 bits1070 plan3312

def plan5487 : Plan := .step choices194 bits1071 plan3313

def plan5488 : Plan := .step choices194 bits1070 plan3314

def plan5489 : Plan := .step choices194 bits1072 plan3315

def plan5490 : Plan := .step choices194 bits1071 plan3316

def plan5491 : Plan := .step choices194 bits1070 plan3317

def plan5492 : Plan := .step choices194 bits1073 plan3318

def plan5493 : Plan := .step choices194 bits1072 plan3319

def plan5494 : Plan := .step choices194 bits1071 plan3320

def plan5495 : Plan := .step choices194 bits1070 plan3321

def plan5496 : Plan := .step choices195 bits1058 plan3285

def plan5497 : Plan := .step choices195 bits1101 plan3304

def plan5498 : Plan := .step choices195 bits1061 plan3307

def plan5499 : Plan := .step choices195 bits1062 plan3309

def plan5500 : Plan := .step choices195 bits1061 plan3310

def plan5501 : Plan := .step choices196 bits1105 plan3303

def plan5502 : Plan := .step choices196 bits1106 plan3304

def plan5503 : Plan := .step choices196 bits1105 plan3305

def plan5504 : Plan := .step choices196 bits1066 plan3306

def plan5505 : Plan := .step choices196 bits1067 plan3307

def plan5506 : Plan := .step choices196 bits1066 plan3308

def plan5507 : Plan := .step choices196 bits1068 plan3309

def plan5508 : Plan := .step choices196 bits1067 plan3310

def plan5509 : Plan := .step choices196 bits1066 plan3311

def plan5510 : Plan := .step choices196 bits1102 plan3322

def plan5511 : Plan := .step choices196 bits1060 plan3323

def plan5512 : Plan := .step choices196 bits1063 plan3324

def plan5513 : Plan := .step choices196 bits1060 plan3325

def plan5514 : Plan := .step choices196 bits1102 plan3334

def plan5515 : Plan := .step choices196 bits1060 plan3335

def plan5516 : Plan := .step choices196 bits1063 plan3336

def plan5517 : Plan := .step choices196 bits1060 plan3337

def plan5518 : Plan := .step choices199 bits1058 plan3285

def plan5519 : Plan := .step choices199 bits1101 plan3304

def plan5520 : Plan := .step choices199 bits1061 plan3307

def plan5521 : Plan := .step choices199 bits1062 plan3309

def plan5522 : Plan := .step choices199 bits1061 plan3310

def plan5523 : Plan := .step choices200 bits1105 plan3303

def plan5524 : Plan := .step choices200 bits1106 plan3304

def plan5525 : Plan := .step choices200 bits1105 plan3305

def plan5526 : Plan := .step choices200 bits1066 plan3306

def plan5527 : Plan := .step choices200 bits1067 plan3307

def plan5528 : Plan := .step choices200 bits1066 plan3308

def plan5529 : Plan := .step choices200 bits1068 plan3309

def plan5530 : Plan := .step choices200 bits1067 plan3310

def plan5531 : Plan := .step choices200 bits1066 plan3311

def plan5532 : Plan := .step choices200 bits1102 plan3334

def plan5533 : Plan := .step choices200 bits1060 plan3335

def plan5534 : Plan := .step choices200 bits1063 plan3336

def plan5535 : Plan := .step choices200 bits1060 plan3337

def plan5536 : Plan := .step choices203 bits1239 plan3370

def plan5537 : Plan := .step choices203 bits1241 plan3387

def plan5538 : Plan := .step choices203 bits1244 plan3390

def plan5539 : Plan := .step choices203 bits1241 plan3395

def plan5540 : Plan := .step choices203 bits1242 plan3399

def plan5541 : Plan := .step choices203 bits1245 plan3401

def plan5542 : Plan := .step choices203 bits1242 plan3402

def plan5543 : Plan := .step choices203 bits1246 plan3404

def plan5544 : Plan := .step choices203 bits1245 plan3405

def plan5545 : Plan := .step choices203 bits1242 plan3406

def plan5546 : Plan := .step choices203 bits1247 plan3408

def plan5547 : Plan := .step choices203 bits1239 plan3409

def plan5548 : Plan := .step choices203 bits1241 plan3422

def plan5549 : Plan := .step choices203 bits1244 plan3425

def plan5550 : Plan := .step choices203 bits1241 plan3430

def plan5551 : Plan := .step choices203 bits1246 plan3433

def plan5552 : Plan := .step choices203 bits1245 plan3434

def plan5553 : Plan := .step choices203 bits1242 plan3435

def plan5554 : Plan := .step choices204 bits1298 plan3346

def plan5555 : Plan := .step choices204 bits1299 plan3347

def plan5556 : Plan := .step choices204 bits1300 plan3348

def plan5557 : Plan := .step choices204 bits1299 plan3349

def plan5558 : Plan := .step choices204 bits1301 plan3350

def plan5559 : Plan := .step choices204 bits1298 plan3351

def plan5560 : Plan := .step choices204 bits1300 plan3352

def plan5561 : Plan := .step choices204 bits1299 plan3353

def plan5562 : Plan := .step choices204 bits1305 plan3360

def plan5563 : Plan := .step choices204 bits1307 plan3361

def plan5564 : Plan := .step choices204 bits1305 plan3362

def plan5565 : Plan := .step choices204 bits1308 plan3363

def plan5566 : Plan := .step choices204 bits1307 plan3364

def plan5567 : Plan := .step choices204 bits1305 plan3365

def plan5568 : Plan := .step choices204 bits1309 plan3366

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


