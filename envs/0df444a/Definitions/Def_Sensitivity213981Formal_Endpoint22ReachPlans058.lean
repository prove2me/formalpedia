-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans058
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:50:33.059977+00:00
-- url     : https://prove2.me/theorems/a9ef9cd8-6029-4244-ba3f-7409ac303947
-- title:
--   Endpoint22 Reach Plans058 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans058 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5637`, `ThreeBoundEndpoint22Reachable.plan5638`, `ThreeBoundEndpoint22Reachable.plan5639`, `ThreeBoundEndpoint22Reachable.plan5640`, `ThreeBoundEndpoint22Reachable.plan5641`, `ThreeBoundEndpoint22Reachable.plan5642`, `ThreeBoundEndpoint22Reachable.plan5643`, `ThreeBoundEndpoint22Reachable.plan5574`, `ThreeBoundEndpoint22Reachable.plan5644`, `ThreeBoundEndpoint22Reachable.plan5645`, `ThreeBoundEndpoint22Reachable.plan5646`, `ThreeBoundEndpoint22Reachable.plan5647`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans058.lean, lines 1–205.

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
def plan5569 : Plan := .step choices204 bits1308 plan3367

def plan5570 : Plan := .step choices204 bits1307 plan3368

def plan5571 : Plan := .step choices204 bits1305 plan3369

def plan5572 : Plan := .step choices204 bits1304 plan3375

def plan5573 : Plan := .step choices204 bits1306 plan3377

def plan5574 : Plan := .step choices204 bits1304 plan3378

def plan5575 : Plan := .step choices204 bits1248 plan3381

def plan5576 : Plan := .step choices204 bits1251 plan3382

def plan5577 : Plan := .step choices204 bits1248 plan3383

def plan5578 : Plan := .step choices204 bits1249 plan3384

def plan5579 : Plan := .step choices204 bits1252 plan3385

def plan5580 : Plan := .step choices204 bits1249 plan3386

def plan5581 : Plan := .step choices204 bits1255 plan3387

def plan5582 : Plan := .step choices204 bits1252 plan3388

def plan5583 : Plan := .step choices204 bits1249 plan3389

def plan5584 : Plan := .step choices204 bits1258 plan3390

def plan5585 : Plan := .step choices204 bits1248 plan3392

def plan5586 : Plan := .step choices204 bits1251 plan3393

def plan5587 : Plan := .step choices204 bits1248 plan3394

def plan5588 : Plan := .step choices204 bits1255 plan3395

def plan5589 : Plan := .step choices204 bits1252 plan3396

def plan5590 : Plan := .step choices204 bits1249 plan3397

def plan5591 : Plan := .step choices204 bits1253 plan3398

def plan5592 : Plan := .step choices204 bits1256 plan3399

def plan5593 : Plan := .step choices204 bits1253 plan3400

def plan5594 : Plan := .step choices204 bits1259 plan3401

def plan5595 : Plan := .step choices204 bits1256 plan3402

def plan5596 : Plan := .step choices204 bits1253 plan3403

def plan5597 : Plan := .step choices204 bits1260 plan3404

def plan5598 : Plan := .step choices204 bits1259 plan3405

def plan5599 : Plan := .step choices204 bits1256 plan3406

def plan5600 : Plan := .step choices204 bits1253 plan3407

def plan5601 : Plan := .step choices204 bits1261 plan3408

def plan5602 : Plan := .step choices204 bits1304 plan3414

def plan5603 : Plan := .step choices204 bits1306 plan3416

def plan5604 : Plan := .step choices204 bits1304 plan3417

def plan5605 : Plan := .step choices204 bits1249 plan3419

def plan5606 : Plan := .step choices204 bits1252 plan3420

def plan5607 : Plan := .step choices204 bits1249 plan3421

def plan5608 : Plan := .step choices204 bits1255 plan3422

def plan5609 : Plan := .step choices204 bits1252 plan3423

def plan5610 : Plan := .step choices204 bits1249 plan3424

def plan5611 : Plan := .step choices204 bits1258 plan3425

def plan5612 : Plan := .step choices204 bits1248 plan3427

def plan5613 : Plan := .step choices204 bits1251 plan3428

def plan5614 : Plan := .step choices204 bits1248 plan3429

def plan5615 : Plan := .step choices204 bits1255 plan3430

def plan5616 : Plan := .step choices204 bits1252 plan3431

def plan5617 : Plan := .step choices204 bits1249 plan3432

def plan5618 : Plan := .step choices204 bits1260 plan3433

def plan5619 : Plan := .step choices204 bits1259 plan3434

def plan5620 : Plan := .step choices204 bits1256 plan3435

def plan5621 : Plan := .step choices204 bits1253 plan3436

def plan5622 : Plan := .step choices205 bits1314 plan3360

def plan5623 : Plan := .step choices205 bits1316 plan3361

def plan5624 : Plan := .step choices205 bits1314 plan3362

def plan5625 : Plan := .step choices205 bits1317 plan3363

def plan5626 : Plan := .step choices205 bits1316 plan3364

def plan5627 : Plan := .step choices205 bits1314 plan3365

def plan5628 : Plan := .step choices205 bits1318 plan3366

def plan5629 : Plan := .step choices205 bits1317 plan3367

def plan5630 : Plan := .step choices205 bits1316 plan3368

def plan5631 : Plan := .step choices205 bits1314 plan3369

def plan5632 : Plan := .step choices205 bits1268 plan3398

def plan5633 : Plan := .step choices205 bits1270 plan3399

def plan5634 : Plan := .step choices205 bits1268 plan3400

def plan5635 : Plan := .step choices205 bits1272 plan3401

def plan5636 : Plan := .step choices205 bits1270 plan3402

def plan5637 : Plan := .step choices205 bits1268 plan3403

def plan5638 : Plan := .step choices205 bits1273 plan3404

def plan5639 : Plan := .step choices205 bits1272 plan3405

def plan5640 : Plan := .step choices205 bits1270 plan3406

def plan5641 : Plan := .step choices205 bits1268 plan3407

def plan5642 : Plan := .step choices205 bits1274 plan3408

def plan5643 : Plan := .step choices205 bits1273 plan3433

def plan5644 : Plan := .step choices205 bits1272 plan3434

def plan5645 : Plan := .step choices205 bits1270 plan3435

def plan5646 : Plan := .step choices205 bits1268 plan3436

def plan5647 : Plan := .step choices206 bits1297 plan3345

def plan5648 : Plan := .step choices206 bits1240 plan3348

def plan5649 : Plan := .step choices206 bits1243 plan3350

def plan5650 : Plan := .step choices206 bits1240 plan3352

def plan5651 : Plan := .step choices206 bits1302 plan3355

def plan5652 : Plan := .step choices206 bits1303 plan3357

def plan5653 : Plan := .step choices206 bits1302 plan3358

def plan5654 : Plan := .step choices206 bits1251 plan3361

def plan5655 : Plan := .step choices206 bits1254 plan3363

def plan5656 : Plan := .step choices206 bits1251 plan3364

def plan5657 : Plan := .step choices206 bits1257 plan3366

def plan5658 : Plan := .step choices206 bits1254 plan3367

def plan5659 : Plan := .step choices206 bits1251 plan3368

def plan5660 : Plan := .step choices206 bits1250 plan3377

def plan5661 : Plan := .step choices206 bits1250 plan3416

def plan5662 : Plan := .step choices207 bits1312 plan3354

def plan5663 : Plan := .step choices207 bits1313 plan3355

def plan5664 : Plan := .step choices207 bits1312 plan3356

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


