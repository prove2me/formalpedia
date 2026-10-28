-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans059
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T01:58:08.413327+00:00
-- url     : https://prove2.me/theorems/34b5cde1-ce67-4ccf-b819-39e1cc1f6442
-- title:
--   Endpoint22 Reach Plans059 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans059 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5732`, `ThreeBoundEndpoint22Reachable.plan5733`, `ThreeBoundEndpoint22Reachable.plan5669`, `ThreeBoundEndpoint22Reachable.plan5734`, `ThreeBoundEndpoint22Reachable.plan5735`, `ThreeBoundEndpoint22Reachable.plan5736`, `ThreeBoundEndpoint22Reachable.plan5737`, `ThreeBoundEndpoint22Reachable.plan5738`, `ThreeBoundEndpoint22Reachable.plan5739`, `ThreeBoundEndpoint22Reachable.plan5740`, `ThreeBoundEndpoint22Reachable.plan5741`, `ThreeBoundEndpoint22Reachable.plan5742`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans059.lean, lines 1–207.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
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
def plan5665 : Plan := .step choices207 bits1315 plan3357

def plan5666 : Plan := .step choices207 bits1313 plan3358

def plan5667 : Plan := .step choices207 bits1312 plan3359

def plan5668 : Plan := .step choices207 bits1265 plan3360

def plan5669 : Plan := .step choices207 bits1267 plan3361

def plan5670 : Plan := .step choices207 bits1265 plan3362

def plan5671 : Plan := .step choices207 bits1269 plan3363

def plan5672 : Plan := .step choices207 bits1267 plan3364

def plan5673 : Plan := .step choices207 bits1265 plan3365

def plan5674 : Plan := .step choices207 bits1271 plan3366

def plan5675 : Plan := .step choices207 bits1269 plan3367

def plan5676 : Plan := .step choices207 bits1267 plan3368

def plan5677 : Plan := .step choices207 bits1265 plan3369

def plan5678 : Plan := .step choices207 bits1310 plan3371

def plan5679 : Plan := .step choices207 bits1311 plan3372

def plan5680 : Plan := .step choices207 bits1310 plan3373

def plan5681 : Plan := .step choices207 bits1263 plan3374

def plan5682 : Plan := .step choices207 bits1264 plan3375

def plan5683 : Plan := .step choices207 bits1263 plan3376

def plan5684 : Plan := .step choices207 bits1266 plan3377

def plan5685 : Plan := .step choices207 bits1264 plan3378

def plan5686 : Plan := .step choices207 bits1263 plan3379

def plan5687 : Plan := .step choices207 bits1262 plan3380

def plan5688 : Plan := .step choices207 bits1262 plan3391

def plan5689 : Plan := .step choices207 bits1310 plan3410

def plan5690 : Plan := .step choices207 bits1311 plan3411

def plan5691 : Plan := .step choices207 bits1310 plan3412

def plan5692 : Plan := .step choices207 bits1263 plan3413

def plan5693 : Plan := .step choices207 bits1264 plan3414

def plan5694 : Plan := .step choices207 bits1263 plan3415

def plan5695 : Plan := .step choices207 bits1266 plan3416

def plan5696 : Plan := .step choices207 bits1264 plan3417

def plan5697 : Plan := .step choices207 bits1263 plan3418

def plan5698 : Plan := .step choices207 bits1262 plan3426

def plan5699 : Plan := .step choices210 bits1297 plan3345

def plan5700 : Plan := .step choices210 bits1240 plan3348

def plan5701 : Plan := .step choices210 bits1243 plan3350

def plan5702 : Plan := .step choices210 bits1240 plan3352

def plan5703 : Plan := .step choices210 bits1302 plan3355

def plan5704 : Plan := .step choices210 bits1303 plan3357

def plan5705 : Plan := .step choices210 bits1302 plan3358

def plan5706 : Plan := .step choices210 bits1251 plan3361

def plan5707 : Plan := .step choices210 bits1254 plan3363

def plan5708 : Plan := .step choices210 bits1251 plan3364

def plan5709 : Plan := .step choices210 bits1257 plan3366

def plan5710 : Plan := .step choices210 bits1254 plan3367

def plan5711 : Plan := .step choices210 bits1251 plan3368

def plan5712 : Plan := .step choices210 bits1250 plan3377

def plan5713 : Plan := .step choices210 bits1250 plan3416

def plan5714 : Plan := .step choices211 bits1312 plan3354

def plan5715 : Plan := .step choices211 bits1313 plan3355

def plan5716 : Plan := .step choices211 bits1312 plan3356

def plan5717 : Plan := .step choices211 bits1315 plan3357

def plan5718 : Plan := .step choices211 bits1313 plan3358

def plan5719 : Plan := .step choices211 bits1312 plan3359

def plan5720 : Plan := .step choices211 bits1265 plan3360

def plan5721 : Plan := .step choices211 bits1267 plan3361

def plan5722 : Plan := .step choices211 bits1265 plan3362

def plan5723 : Plan := .step choices211 bits1269 plan3363

def plan5724 : Plan := .step choices211 bits1267 plan3364

def plan5725 : Plan := .step choices211 bits1265 plan3365

def plan5726 : Plan := .step choices211 bits1271 plan3366

def plan5727 : Plan := .step choices211 bits1269 plan3367

def plan5728 : Plan := .step choices211 bits1267 plan3368

def plan5729 : Plan := .step choices211 bits1265 plan3369

def plan5730 : Plan := .step choices211 bits1310 plan3410

def plan5731 : Plan := .step choices211 bits1311 plan3411

def plan5732 : Plan := .step choices211 bits1310 plan3412

def plan5733 : Plan := .step choices211 bits1263 plan3413

def plan5734 : Plan := .step choices211 bits1264 plan3414

def plan5735 : Plan := .step choices211 bits1263 plan3415

def plan5736 : Plan := .step choices211 bits1266 plan3416

def plan5737 : Plan := .step choices211 bits1264 plan3417

def plan5738 : Plan := .step choices211 bits1263 plan3418

def plan5739 : Plan := .step choices211 bits1262 plan3426

def plan5740 : Plan := .step choices215 bits1429 plan3459

def plan5741 : Plan := .step choices215 bits1429 plan3462

def plan5742 : Plan := .step choices215 bits1430 plan3464

def plan5743 : Plan := .step choices215 bits1429 plan3465

def plan5744 : Plan := .step choices215 bits1431 plan3467

def plan5745 : Plan := .step choices215 bits1429 plan3470

def plan5746 : Plan := .step choices215 bits1430 plan3472

def plan5747 : Plan := .step choices215 bits1429 plan3473

def plan5748 : Plan := .step choices215 bits1429 plan3475

def plan5749 : Plan := .step choices215 bits1430 plan3476

def plan5750 : Plan := .step choices215 bits1429 plan3477

def plan5751 : Plan := .step choices215 bits1431 plan3478

def plan5752 : Plan := .step choices215 bits1430 plan3479

def plan5753 : Plan := .step choices215 bits1429 plan3480

def plan5754 : Plan := .step choices215 bits1432 plan3481

def plan5755 : Plan := .step choices215 bits1431 plan3482

def plan5756 : Plan := .step choices215 bits1430 plan3483

def plan5757 : Plan := .step choices215 bits1429 plan3484

def plan5758 : Plan := .step choices215 bits1433 plan3485

def plan5759 : Plan := .step choices215 bits1429 plan3494

def plan5760 : Plan := .step choices215 bits1430 plan3496

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


