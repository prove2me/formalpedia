-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans035
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:33.533344+00:00
-- url     : https://prove2.me/theorems/0a367065-ba00-4370-a30e-09e2ec9ce22f
-- title:
--   Endpoint22 Reach Plans035 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans035 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3429`, `ThreeBoundEndpoint22Reachable.plan3430`, `ThreeBoundEndpoint22Reachable.plan3431`, `ThreeBoundEndpoint22Reachable.plan3432`, `ThreeBoundEndpoint22Reachable.plan3433`, `ThreeBoundEndpoint22Reachable.plan3434`, `ThreeBoundEndpoint22Reachable.plan3435`, `ThreeBoundEndpoint22Reachable.plan3436`, `ThreeBoundEndpoint22Reachable.plan3366`, `ThreeBoundEndpoint22Reachable.plan3437`, `ThreeBoundEndpoint22Reachable.plan3438`, `ThreeBoundEndpoint22Reachable.plan3439`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans035.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
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
def plan3361 : Plan := .step choices205 bits957 plan1570

def plan3362 : Plan := .step choices205 bits955 plan1571

def plan3363 : Plan := .step choices205 bits958 plan1572

def plan3364 : Plan := .step choices205 bits957 plan1573

def plan3365 : Plan := .step choices205 bits955 plan1574

def plan3366 : Plan := .step choices205 bits959 plan1575

def plan3367 : Plan := .step choices205 bits958 plan1580

def plan3368 : Plan := .step choices205 bits957 plan1581

def plan3369 : Plan := .step choices205 bits955 plan1582

def plan3370 : Plan := .step choices206 bits883 plan1575

def plan3371 : Plan := .step choices207 bits964 plan1556

def plan3372 : Plan := .step choices207 bits965 plan1557

def plan3373 : Plan := .step choices207 bits964 plan1558

def plan3374 : Plan := .step choices207 bits953 plan1559

def plan3375 : Plan := .step choices207 bits954 plan1560

def plan3376 : Plan := .step choices207 bits953 plan1561

def plan3377 : Plan := .step choices207 bits956 plan1562

def plan3378 : Plan := .step choices207 bits954 plan1563

def plan3379 : Plan := .step choices207 bits953 plan1564

def plan3380 : Plan := .step choices207 bits952 plan1565

def plan3381 : Plan := .step choices207 bits884 plan1566

def plan3382 : Plan := .step choices207 bits886 plan1567

def plan3383 : Plan := .step choices207 bits884 plan1568

def plan3384 : Plan := .step choices207 bits885 plan1569

def plan3385 : Plan := .step choices207 bits887 plan1570

def plan3386 : Plan := .step choices207 bits885 plan1571

def plan3387 : Plan := .step choices207 bits889 plan1572

def plan3388 : Plan := .step choices207 bits887 plan1573

def plan3389 : Plan := .step choices207 bits885 plan1574

def plan3390 : Plan := .step choices207 bits891 plan1575

def plan3391 : Plan := .step choices207 bits952 plan1576

def plan3392 : Plan := .step choices207 bits884 plan1577

def plan3393 : Plan := .step choices207 bits886 plan1578

def plan3394 : Plan := .step choices207 bits884 plan1579

def plan3395 : Plan := .step choices207 bits889 plan1580

def plan3396 : Plan := .step choices207 bits887 plan1581

def plan3397 : Plan := .step choices207 bits885 plan1582

def plan3398 : Plan := .step choices208 bits888 plan1569

def plan3399 : Plan := .step choices208 bits890 plan1570

def plan3400 : Plan := .step choices208 bits888 plan1571

def plan3401 : Plan := .step choices208 bits892 plan1572

def plan3402 : Plan := .step choices208 bits890 plan1573

def plan3403 : Plan := .step choices208 bits888 plan1574

def plan3404 : Plan := .step choices208 bits893 plan1575

def plan3405 : Plan := .step choices208 bits892 plan1580

def plan3406 : Plan := .step choices208 bits890 plan1581

def plan3407 : Plan := .step choices208 bits888 plan1582

def plan3408 : Plan := .step choices209 bits894 plan1575

def plan3409 : Plan := .step choices210 bits883 plan1575

def plan3410 : Plan := .step choices211 bits964 plan1556

def plan3411 : Plan := .step choices211 bits965 plan1557

def plan3412 : Plan := .step choices211 bits964 plan1558

def plan3413 : Plan := .step choices211 bits953 plan1559

def plan3414 : Plan := .step choices211 bits954 plan1560

def plan3415 : Plan := .step choices211 bits953 plan1561

def plan3416 : Plan := .step choices211 bits956 plan1562

def plan3417 : Plan := .step choices211 bits954 plan1563

def plan3418 : Plan := .step choices211 bits953 plan1564

def plan3419 : Plan := .step choices211 bits885 plan1569

def plan3420 : Plan := .step choices211 bits887 plan1570

def plan3421 : Plan := .step choices211 bits885 plan1571

def plan3422 : Plan := .step choices211 bits889 plan1572

def plan3423 : Plan := .step choices211 bits887 plan1573

def plan3424 : Plan := .step choices211 bits885 plan1574

def plan3425 : Plan := .step choices211 bits891 plan1575

def plan3426 : Plan := .step choices211 bits952 plan1576

def plan3427 : Plan := .step choices211 bits884 plan1577

def plan3428 : Plan := .step choices211 bits886 plan1578

def plan3429 : Plan := .step choices211 bits884 plan1579

def plan3430 : Plan := .step choices211 bits889 plan1580

def plan3431 : Plan := .step choices211 bits887 plan1581

def plan3432 : Plan := .step choices211 bits885 plan1582

def plan3433 : Plan := .step choices212 bits893 plan1575

def plan3434 : Plan := .step choices212 bits892 plan1580

def plan3435 : Plan := .step choices212 bits890 plan1581

def plan3436 : Plan := .step choices212 bits888 plan1582

def plan3437 : Plan := .step choices215 bits1113 plan1596

def plan3438 : Plan := .step choices215 bits1114 plan1599

def plan3439 : Plan := .step choices215 bits1113 plan1604

def plan3440 : Plan := .step choices216 bits1116 plan1593

def plan3441 : Plan := .step choices216 bits1117 plan1594

def plan3442 : Plan := .step choices216 bits1116 plan1595

def plan3443 : Plan := .step choices216 bits1118 plan1596

def plan3444 : Plan := .step choices216 bits1117 plan1597

def plan3445 : Plan := .step choices216 bits1116 plan1598

def plan3446 : Plan := .step choices216 bits1119 plan1599

def plan3447 : Plan := .step choices216 bits1118 plan1604

def plan3448 : Plan := .step choices216 bits1117 plan1605

def plan3449 : Plan := .step choices216 bits1116 plan1606

def plan3450 : Plan := .step choices217 bits1090 plan1599

def plan3451 : Plan := .step choices218 bits1115 plan1583

def plan3452 : Plan := .step choices218 bits1116 plan1584

def plan3453 : Plan := .step choices218 bits1115 plan1585

def plan3454 : Plan := .step choices218 bits1117 plan1586

def plan3455 : Plan := .step choices218 bits1116 plan1587

def plan3456 : Plan := .step choices218 bits1115 plan1588

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


