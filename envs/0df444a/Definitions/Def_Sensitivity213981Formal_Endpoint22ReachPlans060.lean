-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans060
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T01:57:52.221088+00:00
-- url     : https://prove2.me/theorems/aa4ae974-6a00-466d-9f15-ea89a87def5e
-- title:
--   Endpoint22 Reach Plans060 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans060 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5829`, `ThreeBoundEndpoint22Reachable.plan5830`, `ThreeBoundEndpoint22Reachable.plan5831`, `ThreeBoundEndpoint22Reachable.plan5832`, `ThreeBoundEndpoint22Reachable.plan5833`, `ThreeBoundEndpoint22Reachable.plan5834`, `ThreeBoundEndpoint22Reachable.plan5835`, `ThreeBoundEndpoint22Reachable.plan5766`, `ThreeBoundEndpoint22Reachable.plan5836`, `ThreeBoundEndpoint22Reachable.plan5837`, `ThreeBoundEndpoint22Reachable.plan5838`, `ThreeBoundEndpoint22Reachable.plan5839`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans060.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan5761 : Plan := .step choices215 bits1429 plan3497

def plan5762 : Plan := .step choices215 bits1431 plan3499

def plan5763 : Plan := .step choices215 bits1429 plan3502

def plan5764 : Plan := .step choices215 bits1430 plan3504

def plan5765 : Plan := .step choices215 bits1429 plan3505

def plan5766 : Plan := .step choices215 bits1432 plan3507

def plan5767 : Plan := .step choices215 bits1431 plan3508

def plan5768 : Plan := .step choices215 bits1430 plan3509

def plan5769 : Plan := .step choices215 bits1429 plan3510

def plan5770 : Plan := .step choices216 bits1436 plan3475

def plan5771 : Plan := .step choices216 bits1437 plan3476

def plan5772 : Plan := .step choices216 bits1436 plan3477

def plan5773 : Plan := .step choices216 bits1438 plan3478

def plan5774 : Plan := .step choices216 bits1437 plan3479

def plan5775 : Plan := .step choices216 bits1436 plan3480

def plan5776 : Plan := .step choices216 bits1439 plan3481

def plan5777 : Plan := .step choices216 bits1438 plan3482

def plan5778 : Plan := .step choices216 bits1437 plan3483

def plan5779 : Plan := .step choices216 bits1436 plan3484

def plan5780 : Plan := .step choices216 bits1440 plan3485

def plan5781 : Plan := .step choices216 bits1439 plan3507

def plan5782 : Plan := .step choices216 bits1438 plan3508

def plan5783 : Plan := .step choices216 bits1437 plan3509

def plan5784 : Plan := .step choices216 bits1436 plan3510

def plan5785 : Plan := .step choices217 bits1429 plan3437

def plan5786 : Plan := .step choices217 bits1430 plan3438

def plan5787 : Plan := .step choices217 bits1429 plan3439

def plan5788 : Plan := .step choices217 bits1435 plan3441

def plan5789 : Plan := .step choices217 bits1436 plan3443

def plan5790 : Plan := .step choices217 bits1435 plan3444

def plan5791 : Plan := .step choices217 bits1437 plan3446

def plan5792 : Plan := .step choices217 bits1436 plan3447

def plan5793 : Plan := .step choices217 bits1435 plan3448

def plan5794 : Plan := .step choices217 bits1408 plan3450

def plan5795 : Plan := .step choices217 bits1435 plan3454

def plan5796 : Plan := .step choices217 bits1408 plan3464

def plan5797 : Plan := .step choices217 bits1409 plan3467

def plan5798 : Plan := .step choices217 bits1408 plan3472

def plan5799 : Plan := .step choices217 bits1408 plan3476

def plan5800 : Plan := .step choices217 bits1409 plan3478

def plan5801 : Plan := .step choices217 bits1408 plan3479

def plan5802 : Plan := .step choices217 bits1410 plan3481

def plan5803 : Plan := .step choices217 bits1409 plan3482

def plan5804 : Plan := .step choices217 bits1408 plan3483

def plan5805 : Plan := .step choices217 bits1411 plan3485

def plan5806 : Plan := .step choices217 bits1408 plan3486

def plan5807 : Plan := .step choices217 bits1435 plan3490

def plan5808 : Plan := .step choices217 bits1408 plan3496

def plan5809 : Plan := .step choices217 bits1409 plan3499

def plan5810 : Plan := .step choices217 bits1408 plan3504

def plan5811 : Plan := .step choices217 bits1410 plan3507

def plan5812 : Plan := .step choices217 bits1409 plan3508

def plan5813 : Plan := .step choices217 bits1408 plan3509

def plan5814 : Plan := .step choices218 bits1435 plan3440

def plan5815 : Plan := .step choices218 bits1436 plan3441

def plan5816 : Plan := .step choices218 bits1435 plan3442

def plan5817 : Plan := .step choices218 bits1437 plan3443

def plan5818 : Plan := .step choices218 bits1436 plan3444

def plan5819 : Plan := .step choices218 bits1435 plan3445

def plan5820 : Plan := .step choices218 bits1438 plan3446

def plan5821 : Plan := .step choices218 bits1437 plan3447

def plan5822 : Plan := .step choices218 bits1436 plan3448

def plan5823 : Plan := .step choices218 bits1435 plan3449

def plan5824 : Plan := .step choices218 bits1434 plan3451

def plan5825 : Plan := .step choices218 bits1435 plan3452

def plan5826 : Plan := .step choices218 bits1434 plan3453

def plan5827 : Plan := .step choices218 bits1436 plan3454

def plan5828 : Plan := .step choices218 bits1435 plan3455

def plan5829 : Plan := .step choices218 bits1434 plan3456

def plan5830 : Plan := .step choices218 bits1434 plan3457

def plan5831 : Plan := .step choices218 bits1407 plan3458

def plan5832 : Plan := .step choices218 bits1408 plan3459

def plan5833 : Plan := .step choices218 bits1407 plan3460

def plan5834 : Plan := .step choices218 bits1407 plan3461

def plan5835 : Plan := .step choices218 bits1408 plan3462

def plan5836 : Plan := .step choices218 bits1407 plan3463

def plan5837 : Plan := .step choices218 bits1409 plan3464

def plan5838 : Plan := .step choices218 bits1408 plan3465

def plan5839 : Plan := .step choices218 bits1407 plan3466

def plan5840 : Plan := .step choices218 bits1410 plan3467

def plan5841 : Plan := .step choices218 bits1434 plan3468

def plan5842 : Plan := .step choices218 bits1407 plan3469

def plan5843 : Plan := .step choices218 bits1408 plan3470

def plan5844 : Plan := .step choices218 bits1407 plan3471

def plan5845 : Plan := .step choices218 bits1409 plan3472

def plan5846 : Plan := .step choices218 bits1408 plan3473

def plan5847 : Plan := .step choices218 bits1407 plan3474

def plan5848 : Plan := .step choices218 bits1408 plan3475

def plan5849 : Plan := .step choices218 bits1409 plan3476

def plan5850 : Plan := .step choices218 bits1408 plan3477

def plan5851 : Plan := .step choices218 bits1410 plan3478

def plan5852 : Plan := .step choices218 bits1409 plan3479

def plan5853 : Plan := .step choices218 bits1408 plan3480

def plan5854 : Plan := .step choices218 bits1411 plan3481

def plan5855 : Plan := .step choices218 bits1410 plan3482

def plan5856 : Plan := .step choices218 bits1409 plan3483

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


