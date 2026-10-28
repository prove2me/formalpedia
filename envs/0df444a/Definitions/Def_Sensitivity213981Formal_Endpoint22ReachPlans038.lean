-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans038
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:50:23.614746+00:00
-- url     : https://prove2.me/theorems/9e834fda-ca53-4d52-bb07-42d95354d9df
-- title:
--   Endpoint22 Reach Plans038 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans038 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3716`, `ThreeBoundEndpoint22Reachable.plan3717`, `ThreeBoundEndpoint22Reachable.plan3718`, `ThreeBoundEndpoint22Reachable.plan3719`, `ThreeBoundEndpoint22Reachable.plan3720`, `ThreeBoundEndpoint22Reachable.plan3721`, `ThreeBoundEndpoint22Reachable.plan3722`, `ThreeBoundEndpoint22Reachable.plan3723`, `ThreeBoundEndpoint22Reachable.plan3653`, `ThreeBoundEndpoint22Reachable.plan3724`, `ThreeBoundEndpoint22Reachable.plan3725`, `ThreeBoundEndpoint22Reachable.plan3726`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans038.lean, lines 1–210.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
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
def plan3649 : Plan := .step choices295 bits1425 plan1685

def plan3650 : Plan := .step choices295 bits1424 plan1686

def plan3651 : Plan := .step choices295 bits1423 plan1687

def plan3652 : Plan := .step choices297 bits900 plan1688

def plan3653 : Plan := .step choices301 bits1099 plan1689

def plan3654 : Plan := .step choices308 bits1295 plan1690

def plan3655 : Plan := .step choices318 bits1428 plan1691

def plan3656 : Plan := .step choices325 bits1561 plan1692

def plan3657 : Plan := .step choices329 bits1592 plan1693

def plan3658 : Plan := .step choices110 bits424 plan2515

def plan3659 : Plan := .step choices110 bits424 plan2518

def plan3660 : Plan := .step choices110 bits426 plan2519

def plan3661 : Plan := .step choices110 bits428 plan2520

def plan3662 : Plan := .step choices111 bits424 plan2514

def plan3663 : Plan := .step choices111 bits426 plan2515

def plan3664 : Plan := .step choices111 bits424 plan2517

def plan3665 : Plan := .step choices111 bits426 plan2518

def plan3666 : Plan := .step choices111 bits428 plan2519

def plan3667 : Plan := .step choices111 bits430 plan2520

def plan3668 : Plan := .step choices112 bits424 plan2516

def plan3669 : Plan := .step choices112 bits426 plan2517

def plan3670 : Plan := .step choices112 bits428 plan2518

def plan3671 : Plan := .step choices112 bits430 plan2519

def plan3672 : Plan := .step choices112 bits431 plan2520

def plan3673 : Plan := .step choices113 bits432 plan2520

def plan3674 : Plan := .step choices114 bits585 plan2524

def plan3675 : Plan := .step choices114 bits587 plan2526

def plan3676 : Plan := .step choices114 bits589 plan2527

def plan3677 : Plan := .step choices114 bits587 plan2528

def plan3678 : Plan := .step choices114 bits585 plan2534

def plan3679 : Plan := .step choices114 bits587 plan2538

def plan3680 : Plan := .step choices114 bits589 plan2539

def plan3681 : Plan := .step choices114 bits587 plan2540

def plan3682 : Plan := .step choices114 bits593 plan2544

def plan3683 : Plan := .step choices114 bits595 plan2545

def plan3684 : Plan := .step choices114 bits593 plan2546

def plan3685 : Plan := .step choices114 bits591 plan2547

def plan3686 : Plan := .step choices114 bits591 plan2548

def plan3687 : Plan := .step choices114 bits601 plan2550

def plan3688 : Plan := .step choices114 bits603 plan2551

def plan3689 : Plan := .step choices114 bits601 plan2552

def plan3690 : Plan := .step choices114 bits597 plan2554

def plan3691 : Plan := .step choices114 bits599 plan2555

def plan3692 : Plan := .step choices114 bits597 plan2557

def plan3693 : Plan := .step choices114 bits599 plan2558

def plan3694 : Plan := .step choices115 bits586 plan2521

def plan3695 : Plan := .step choices115 bits586 plan2522

def plan3696 : Plan := .step choices115 bits588 plan2523

def plan3697 : Plan := .step choices115 bits590 plan2524

def plan3698 : Plan := .step choices115 bits588 plan2525

def plan3699 : Plan := .step choices115 bits594 plan2526

def plan3700 : Plan := .step choices115 bits596 plan2527

def plan3701 : Plan := .step choices115 bits594 plan2528

def plan3702 : Plan := .step choices115 bits592 plan2529

def plan3703 : Plan := .step choices115 bits592 plan2530

def plan3704 : Plan := .step choices115 bits588 plan2533

def plan3705 : Plan := .step choices115 bits590 plan2534

def plan3706 : Plan := .step choices115 bits588 plan2536

def plan3707 : Plan := .step choices115 bits594 plan2538

def plan3708 : Plan := .step choices115 bits596 plan2539

def plan3709 : Plan := .step choices115 bits594 plan2540

def plan3710 : Plan := .step choices115 bits592 plan2541

def plan3711 : Plan := .step choices115 bits592 plan2542

def plan3712 : Plan := .step choices115 bits602 plan2544

def plan3713 : Plan := .step choices115 bits604 plan2545

def plan3714 : Plan := .step choices115 bits602 plan2546

def plan3715 : Plan := .step choices115 bits600 plan2547

def plan3716 : Plan := .step choices115 bits600 plan2548

def plan3717 : Plan := .step choices115 bits607 plan2550

def plan3718 : Plan := .step choices115 bits608 plan2551

def plan3719 : Plan := .step choices115 bits607 plan2552

def plan3720 : Plan := .step choices115 bits598 plan2553

def plan3721 : Plan := .step choices115 bits605 plan2554

def plan3722 : Plan := .step choices115 bits606 plan2555

def plan3723 : Plan := .step choices115 bits598 plan2556

def plan3724 : Plan := .step choices115 bits605 plan2557

def plan3725 : Plan := .step choices115 bits606 plan2558

def plan3726 : Plan := .step choices116 bits592 plan2532

def plan3727 : Plan := .step choices116 bits594 plan2533

def plan3728 : Plan := .step choices116 bits596 plan2534

def plan3729 : Plan := .step choices116 bits592 plan2535

def plan3730 : Plan := .step choices116 bits594 plan2536

def plan3731 : Plan := .step choices116 bits602 plan2538

def plan3732 : Plan := .step choices116 bits604 plan2539

def plan3733 : Plan := .step choices116 bits602 plan2540

def plan3734 : Plan := .step choices116 bits600 plan2541

def plan3735 : Plan := .step choices116 bits600 plan2542

def plan3736 : Plan := .step choices116 bits607 plan2544

def plan3737 : Plan := .step choices116 bits608 plan2545

def plan3738 : Plan := .step choices116 bits607 plan2546

def plan3739 : Plan := .step choices116 bits606 plan2547

def plan3740 : Plan := .step choices116 bits606 plan2548

def plan3741 : Plan := .step choices116 bits611 plan2550

def plan3742 : Plan := .step choices116 bits612 plan2551

def plan3743 : Plan := .step choices116 bits611 plan2552

def plan3744 : Plan := .step choices116 bits610 plan2555

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


