-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans039
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:48:40.667032+00:00
-- url     : https://prove2.me/theorems/842e41c4-7714-4e0a-ac08-0ac1bdb6ad0f
-- title:
--   Endpoint22 Reach Plans039 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans039 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3813`, `ThreeBoundEndpoint22Reachable.plan3814`, `ThreeBoundEndpoint22Reachable.plan3815`, `ThreeBoundEndpoint22Reachable.plan3816`, `ThreeBoundEndpoint22Reachable.plan3817`, `ThreeBoundEndpoint22Reachable.plan3818`, `ThreeBoundEndpoint22Reachable.plan3819`, `ThreeBoundEndpoint22Reachable.plan3820`, `ThreeBoundEndpoint22Reachable.plan3821`, `ThreeBoundEndpoint22Reachable.plan3750`, `ThreeBoundEndpoint22Reachable.plan3822`, `ThreeBoundEndpoint22Reachable.plan3823`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans039.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
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
def plan3745 : Plan := .step choices116 bits610 plan2558

def plan3746 : Plan := .step choices117 bits616 plan2550

def plan3747 : Plan := .step choices117 bits617 plan2551

def plan3748 : Plan := .step choices117 bits616 plan2552

def plan3749 : Plan := .step choices118 bits598 plan2531

def plan3750 : Plan := .step choices118 bits605 plan2537

def plan3751 : Plan := .step choices118 bits609 plan2543

def plan3752 : Plan := .step choices118 bits614 plan2549

def plan3753 : Plan := .step choices119 bits615 plan2549

def plan3754 : Plan := .step choices122 bits598 plan2531

def plan3755 : Plan := .step choices122 bits605 plan2537

def plan3756 : Plan := .step choices122 bits609 plan2543

def plan3757 : Plan := .step choices122 bits614 plan2549

def plan3758 : Plan := .step choices123 bits615 plan2549

def plan3759 : Plan := .step choices125 bits764 plan2564

def plan3760 : Plan := .step choices125 bits765 plan2566

def plan3761 : Plan := .step choices125 bits764 plan2568

def plan3762 : Plan := .step choices125 bits766 plan2570

def plan3763 : Plan := .step choices125 bits767 plan2571

def plan3764 : Plan := .step choices125 bits766 plan2572

def plan3765 : Plan := .step choices125 bits768 plan2573

def plan3766 : Plan := .step choices125 bits767 plan2574

def plan3767 : Plan := .step choices125 bits766 plan2575

def plan3768 : Plan := .step choices125 bits763 plan2578

def plan3769 : Plan := .step choices125 bits763 plan2582

def plan3770 : Plan := .step choices125 bits770 plan2593

def plan3771 : Plan := .step choices125 bits773 plan2596

def plan3772 : Plan := .step choices125 bits776 plan2597

def plan3773 : Plan := .step choices125 bits773 plan2598

def plan3774 : Plan := .step choices125 bits777 plan2599

def plan3775 : Plan := .step choices125 bits770 plan2602

def plan3776 : Plan := .step choices125 bits776 plan2605

def plan3777 : Plan := .step choices125 bits773 plan2606

def plan3778 : Plan := .step choices125 bits779 plan2610

def plan3779 : Plan := .step choices125 bits781 plan2611

def plan3780 : Plan := .step choices125 bits779 plan2612

def plan3781 : Plan := .step choices125 bits782 plan2613

def plan3782 : Plan := .step choices125 bits781 plan2614

def plan3783 : Plan := .step choices125 bits779 plan2615

def plan3784 : Plan := .step choices125 bits772 plan2617

def plan3785 : Plan := .step choices125 bits775 plan2618

def plan3786 : Plan := .step choices125 bits772 plan2619

def plan3787 : Plan := .step choices125 bits772 plan2623

def plan3788 : Plan := .step choices125 bits775 plan2624

def plan3789 : Plan := .step choices125 bits772 plan2625

def plan3790 : Plan := .step choices125 bits783 plan2630

def plan3791 : Plan := .step choices125 bits784 plan2631

def plan3792 : Plan := .step choices125 bits783 plan2632

def plan3793 : Plan := .step choices125 bits785 plan2633

def plan3794 : Plan := .step choices125 bits784 plan2634

def plan3795 : Plan := .step choices125 bits783 plan2635

def plan3796 : Plan := .step choices125 bits769 plan2639

def plan3797 : Plan := .step choices125 bits771 plan2642

def plan3798 : Plan := .step choices125 bits774 plan2643

def plan3799 : Plan := .step choices125 bits771 plan2644

def plan3800 : Plan := .step choices125 bits778 plan2648

def plan3801 : Plan := .step choices125 bits780 plan2649

def plan3802 : Plan := .step choices125 bits778 plan2650

def plan3803 : Plan := .step choices125 bits771 plan2651

def plan3804 : Plan := .step choices125 bits771 plan2652

def plan3805 : Plan := .step choices125 bits769 plan2656

def plan3806 : Plan := .step choices125 bits771 plan2659

def plan3807 : Plan := .step choices125 bits774 plan2660

def plan3808 : Plan := .step choices125 bits771 plan2661

def plan3809 : Plan := .step choices125 bits778 plan2665

def plan3810 : Plan := .step choices125 bits780 plan2666

def plan3811 : Plan := .step choices125 bits778 plan2667

def plan3812 : Plan := .step choices125 bits771 plan2668

def plan3813 : Plan := .step choices126 bits764 plan2559

def plan3814 : Plan := .step choices126 bits765 plan2560

def plan3815 : Plan := .step choices126 bits764 plan2561

def plan3816 : Plan := .step choices126 bits770 plan2562

def plan3817 : Plan := .step choices126 bits773 plan2563

def plan3818 : Plan := .step choices126 bits776 plan2564

def plan3819 : Plan := .step choices126 bits773 plan2565

def plan3820 : Plan := .step choices126 bits777 plan2566

def plan3821 : Plan := .step choices126 bits770 plan2567

def plan3822 : Plan := .step choices126 bits776 plan2568

def plan3823 : Plan := .step choices126 bits773 plan2569

def plan3824 : Plan := .step choices126 bits779 plan2570

def plan3825 : Plan := .step choices126 bits781 plan2571

def plan3826 : Plan := .step choices126 bits779 plan2572

def plan3827 : Plan := .step choices126 bits782 plan2573

def plan3828 : Plan := .step choices126 bits781 plan2574

def plan3829 : Plan := .step choices126 bits779 plan2575

def plan3830 : Plan := .step choices126 bits769 plan2576

def plan3831 : Plan := .step choices126 bits772 plan2577

def plan3832 : Plan := .step choices126 bits775 plan2578

def plan3833 : Plan := .step choices126 bits772 plan2579

def plan3834 : Plan := .step choices126 bits769 plan2580

def plan3835 : Plan := .step choices126 bits772 plan2581

def plan3836 : Plan := .step choices126 bits775 plan2582

def plan3837 : Plan := .step choices126 bits772 plan2583

def plan3838 : Plan := .step choices126 bits789 plan2592

def plan3839 : Plan := .step choices126 bits791 plan2593

def plan3840 : Plan := .step choices126 bits789 plan2595

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


