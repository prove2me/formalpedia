-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans040
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:03.709677+00:00
-- url     : https://prove2.me/theorems/261693f3-0ca5-4b5e-8719-65abf5c17e22
-- title:
--   Endpoint22 Reach Plans040 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans040 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3909`, `ThreeBoundEndpoint22Reachable.plan3910`, `ThreeBoundEndpoint22Reachable.plan3911`, `ThreeBoundEndpoint22Reachable.plan3912`, `ThreeBoundEndpoint22Reachable.plan3913`, `ThreeBoundEndpoint22Reachable.plan3914`, `ThreeBoundEndpoint22Reachable.plan3846`, `ThreeBoundEndpoint22Reachable.plan3915`, `ThreeBoundEndpoint22Reachable.plan3916`, `ThreeBoundEndpoint22Reachable.plan3917`, `ThreeBoundEndpoint22Reachable.plan3918`, `ThreeBoundEndpoint22Reachable.plan3919`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans040.lean, lines 1–204.

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
def plan3841 : Plan := .step choices126 bits794 plan2596

def plan3842 : Plan := .step choices126 bits797 plan2597

def plan3843 : Plan := .step choices126 bits794 plan2598

def plan3844 : Plan := .step choices126 bits798 plan2599

def plan3845 : Plan := .step choices126 bits789 plan2601

def plan3846 : Plan := .step choices126 bits791 plan2602

def plan3847 : Plan := .step choices126 bits789 plan2604

def plan3848 : Plan := .step choices126 bits797 plan2605

def plan3849 : Plan := .step choices126 bits794 plan2606

def plan3850 : Plan := .step choices126 bits800 plan2610

def plan3851 : Plan := .step choices126 bits802 plan2611

def plan3852 : Plan := .step choices126 bits800 plan2612

def plan3853 : Plan := .step choices126 bits803 plan2613

def plan3854 : Plan := .step choices126 bits802 plan2614

def plan3855 : Plan := .step choices126 bits800 plan2615

def plan3856 : Plan := .step choices126 bits793 plan2617

def plan3857 : Plan := .step choices126 bits796 plan2618

def plan3858 : Plan := .step choices126 bits793 plan2619

def plan3859 : Plan := .step choices126 bits788 plan2620

def plan3860 : Plan := .step choices126 bits788 plan2621

def plan3861 : Plan := .step choices126 bits793 plan2623

def plan3862 : Plan := .step choices126 bits796 plan2624

def plan3863 : Plan := .step choices126 bits793 plan2625

def plan3864 : Plan := .step choices126 bits788 plan2626

def plan3865 : Plan := .step choices126 bits804 plan2630

def plan3866 : Plan := .step choices126 bits805 plan2631

def plan3867 : Plan := .step choices126 bits804 plan2632

def plan3868 : Plan := .step choices126 bits806 plan2633

def plan3869 : Plan := .step choices126 bits805 plan2634

def plan3870 : Plan := .step choices126 bits804 plan2635

def plan3871 : Plan := .step choices126 bits786 plan2636

def plan3872 : Plan := .step choices126 bits788 plan2638

def plan3873 : Plan := .step choices126 bits790 plan2639

def plan3874 : Plan := .step choices126 bits788 plan2640

def plan3875 : Plan := .step choices126 bits792 plan2642

def plan3876 : Plan := .step choices126 bits795 plan2643

def plan3877 : Plan := .step choices126 bits792 plan2644

def plan3878 : Plan := .step choices126 bits787 plan2645

def plan3879 : Plan := .step choices126 bits787 plan2646

def plan3880 : Plan := .step choices126 bits799 plan2648

def plan3881 : Plan := .step choices126 bits801 plan2649

def plan3882 : Plan := .step choices126 bits799 plan2650

def plan3883 : Plan := .step choices126 bits792 plan2651

def plan3884 : Plan := .step choices126 bits792 plan2652

def plan3885 : Plan := .step choices126 bits786 plan2653

def plan3886 : Plan := .step choices126 bits788 plan2655

def plan3887 : Plan := .step choices126 bits790 plan2656

def plan3888 : Plan := .step choices126 bits788 plan2657

def plan3889 : Plan := .step choices126 bits792 plan2659

def plan3890 : Plan := .step choices126 bits795 plan2660

def plan3891 : Plan := .step choices126 bits792 plan2661

def plan3892 : Plan := .step choices126 bits787 plan2662

def plan3893 : Plan := .step choices126 bits787 plan2663

def plan3894 : Plan := .step choices126 bits799 plan2665

def plan3895 : Plan := .step choices126 bits801 plan2666

def plan3896 : Plan := .step choices126 bits799 plan2667

def plan3897 : Plan := .step choices126 bits792 plan2668

def plan3898 : Plan := .step choices127 bits809 plan2591

def plan3899 : Plan := .step choices127 bits814 plan2592

def plan3900 : Plan := .step choices127 bits816 plan2593

def plan3901 : Plan := .step choices127 bits809 plan2594

def plan3902 : Plan := .step choices127 bits814 plan2595

def plan3903 : Plan := .step choices127 bits820 plan2596

def plan3904 : Plan := .step choices127 bits823 plan2597

def plan3905 : Plan := .step choices127 bits820 plan2598

def plan3906 : Plan := .step choices127 bits824 plan2599

def plan3907 : Plan := .step choices127 bits814 plan2601

def plan3908 : Plan := .step choices127 bits816 plan2602

def plan3909 : Plan := .step choices127 bits809 plan2603

def plan3910 : Plan := .step choices127 bits814 plan2604

def plan3911 : Plan := .step choices127 bits823 plan2605

def plan3912 : Plan := .step choices127 bits820 plan2606

def plan3913 : Plan := .step choices127 bits827 plan2610

def plan3914 : Plan := .step choices127 bits831 plan2611

def plan3915 : Plan := .step choices127 bits827 plan2612

def plan3916 : Plan := .step choices127 bits832 plan2613

def plan3917 : Plan := .step choices127 bits831 plan2614

def plan3918 : Plan := .step choices127 bits827 plan2615

def plan3919 : Plan := .step choices127 bits819 plan2617

def plan3920 : Plan := .step choices127 bits822 plan2618

def plan3921 : Plan := .step choices127 bits819 plan2619

def plan3922 : Plan := .step choices127 bits813 plan2620

def plan3923 : Plan := .step choices127 bits813 plan2621

def plan3924 : Plan := .step choices127 bits819 plan2623

def plan3925 : Plan := .step choices127 bits822 plan2624

def plan3926 : Plan := .step choices127 bits819 plan2625

def plan3927 : Plan := .step choices127 bits813 plan2626

def plan3928 : Plan := .step choices127 bits834 plan2630

def plan3929 : Plan := .step choices127 bits838 plan2631

def plan3930 : Plan := .step choices127 bits834 plan2632

def plan3931 : Plan := .step choices127 bits839 plan2633

def plan3932 : Plan := .step choices127 bits838 plan2634

def plan3933 : Plan := .step choices127 bits834 plan2635

def plan3934 : Plan := .step choices127 bits826 plan2648

def plan3935 : Plan := .step choices127 bits830 plan2649

def plan3936 : Plan := .step choices127 bits826 plan2650

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


