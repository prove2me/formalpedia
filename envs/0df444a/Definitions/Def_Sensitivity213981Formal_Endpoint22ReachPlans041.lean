-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans041
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:48:49.660978+00:00
-- url     : https://prove2.me/theorems/9c3134e2-7ba6-419a-bd29-182fecb91b53
-- title:
--   Endpoint22 Reach Plans041 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans041 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4005`, `ThreeBoundEndpoint22Reachable.plan4006`, `ThreeBoundEndpoint22Reachable.plan4007`, `ThreeBoundEndpoint22Reachable.plan4008`, `ThreeBoundEndpoint22Reachable.plan4009`, `ThreeBoundEndpoint22Reachable.plan4010`, `ThreeBoundEndpoint22Reachable.plan4011`, `ThreeBoundEndpoint22Reachable.plan4012`, `ThreeBoundEndpoint22Reachable.plan4013`, `ThreeBoundEndpoint22Reachable.plan4014`, `ThreeBoundEndpoint22Reachable.plan3942`, `ThreeBoundEndpoint22Reachable.plan4015`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans041.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
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
def plan3937 : Plan := .step choices127 bits818 plan2651

def plan3938 : Plan := .step choices127 bits818 plan2652

def plan3939 : Plan := .step choices127 bits826 plan2665

def plan3940 : Plan := .step choices127 bits830 plan2666

def plan3941 : Plan := .step choices127 bits826 plan2667

def plan3942 : Plan := .step choices127 bits818 plan2668

def plan3943 : Plan := .step choices128 bits840 plan2630

def plan3944 : Plan := .step choices128 bits841 plan2631

def plan3945 : Plan := .step choices128 bits840 plan2632

def plan3946 : Plan := .step choices128 bits842 plan2633

def plan3947 : Plan := .step choices128 bits841 plan2634

def plan3948 : Plan := .step choices128 bits840 plan2635

def plan3949 : Plan := .step choices129 bits809 plan2584

def plan3950 : Plan := .step choices129 bits810 plan2585

def plan3951 : Plan := .step choices129 bits809 plan2586

def plan3952 : Plan := .step choices129 bits813 plan2587

def plan3953 : Plan := .step choices129 bits815 plan2588

def plan3954 : Plan := .step choices129 bits813 plan2589

def plan3955 : Plan := .step choices129 bits808 plan2590

def plan3956 : Plan := .step choices129 bits808 plan2600

def plan3957 : Plan := .step choices129 bits818 plan2607

def plan3958 : Plan := .step choices129 bits821 plan2608

def plan3959 : Plan := .step choices129 bits818 plan2609

def plan3960 : Plan := .step choices129 bits812 plan2616

def plan3961 : Plan := .step choices129 bits812 plan2622

def plan3962 : Plan := .step choices129 bits825 plan2627

def plan3963 : Plan := .step choices129 bits829 plan2628

def plan3964 : Plan := .step choices129 bits825 plan2629

def plan3965 : Plan := .step choices129 bits807 plan2637

def plan3966 : Plan := .step choices129 bits811 plan2641

def plan3967 : Plan := .step choices129 bits817 plan2647

def plan3968 : Plan := .step choices129 bits807 plan2654

def plan3969 : Plan := .step choices129 bits811 plan2658

def plan3970 : Plan := .step choices129 bits817 plan2664

def plan3971 : Plan := .step choices130 bits833 plan2627

def plan3972 : Plan := .step choices130 bits837 plan2628

def plan3973 : Plan := .step choices130 bits833 plan2629

def plan3974 : Plan := .step choices130 bits825 plan2647

def plan3975 : Plan := .step choices130 bits825 plan2664

def plan3976 : Plan := .step choices133 bits809 plan2584

def plan3977 : Plan := .step choices133 bits810 plan2585

def plan3978 : Plan := .step choices133 bits809 plan2586

def plan3979 : Plan := .step choices133 bits813 plan2587

def plan3980 : Plan := .step choices133 bits815 plan2588

def plan3981 : Plan := .step choices133 bits813 plan2589

def plan3982 : Plan := .step choices133 bits808 plan2590

def plan3983 : Plan := .step choices133 bits808 plan2600

def plan3984 : Plan := .step choices133 bits818 plan2607

def plan3985 : Plan := .step choices133 bits821 plan2608

def plan3986 : Plan := .step choices133 bits818 plan2609

def plan3987 : Plan := .step choices133 bits812 plan2616

def plan3988 : Plan := .step choices133 bits812 plan2622

def plan3989 : Plan := .step choices133 bits825 plan2627

def plan3990 : Plan := .step choices133 bits829 plan2628

def plan3991 : Plan := .step choices133 bits825 plan2629

def plan3992 : Plan := .step choices133 bits817 plan2647

def plan3993 : Plan := .step choices133 bits807 plan2654

def plan3994 : Plan := .step choices133 bits811 plan2658

def plan3995 : Plan := .step choices133 bits817 plan2664

def plan3996 : Plan := .step choices134 bits833 plan2627

def plan3997 : Plan := .step choices134 bits837 plan2628

def plan3998 : Plan := .step choices134 bits833 plan2629

def plan3999 : Plan := .step choices134 bits825 plan2664

def plan4000 : Plan := .step choices136 bits977 plan2674

def plan4001 : Plan := .step choices136 bits978 plan2676

def plan4002 : Plan := .step choices136 bits977 plan2678

def plan4003 : Plan := .step choices136 bits977 plan2680

def plan4004 : Plan := .step choices136 bits978 plan2681

def plan4005 : Plan := .step choices136 bits977 plan2682

def plan4006 : Plan := .step choices136 bits979 plan2683

def plan4007 : Plan := .step choices136 bits978 plan2684

def plan4008 : Plan := .step choices136 bits977 plan2685

def plan4009 : Plan := .step choices136 bits980 plan2686

def plan4010 : Plan := .step choices136 bits977 plan2691

def plan4011 : Plan := .step choices136 bits978 plan2693

def plan4012 : Plan := .step choices136 bits977 plan2695

def plan4013 : Plan := .step choices136 bits979 plan2697

def plan4014 : Plan := .step choices136 bits978 plan2698

def plan4015 : Plan := .step choices136 bits977 plan2699

def plan4016 : Plan := .step choices136 bits984 plan2724

def plan4017 : Plan := .step choices136 bits984 plan2727

def plan4018 : Plan := .step choices136 bits985 plan2728

def plan4019 : Plan := .step choices136 bits984 plan2729

def plan4020 : Plan := .step choices136 bits986 plan2730

def plan4021 : Plan := .step choices136 bits984 plan2733

def plan4022 : Plan := .step choices136 bits985 plan2736

def plan4023 : Plan := .step choices136 bits984 plan2737

def plan4024 : Plan := .step choices136 bits985 plan2738

def plan4025 : Plan := .step choices136 bits986 plan2739

def plan4026 : Plan := .step choices136 bits985 plan2740

def plan4027 : Plan := .step choices136 bits987 plan2741

def plan4028 : Plan := .step choices136 bits986 plan2742

def plan4029 : Plan := .step choices136 bits985 plan2743

def plan4030 : Plan := .step choices136 bits988 plan2744

def plan4031 : Plan := .step choices136 bits984 plan2748

def plan4032 : Plan := .step choices136 bits985 plan2749

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


