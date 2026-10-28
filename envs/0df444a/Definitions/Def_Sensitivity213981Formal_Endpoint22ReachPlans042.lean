-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans042
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans042
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:48:55.77842+00:00
-- url     : https://prove2.me/theorems/da50bfee-75f4-4372-8f5c-8b18f7408d52
-- title:
--   Endpoint22 Reach Plans042 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans042 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4101`, `ThreeBoundEndpoint22Reachable.plan4102`, `ThreeBoundEndpoint22Reachable.plan4103`, `ThreeBoundEndpoint22Reachable.plan4104`, `ThreeBoundEndpoint22Reachable.plan4105`, `ThreeBoundEndpoint22Reachable.plan4106`, `ThreeBoundEndpoint22Reachable.plan4107`, `ThreeBoundEndpoint22Reachable.plan4108`, `ThreeBoundEndpoint22Reachable.plan4038`, `ThreeBoundEndpoint22Reachable.plan4109`, `ThreeBoundEndpoint22Reachable.plan4110`, `ThreeBoundEndpoint22Reachable.plan4111`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans042.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
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
def plan4033 : Plan := .step choices136 bits984 plan2750

def plan4034 : Plan := .step choices136 bits986 plan2751

def plan4035 : Plan := .step choices136 bits984 plan2754

def plan4036 : Plan := .step choices136 bits985 plan2757

def plan4037 : Plan := .step choices136 bits984 plan2758

def plan4038 : Plan := .step choices136 bits987 plan2759

def plan4039 : Plan := .step choices136 bits986 plan2760

def plan4040 : Plan := .step choices136 bits985 plan2761

def plan4041 : Plan := .step choices136 bits991 plan2768

def plan4042 : Plan := .step choices136 bits992 plan2769

def plan4043 : Plan := .step choices136 bits991 plan2770

def plan4044 : Plan := .step choices136 bits993 plan2771

def plan4045 : Plan := .step choices136 bits992 plan2772

def plan4046 : Plan := .step choices136 bits991 plan2773

def plan4047 : Plan := .step choices136 bits994 plan2774

def plan4048 : Plan := .step choices136 bits993 plan2775

def plan4049 : Plan := .step choices136 bits992 plan2776

def plan4050 : Plan := .step choices136 bits991 plan2777

def plan4051 : Plan := .step choices136 bits975 plan2784

def plan4052 : Plan := .step choices136 bits976 plan2786

def plan4053 : Plan := .step choices136 bits975 plan2788

def plan4054 : Plan := .step choices136 bits981 plan2793

def plan4055 : Plan := .step choices136 bits982 plan2794

def plan4056 : Plan := .step choices136 bits981 plan2795

def plan4057 : Plan := .step choices136 bits983 plan2796

def plan4058 : Plan := .step choices136 bits982 plan2797

def plan4059 : Plan := .step choices136 bits981 plan2798

def plan4060 : Plan := .step choices136 bits981 plan2802

def plan4061 : Plan := .step choices136 bits981 plan2807

def plan4062 : Plan := .step choices136 bits990 plan2812

def plan4063 : Plan := .step choices136 bits991 plan2813

def plan4064 : Plan := .step choices136 bits990 plan2814

def plan4065 : Plan := .step choices136 bits992 plan2815

def plan4066 : Plan := .step choices136 bits991 plan2816

def plan4067 : Plan := .step choices136 bits990 plan2817

def plan4068 : Plan := .step choices136 bits989 plan2819

def plan4069 : Plan := .step choices136 bits990 plan2820

def plan4070 : Plan := .step choices136 bits989 plan2821

def plan4071 : Plan := .step choices136 bits989 plan2825

def plan4072 : Plan := .step choices136 bits990 plan2826

def plan4073 : Plan := .step choices136 bits989 plan2827

def plan4074 : Plan := .step choices136 bits975 plan2835

def plan4075 : Plan := .step choices136 bits976 plan2837

def plan4076 : Plan := .step choices136 bits975 plan2839

def plan4077 : Plan := .step choices136 bits981 plan2844

def plan4078 : Plan := .step choices136 bits982 plan2845

def plan4079 : Plan := .step choices136 bits981 plan2846

def plan4080 : Plan := .step choices136 bits983 plan2847

def plan4081 : Plan := .step choices136 bits982 plan2848

def plan4082 : Plan := .step choices136 bits981 plan2849

def plan4083 : Plan := .step choices136 bits981 plan2852

def plan4084 : Plan := .step choices136 bits981 plan2857

def plan4085 : Plan := .step choices136 bits990 plan2862

def plan4086 : Plan := .step choices136 bits991 plan2863

def plan4087 : Plan := .step choices136 bits990 plan2864

def plan4088 : Plan := .step choices136 bits992 plan2865

def plan4089 : Plan := .step choices136 bits991 plan2866

def plan4090 : Plan := .step choices136 bits990 plan2867

def plan4091 : Plan := .step choices136 bits989 plan2869

def plan4092 : Plan := .step choices136 bits990 plan2870

def plan4093 : Plan := .step choices136 bits989 plan2871

def plan4094 : Plan := .step choices137 bits995 plan2669

def plan4095 : Plan := .step choices137 bits996 plan2670

def plan4096 : Plan := .step choices137 bits995 plan2671

def plan4097 : Plan := .step choices137 bits999 plan2672

def plan4098 : Plan := .step choices137 bits999 plan2673

def plan4099 : Plan := .step choices137 bits1002 plan2674

def plan4100 : Plan := .step choices137 bits999 plan2675

def plan4101 : Plan := .step choices137 bits1003 plan2676

def plan4102 : Plan := .step choices137 bits999 plan2677

def plan4103 : Plan := .step choices137 bits1002 plan2678

def plan4104 : Plan := .step choices137 bits999 plan2679

def plan4105 : Plan := .step choices137 bits1002 plan2680

def plan4106 : Plan := .step choices137 bits1003 plan2681

def plan4107 : Plan := .step choices137 bits1002 plan2682

def plan4108 : Plan := .step choices137 bits1004 plan2683

def plan4109 : Plan := .step choices137 bits1003 plan2684

def plan4110 : Plan := .step choices137 bits1002 plan2685

def plan4111 : Plan := .step choices137 bits1005 plan2686

def plan4112 : Plan := .step choices137 bits995 plan2687

def plan4113 : Plan := .step choices137 bits996 plan2688

def plan4114 : Plan := .step choices137 bits995 plan2689

def plan4115 : Plan := .step choices137 bits999 plan2690

def plan4116 : Plan := .step choices137 bits1002 plan2691

def plan4117 : Plan := .step choices137 bits999 plan2692

def plan4118 : Plan := .step choices137 bits1003 plan2693

def plan4119 : Plan := .step choices137 bits999 plan2694

def plan4120 : Plan := .step choices137 bits1002 plan2695

def plan4121 : Plan := .step choices137 bits999 plan2696

def plan4122 : Plan := .step choices137 bits1004 plan2697

def plan4123 : Plan := .step choices137 bits1003 plan2698

def plan4124 : Plan := .step choices137 bits1002 plan2699

def plan4125 : Plan := .step choices137 bits1009 plan2723

def plan4126 : Plan := .step choices137 bits1013 plan2724

def plan4127 : Plan := .step choices137 bits1009 plan2726

def plan4128 : Plan := .step choices137 bits1013 plan2727

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


