-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans043
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:12.615163+00:00
-- url     : https://prove2.me/theorems/cc20cbb9-ac49-4ecb-9b9f-241a715234b3
-- title:
--   Endpoint22 Reach Plans043 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans043 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4197`, `ThreeBoundEndpoint22Reachable.plan4198`, `ThreeBoundEndpoint22Reachable.plan4199`, `ThreeBoundEndpoint22Reachable.plan4200`, `ThreeBoundEndpoint22Reachable.plan4201`, `ThreeBoundEndpoint22Reachable.plan4202`, `ThreeBoundEndpoint22Reachable.plan4203`, `ThreeBoundEndpoint22Reachable.plan4134`, `ThreeBoundEndpoint22Reachable.plan4204`, `ThreeBoundEndpoint22Reachable.plan4205`, `ThreeBoundEndpoint22Reachable.plan4206`, `ThreeBoundEndpoint22Reachable.plan4207`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans043.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan4129 : Plan := .step choices137 bits1014 plan2728

def plan4130 : Plan := .step choices137 bits1013 plan2729

def plan4131 : Plan := .step choices137 bits1015 plan2730

def plan4132 : Plan := .step choices137 bits1009 plan2732

def plan4133 : Plan := .step choices137 bits1013 plan2733

def plan4134 : Plan := .step choices137 bits1009 plan2735

def plan4135 : Plan := .step choices137 bits1014 plan2736

def plan4136 : Plan := .step choices137 bits1013 plan2737

def plan4137 : Plan := .step choices137 bits1014 plan2738

def plan4138 : Plan := .step choices137 bits1015 plan2739

def plan4139 : Plan := .step choices137 bits1014 plan2740

def plan4140 : Plan := .step choices137 bits1016 plan2741

def plan4141 : Plan := .step choices137 bits1015 plan2742

def plan4142 : Plan := .step choices137 bits1014 plan2743

def plan4143 : Plan := .step choices137 bits1017 plan2744

def plan4144 : Plan := .step choices137 bits1013 plan2748

def plan4145 : Plan := .step choices137 bits1014 plan2749

def plan4146 : Plan := .step choices137 bits1013 plan2750

def plan4147 : Plan := .step choices137 bits1015 plan2751

def plan4148 : Plan := .step choices137 bits1009 plan2753

def plan4149 : Plan := .step choices137 bits1013 plan2754

def plan4150 : Plan := .step choices137 bits1009 plan2756

def plan4151 : Plan := .step choices137 bits1014 plan2757

def plan4152 : Plan := .step choices137 bits1013 plan2758

def plan4153 : Plan := .step choices137 bits1016 plan2759

def plan4154 : Plan := .step choices137 bits1015 plan2760

def plan4155 : Plan := .step choices137 bits1014 plan2761

def plan4156 : Plan := .step choices137 bits1029 plan2768

def plan4157 : Plan := .step choices137 bits1030 plan2769

def plan4158 : Plan := .step choices137 bits1029 plan2770

def plan4159 : Plan := .step choices137 bits1031 plan2771

def plan4160 : Plan := .step choices137 bits1030 plan2772

def plan4161 : Plan := .step choices137 bits1029 plan2773

def plan4162 : Plan := .step choices137 bits1032 plan2774

def plan4163 : Plan := .step choices137 bits1031 plan2775

def plan4164 : Plan := .step choices137 bits1030 plan2776

def plan4165 : Plan := .step choices137 bits1029 plan2777

def plan4166 : Plan := .step choices137 bits998 plan2782

def plan4167 : Plan := .step choices137 bits998 plan2783

def plan4168 : Plan := .step choices137 bits1000 plan2784

def plan4169 : Plan := .step choices137 bits998 plan2785

def plan4170 : Plan := .step choices137 bits1001 plan2786

def plan4171 : Plan := .step choices137 bits998 plan2787

def plan4172 : Plan := .step choices137 bits1000 plan2788

def plan4173 : Plan := .step choices137 bits998 plan2789

def plan4174 : Plan := .step choices137 bits1010 plan2793

def plan4175 : Plan := .step choices137 bits1011 plan2794

def plan4176 : Plan := .step choices137 bits1010 plan2795

def plan4177 : Plan := .step choices137 bits1012 plan2796

def plan4178 : Plan := .step choices137 bits1011 plan2797

def plan4179 : Plan := .step choices137 bits1010 plan2798

def plan4180 : Plan := .step choices137 bits997 plan2799

def plan4181 : Plan := .step choices137 bits1008 plan2801

def plan4182 : Plan := .step choices137 bits1010 plan2802

def plan4183 : Plan := .step choices137 bits1008 plan2803

def plan4184 : Plan := .step choices137 bits997 plan2804

def plan4185 : Plan := .step choices137 bits1008 plan2806

def plan4186 : Plan := .step choices137 bits1010 plan2807

def plan4187 : Plan := .step choices137 bits1008 plan2808

def plan4188 : Plan := .step choices137 bits1028 plan2812

def plan4189 : Plan := .step choices137 bits1029 plan2813

def plan4190 : Plan := .step choices137 bits1028 plan2814

def plan4191 : Plan := .step choices137 bits1030 plan2815

def plan4192 : Plan := .step choices137 bits1029 plan2816

def plan4193 : Plan := .step choices137 bits1028 plan2817

def plan4194 : Plan := .step choices137 bits1024 plan2819

def plan4195 : Plan := .step choices137 bits1028 plan2820

def plan4196 : Plan := .step choices137 bits1024 plan2821

def plan4197 : Plan := .step choices137 bits1020 plan2822

def plan4198 : Plan := .step choices137 bits1020 plan2823

def plan4199 : Plan := .step choices137 bits1024 plan2825

def plan4200 : Plan := .step choices137 bits1028 plan2826

def plan4201 : Plan := .step choices137 bits1024 plan2827

def plan4202 : Plan := .step choices137 bits1020 plan2828

def plan4203 : Plan := .step choices137 bits998 plan2833

def plan4204 : Plan := .step choices137 bits998 plan2834

def plan4205 : Plan := .step choices137 bits1000 plan2835

def plan4206 : Plan := .step choices137 bits998 plan2836

def plan4207 : Plan := .step choices137 bits1001 plan2837

def plan4208 : Plan := .step choices137 bits998 plan2838

def plan4209 : Plan := .step choices137 bits1000 plan2839

def plan4210 : Plan := .step choices137 bits998 plan2840

def plan4211 : Plan := .step choices137 bits1010 plan2844

def plan4212 : Plan := .step choices137 bits1011 plan2845

def plan4213 : Plan := .step choices137 bits1010 plan2846

def plan4214 : Plan := .step choices137 bits1012 plan2847

def plan4215 : Plan := .step choices137 bits1011 plan2848

def plan4216 : Plan := .step choices137 bits1010 plan2849

def plan4217 : Plan := .step choices137 bits1008 plan2851

def plan4218 : Plan := .step choices137 bits1010 plan2852

def plan4219 : Plan := .step choices137 bits1008 plan2853

def plan4220 : Plan := .step choices137 bits997 plan2854

def plan4221 : Plan := .step choices137 bits1008 plan2856

def plan4222 : Plan := .step choices137 bits1010 plan2857

def plan4223 : Plan := .step choices137 bits1008 plan2858

def plan4224 : Plan := .step choices137 bits1028 plan2862

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


