-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans049
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:41.284872+00:00
-- url     : https://prove2.me/theorems/1f1340b2-2eb4-43f6-aabd-69c29a9b4d69
-- title:
--   Endpoint22 Reach Plans049 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans049 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4709`, `ThreeBoundEndpoint22Reachable.plan4772`, `ThreeBoundEndpoint22Reachable.plan4773`, `ThreeBoundEndpoint22Reachable.plan4774`, `ThreeBoundEndpoint22Reachable.plan4775`, `ThreeBoundEndpoint22Reachable.plan4776`, `ThreeBoundEndpoint22Reachable.plan4777`, `ThreeBoundEndpoint22Reachable.plan4778`, `ThreeBoundEndpoint22Reachable.plan4779`, `ThreeBoundEndpoint22Reachable.plan4780`, `ThreeBoundEndpoint22Reachable.plan4781`, `ThreeBoundEndpoint22Reachable.plan4710`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans049.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
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
def plan4705 : Plan := .step choices149 bits1214 plan3024

def plan4706 : Plan := .step choices149 bits1213 plan3025

def plan4707 : Plan := .step choices149 bits1210 plan3026

def plan4708 : Plan := .step choices149 bits1216 plan3027

def plan4709 : Plan := .step choices149 bits1206 plan3083

def plan4710 : Plan := .step choices149 bits1209 plan3084

def plan4711 : Plan := .step choices149 bits1206 plan3085

def plan4712 : Plan := .step choices149 bits1211 plan3086

def plan4713 : Plan := .step choices149 bits1209 plan3087

def plan4714 : Plan := .step choices149 bits1206 plan3088

def plan4715 : Plan := .step choices149 bits1212 plan3089

def plan4716 : Plan := .step choices149 bits1203 plan3093

def plan4717 : Plan := .step choices149 bits1205 plan3094

def plan4718 : Plan := .step choices149 bits1203 plan3095

def plan4719 : Plan := .step choices149 bits1207 plan3096

def plan4720 : Plan := .step choices149 bits1200 plan3098

def plan4721 : Plan := .step choices149 bits1202 plan3099

def plan4722 : Plan := .step choices149 bits1198 plan3100

def plan4723 : Plan := .step choices149 bits1200 plan3101

def plan4724 : Plan := .step choices149 bits1205 plan3102

def plan4725 : Plan := .step choices149 bits1203 plan3103

def plan4726 : Plan := .step choices149 bits1211 plan3104

def plan4727 : Plan := .step choices149 bits1209 plan3105

def plan4728 : Plan := .step choices149 bits1206 plan3106

def plan4729 : Plan := .step choices149 bits1215 plan3107

def plan4730 : Plan := .step choices149 bits1214 plan3108

def plan4731 : Plan := .step choices149 bits1213 plan3109

def plan4732 : Plan := .step choices149 bits1210 plan3110

def plan4733 : Plan := .step choices150 bits1234 plan3017

def plan4734 : Plan := .step choices150 bits1235 plan3018

def plan4735 : Plan := .step choices150 bits1234 plan3019

def plan4736 : Plan := .step choices150 bits1236 plan3020

def plan4737 : Plan := .step choices150 bits1235 plan3021

def plan4738 : Plan := .step choices150 bits1234 plan3022

def plan4739 : Plan := .step choices150 bits1237 plan3023

def plan4740 : Plan := .step choices150 bits1236 plan3024

def plan4741 : Plan := .step choices150 bits1235 plan3025

def plan4742 : Plan := .step choices150 bits1234 plan3026

def plan4743 : Plan := .step choices150 bits1238 plan3027

def plan4744 : Plan := .step choices150 bits1237 plan3107

def plan4745 : Plan := .step choices150 bits1236 plan3108

def plan4746 : Plan := .step choices150 bits1235 plan3109

def plan4747 : Plan := .step choices150 bits1234 plan3110

def plan4748 : Plan := .step choices151 bits1198 plan2873

def plan4749 : Plan := .step choices151 bits1199 plan2874

def plan4750 : Plan := .step choices151 bits1198 plan2875

def plan4751 : Plan := .step choices151 bits1200 plan2876

def plan4752 : Plan := .step choices151 bits1202 plan2877

def plan4753 : Plan := .step choices151 bits1200 plan2878

def plan4754 : Plan := .step choices151 bits1204 plan2879

def plan4755 : Plan := .step choices151 bits1198 plan2880

def plan4756 : Plan := .step choices151 bits1199 plan2881

def plan4757 : Plan := .step choices151 bits1198 plan2882

def plan4758 : Plan := .step choices151 bits1202 plan2883

def plan4759 : Plan := .step choices151 bits1200 plan2884

def plan4760 : Plan := .step choices151 bits1203 plan2885

def plan4761 : Plan := .step choices151 bits1205 plan2886

def plan4762 : Plan := .step choices151 bits1203 plan2887

def plan4763 : Plan := .step choices151 bits1207 plan2888

def plan4764 : Plan := .step choices151 bits1205 plan2889

def plan4765 : Plan := .step choices151 bits1203 plan2890

def plan4766 : Plan := .step choices151 bits1208 plan2891

def plan4767 : Plan := .step choices151 bits1200 plan2892

def plan4768 : Plan := .step choices151 bits1202 plan2893

def plan4769 : Plan := .step choices151 bits1200 plan2894

def plan4770 : Plan := .step choices151 bits1204 plan2895

def plan4771 : Plan := .step choices151 bits1198 plan2896

def plan4772 : Plan := .step choices151 bits1199 plan2897

def plan4773 : Plan := .step choices151 bits1198 plan2898

def plan4774 : Plan := .step choices151 bits1202 plan2899

def plan4775 : Plan := .step choices151 bits1200 plan2900

def plan4776 : Plan := .step choices151 bits1207 plan2901

def plan4777 : Plan := .step choices151 bits1205 plan2902

def plan4778 : Plan := .step choices151 bits1203 plan2903

def plan4779 : Plan := .step choices151 bits1226 plan2904

def plan4780 : Plan := .step choices151 bits1227 plan2905

def plan4781 : Plan := .step choices151 bits1226 plan2906

def plan4782 : Plan := .step choices151 bits1228 plan2907

def plan4783 : Plan := .step choices151 bits1227 plan2908

def plan4784 : Plan := .step choices151 bits1226 plan2909

def plan4785 : Plan := .step choices151 bits1229 plan2910

def plan4786 : Plan := .step choices151 bits1228 plan2911

def plan4787 : Plan := .step choices151 bits1227 plan2912

def plan4788 : Plan := .step choices151 bits1226 plan2913

def plan4789 : Plan := .step choices151 bits1197 plan2914

def plan4790 : Plan := .step choices151 bits1198 plan2915

def plan4791 : Plan := .step choices151 bits1199 plan2916

def plan4792 : Plan := .step choices151 bits1198 plan2917

def plan4793 : Plan := .step choices151 bits1201 plan2918

def plan4794 : Plan := .step choices151 bits1197 plan2919

def plan4795 : Plan := .step choices151 bits1199 plan2920

def plan4796 : Plan := .step choices151 bits1198 plan2921

def plan4797 : Plan := .step choices151 bits1220 plan2922

def plan4798 : Plan := .step choices151 bits1221 plan2923

def plan4799 : Plan := .step choices151 bits1220 plan2924

def plan4800 : Plan := .step choices151 bits1222 plan2925

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


