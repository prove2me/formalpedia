-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans051
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:23.333562+00:00
-- url     : https://prove2.me/theorems/88c34d3b-abd9-4422-b6f7-e177cd2ed0af
-- title:
--   Endpoint22 Reach Plans051 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans051 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4901`, `ThreeBoundEndpoint22Reachable.plan4964`, `ThreeBoundEndpoint22Reachable.plan4965`, `ThreeBoundEndpoint22Reachable.plan4966`, `ThreeBoundEndpoint22Reachable.plan4967`, `ThreeBoundEndpoint22Reachable.plan4968`, `ThreeBoundEndpoint22Reachable.plan4969`, `ThreeBoundEndpoint22Reachable.plan4970`, `ThreeBoundEndpoint22Reachable.plan4971`, `ThreeBoundEndpoint22Reachable.plan4972`, `ThreeBoundEndpoint22Reachable.plan4973`, `ThreeBoundEndpoint22Reachable.plan4902`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans051.lean, lines 1–206.

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
def plan4897 : Plan := .step choices155 bits1200 plan2878

def plan4898 : Plan := .step choices155 bits1204 plan2879

def plan4899 : Plan := .step choices155 bits1198 plan2880

def plan4900 : Plan := .step choices155 bits1199 plan2881

def plan4901 : Plan := .step choices155 bits1198 plan2882

def plan4902 : Plan := .step choices155 bits1202 plan2883

def plan4903 : Plan := .step choices155 bits1200 plan2884

def plan4904 : Plan := .step choices155 bits1203 plan2885

def plan4905 : Plan := .step choices155 bits1205 plan2886

def plan4906 : Plan := .step choices155 bits1203 plan2887

def plan4907 : Plan := .step choices155 bits1207 plan2888

def plan4908 : Plan := .step choices155 bits1205 plan2889

def plan4909 : Plan := .step choices155 bits1203 plan2890

def plan4910 : Plan := .step choices155 bits1208 plan2891

def plan4911 : Plan := .step choices155 bits1200 plan2892

def plan4912 : Plan := .step choices155 bits1202 plan2893

def plan4913 : Plan := .step choices155 bits1200 plan2894

def plan4914 : Plan := .step choices155 bits1204 plan2895

def plan4915 : Plan := .step choices155 bits1198 plan2896

def plan4916 : Plan := .step choices155 bits1199 plan2897

def plan4917 : Plan := .step choices155 bits1198 plan2898

def plan4918 : Plan := .step choices155 bits1202 plan2899

def plan4919 : Plan := .step choices155 bits1200 plan2900

def plan4920 : Plan := .step choices155 bits1207 plan2901

def plan4921 : Plan := .step choices155 bits1205 plan2902

def plan4922 : Plan := .step choices155 bits1203 plan2903

def plan4923 : Plan := .step choices155 bits1226 plan2904

def plan4924 : Plan := .step choices155 bits1227 plan2905

def plan4925 : Plan := .step choices155 bits1226 plan2906

def plan4926 : Plan := .step choices155 bits1228 plan2907

def plan4927 : Plan := .step choices155 bits1227 plan2908

def plan4928 : Plan := .step choices155 bits1226 plan2909

def plan4929 : Plan := .step choices155 bits1229 plan2910

def plan4930 : Plan := .step choices155 bits1228 plan2911

def plan4931 : Plan := .step choices155 bits1227 plan2912

def plan4932 : Plan := .step choices155 bits1226 plan2913

def plan4933 : Plan := .step choices155 bits1223 plan2967

def plan4934 : Plan := .step choices155 bits1224 plan2968

def plan4935 : Plan := .step choices155 bits1223 plan2969

def plan4936 : Plan := .step choices155 bits1225 plan2970

def plan4937 : Plan := .step choices155 bits1224 plan2971

def plan4938 : Plan := .step choices155 bits1223 plan2972

def plan4939 : Plan := .step choices155 bits1220 plan2973

def plan4940 : Plan := .step choices155 bits1221 plan2974

def plan4941 : Plan := .step choices155 bits1220 plan2975

def plan4942 : Plan := .step choices155 bits1218 plan2976

def plan4943 : Plan := .step choices155 bits1218 plan2986

def plan4944 : Plan := .step choices155 bits1220 plan3000

def plan4945 : Plan := .step choices155 bits1221 plan3001

def plan4946 : Plan := .step choices155 bits1220 plan3002

def plan4947 : Plan := .step choices155 bits1218 plan3007

def plan4948 : Plan := .step choices155 bits1197 plan3028

def plan4949 : Plan := .step choices155 bits1198 plan3029

def plan4950 : Plan := .step choices155 bits1199 plan3030

def plan4951 : Plan := .step choices155 bits1198 plan3031

def plan4952 : Plan := .step choices155 bits1201 plan3032

def plan4953 : Plan := .step choices155 bits1197 plan3033

def plan4954 : Plan := .step choices155 bits1199 plan3034

def plan4955 : Plan := .step choices155 bits1198 plan3035

def plan4956 : Plan := .step choices155 bits1220 plan3036

def plan4957 : Plan := .step choices155 bits1221 plan3037

def plan4958 : Plan := .step choices155 bits1220 plan3038

def plan4959 : Plan := .step choices155 bits1222 plan3039

def plan4960 : Plan := .step choices155 bits1221 plan3040

def plan4961 : Plan := .step choices155 bits1220 plan3041

def plan4962 : Plan := .step choices155 bits1218 plan3042

def plan4963 : Plan := .step choices155 bits1219 plan3043

def plan4964 : Plan := .step choices155 bits1218 plan3044

def plan4965 : Plan := .step choices155 bits1217 plan3060

def plan4966 : Plan := .step choices155 bits1218 plan3064

def plan4967 : Plan := .step choices155 bits1219 plan3065

def plan4968 : Plan := .step choices155 bits1218 plan3066

def plan4969 : Plan := .step choices155 bits1223 plan3077

def plan4970 : Plan := .step choices155 bits1224 plan3078

def plan4971 : Plan := .step choices155 bits1223 plan3079

def plan4972 : Plan := .step choices155 bits1225 plan3080

def plan4973 : Plan := .step choices155 bits1224 plan3081

def plan4974 : Plan := .step choices155 bits1223 plan3082

def plan4975 : Plan := .step choices155 bits1220 plan3090

def plan4976 : Plan := .step choices155 bits1221 plan3091

def plan4977 : Plan := .step choices155 bits1220 plan3092

def plan4978 : Plan := .step choices155 bits1218 plan3097

def plan4979 : Plan := .step choices156 bits1230 plan2904

def plan4980 : Plan := .step choices156 bits1231 plan2905

def plan4981 : Plan := .step choices156 bits1230 plan2906

def plan4982 : Plan := .step choices156 bits1232 plan2907

def plan4983 : Plan := .step choices156 bits1231 plan2908

def plan4984 : Plan := .step choices156 bits1230 plan2909

def plan4985 : Plan := .step choices156 bits1233 plan2910

def plan4986 : Plan := .step choices156 bits1232 plan2911

def plan4987 : Plan := .step choices156 bits1231 plan2912

def plan4988 : Plan := .step choices156 bits1230 plan2913

def plan4989 : Plan := .step choices156 bits1226 plan3077

def plan4990 : Plan := .step choices156 bits1227 plan3078

def plan4991 : Plan := .step choices156 bits1226 plan3079

def plan4992 : Plan := .step choices156 bits1228 plan3080

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


