-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans050
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:22.551118+00:00
-- url     : https://prove2.me/theorems/12612799-cdc6-42dc-afc1-96796f3d8772
-- title:
--   Endpoint22 Reach Plans050 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans050 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4805`, `ThreeBoundEndpoint22Reachable.plan4868`, `ThreeBoundEndpoint22Reachable.plan4869`, `ThreeBoundEndpoint22Reachable.plan4870`, `ThreeBoundEndpoint22Reachable.plan4871`, `ThreeBoundEndpoint22Reachable.plan4872`, `ThreeBoundEndpoint22Reachable.plan4873`, `ThreeBoundEndpoint22Reachable.plan4874`, `ThreeBoundEndpoint22Reachable.plan4875`, `ThreeBoundEndpoint22Reachable.plan4876`, `ThreeBoundEndpoint22Reachable.plan4877`, `ThreeBoundEndpoint22Reachable.plan4806`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans050.lean, lines 1–206.

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
def plan4801 : Plan := .step choices151 bits1221 plan2926

def plan4802 : Plan := .step choices151 bits1220 plan2927

def plan4803 : Plan := .step choices151 bits1217 plan2928

def plan4804 : Plan := .step choices151 bits1218 plan2932

def plan4805 : Plan := .step choices151 bits1219 plan2933

def plan4806 : Plan := .step choices151 bits1218 plan2934

def plan4807 : Plan := .step choices151 bits1217 plan2950

def plan4808 : Plan := .step choices151 bits1218 plan2954

def plan4809 : Plan := .step choices151 bits1219 plan2955

def plan4810 : Plan := .step choices151 bits1218 plan2956

def plan4811 : Plan := .step choices151 bits1223 plan2967

def plan4812 : Plan := .step choices151 bits1224 plan2968

def plan4813 : Plan := .step choices151 bits1223 plan2969

def plan4814 : Plan := .step choices151 bits1225 plan2970

def plan4815 : Plan := .step choices151 bits1224 plan2971

def plan4816 : Plan := .step choices151 bits1223 plan2972

def plan4817 : Plan := .step choices151 bits1220 plan2973

def plan4818 : Plan := .step choices151 bits1221 plan2974

def plan4819 : Plan := .step choices151 bits1220 plan2975

def plan4820 : Plan := .step choices151 bits1218 plan2976

def plan4821 : Plan := .step choices151 bits1218 plan2986

def plan4822 : Plan := .step choices151 bits1220 plan3000

def plan4823 : Plan := .step choices151 bits1221 plan3001

def plan4824 : Plan := .step choices151 bits1220 plan3002

def plan4825 : Plan := .step choices151 bits1218 plan3007

def plan4826 : Plan := .step choices151 bits1197 plan3028

def plan4827 : Plan := .step choices151 bits1198 plan3029

def plan4828 : Plan := .step choices151 bits1199 plan3030

def plan4829 : Plan := .step choices151 bits1198 plan3031

def plan4830 : Plan := .step choices151 bits1201 plan3032

def plan4831 : Plan := .step choices151 bits1197 plan3033

def plan4832 : Plan := .step choices151 bits1199 plan3034

def plan4833 : Plan := .step choices151 bits1198 plan3035

def plan4834 : Plan := .step choices151 bits1220 plan3036

def plan4835 : Plan := .step choices151 bits1221 plan3037

def plan4836 : Plan := .step choices151 bits1220 plan3038

def plan4837 : Plan := .step choices151 bits1222 plan3039

def plan4838 : Plan := .step choices151 bits1221 plan3040

def plan4839 : Plan := .step choices151 bits1220 plan3041

def plan4840 : Plan := .step choices151 bits1218 plan3042

def plan4841 : Plan := .step choices151 bits1219 plan3043

def plan4842 : Plan := .step choices151 bits1218 plan3044

def plan4843 : Plan := .step choices151 bits1217 plan3060

def plan4844 : Plan := .step choices151 bits1218 plan3064

def plan4845 : Plan := .step choices151 bits1219 plan3065

def plan4846 : Plan := .step choices151 bits1218 plan3066

def plan4847 : Plan := .step choices151 bits1223 plan3077

def plan4848 : Plan := .step choices151 bits1224 plan3078

def plan4849 : Plan := .step choices151 bits1223 plan3079

def plan4850 : Plan := .step choices151 bits1225 plan3080

def plan4851 : Plan := .step choices151 bits1224 plan3081

def plan4852 : Plan := .step choices151 bits1223 plan3082

def plan4853 : Plan := .step choices151 bits1220 plan3090

def plan4854 : Plan := .step choices151 bits1221 plan3091

def plan4855 : Plan := .step choices151 bits1220 plan3092

def plan4856 : Plan := .step choices151 bits1218 plan3097

def plan4857 : Plan := .step choices152 bits1230 plan2904

def plan4858 : Plan := .step choices152 bits1231 plan2905

def plan4859 : Plan := .step choices152 bits1230 plan2906

def plan4860 : Plan := .step choices152 bits1232 plan2907

def plan4861 : Plan := .step choices152 bits1231 plan2908

def plan4862 : Plan := .step choices152 bits1230 plan2909

def plan4863 : Plan := .step choices152 bits1233 plan2910

def plan4864 : Plan := .step choices152 bits1232 plan2911

def plan4865 : Plan := .step choices152 bits1231 plan2912

def plan4866 : Plan := .step choices152 bits1230 plan2913

def plan4867 : Plan := .step choices152 bits1226 plan2967

def plan4868 : Plan := .step choices152 bits1227 plan2968

def plan4869 : Plan := .step choices152 bits1226 plan2969

def plan4870 : Plan := .step choices152 bits1228 plan2970

def plan4871 : Plan := .step choices152 bits1227 plan2971

def plan4872 : Plan := .step choices152 bits1226 plan2972

def plan4873 : Plan := .step choices152 bits1223 plan2973

def plan4874 : Plan := .step choices152 bits1224 plan2974

def plan4875 : Plan := .step choices152 bits1223 plan2975

def plan4876 : Plan := .step choices152 bits1220 plan2976

def plan4877 : Plan := .step choices152 bits1220 plan2986

def plan4878 : Plan := .step choices152 bits1223 plan3000

def plan4879 : Plan := .step choices152 bits1224 plan3001

def plan4880 : Plan := .step choices152 bits1223 plan3002

def plan4881 : Plan := .step choices152 bits1220 plan3007

def plan4882 : Plan := .step choices152 bits1226 plan3077

def plan4883 : Plan := .step choices152 bits1227 plan3078

def plan4884 : Plan := .step choices152 bits1226 plan3079

def plan4885 : Plan := .step choices152 bits1228 plan3080

def plan4886 : Plan := .step choices152 bits1227 plan3081

def plan4887 : Plan := .step choices152 bits1226 plan3082

def plan4888 : Plan := .step choices152 bits1223 plan3090

def plan4889 : Plan := .step choices152 bits1224 plan3091

def plan4890 : Plan := .step choices152 bits1223 plan3092

def plan4891 : Plan := .step choices152 bits1220 plan3097

def plan4892 : Plan := .step choices155 bits1198 plan2873

def plan4893 : Plan := .step choices155 bits1199 plan2874

def plan4894 : Plan := .step choices155 bits1198 plan2875

def plan4895 : Plan := .step choices155 bits1200 plan2876

def plan4896 : Plan := .step choices155 bits1202 plan2877

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


