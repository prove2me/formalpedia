-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans052
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans052
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:00.780984+00:00
-- url     : https://prove2.me/theorems/9b2a6899-ee43-4f84-9ef0-80a12fedc2af
-- title:
--   Endpoint22 Reach Plans052 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans052 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5061`, `ThreeBoundEndpoint22Reachable.plan5062`, `ThreeBoundEndpoint22Reachable.plan5063`, `ThreeBoundEndpoint22Reachable.plan5064`, `ThreeBoundEndpoint22Reachable.plan5065`, `ThreeBoundEndpoint22Reachable.plan5066`, `ThreeBoundEndpoint22Reachable.plan5067`, `ThreeBoundEndpoint22Reachable.plan4998`, `ThreeBoundEndpoint22Reachable.plan5068`, `ThreeBoundEndpoint22Reachable.plan5069`, `ThreeBoundEndpoint22Reachable.plan5070`, `ThreeBoundEndpoint22Reachable.plan5071`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans052.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
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
def plan4993 : Plan := .step choices156 bits1227 plan3081

def plan4994 : Plan := .step choices156 bits1226 plan3082

def plan4995 : Plan := .step choices156 bits1223 plan3090

def plan4996 : Plan := .step choices156 bits1224 plan3091

def plan4997 : Plan := .step choices156 bits1223 plan3092

def plan4998 : Plan := .step choices156 bits1220 plan3097

def plan4999 : Plan := .step choices158 bits1396 plan3111

def plan5000 : Plan := .step choices158 bits1397 plan3112

def plan5001 : Plan := .step choices158 bits1396 plan3113

def plan5002 : Plan := .step choices158 bits1396 plan3114

def plan5003 : Plan := .step choices158 bits1396 plan3115

def plan5004 : Plan := .step choices158 bits1397 plan3116

def plan5005 : Plan := .step choices158 bits1396 plan3117

def plan5006 : Plan := .step choices158 bits1398 plan3118

def plan5007 : Plan := .step choices158 bits1396 plan3119

def plan5008 : Plan := .step choices158 bits1397 plan3120

def plan5009 : Plan := .step choices158 bits1396 plan3121

def plan5010 : Plan := .step choices158 bits1397 plan3122

def plan5011 : Plan := .step choices158 bits1398 plan3123

def plan5012 : Plan := .step choices158 bits1397 plan3124

def plan5013 : Plan := .step choices158 bits1399 plan3125

def plan5014 : Plan := .step choices158 bits1398 plan3126

def plan5015 : Plan := .step choices158 bits1397 plan3127

def plan5016 : Plan := .step choices158 bits1400 plan3128

def plan5017 : Plan := .step choices158 bits1396 plan3129

def plan5018 : Plan := .step choices158 bits1397 plan3130

def plan5019 : Plan := .step choices158 bits1396 plan3131

def plan5020 : Plan := .step choices158 bits1396 plan3132

def plan5021 : Plan := .step choices158 bits1397 plan3133

def plan5022 : Plan := .step choices158 bits1396 plan3134

def plan5023 : Plan := .step choices158 bits1398 plan3135

def plan5024 : Plan := .step choices158 bits1396 plan3136

def plan5025 : Plan := .step choices158 bits1397 plan3137

def plan5026 : Plan := .step choices158 bits1396 plan3138

def plan5027 : Plan := .step choices158 bits1399 plan3139

def plan5028 : Plan := .step choices158 bits1398 plan3140

def plan5029 : Plan := .step choices158 bits1397 plan3141

def plan5030 : Plan := .step choices158 bits1396 plan3143

def plan5031 : Plan := .step choices158 bits1397 plan3144

def plan5032 : Plan := .step choices158 bits1396 plan3146

def plan5033 : Plan := .step choices158 bits1397 plan3147

def plan5034 : Plan := .step choices158 bits1398 plan3148

def plan5035 : Plan := .step choices158 bits1397 plan3149

def plan5036 : Plan := .step choices158 bits1399 plan3150

def plan5037 : Plan := .step choices158 bits1396 plan3151

def plan5038 : Plan := .step choices158 bits1397 plan3152

def plan5039 : Plan := .step choices158 bits1396 plan3154

def plan5040 : Plan := .step choices158 bits1398 plan3155

def plan5041 : Plan := .step choices158 bits1397 plan3156

def plan5042 : Plan := .step choices158 bits1398 plan3157

def plan5043 : Plan := .step choices158 bits1399 plan3158

def plan5044 : Plan := .step choices158 bits1398 plan3159

def plan5045 : Plan := .step choices158 bits1400 plan3160

def plan5046 : Plan := .step choices158 bits1399 plan3161

def plan5047 : Plan := .step choices158 bits1398 plan3162

def plan5048 : Plan := .step choices158 bits1401 plan3163

def plan5049 : Plan := .step choices158 bits1397 plan3164

def plan5050 : Plan := .step choices158 bits1398 plan3165

def plan5051 : Plan := .step choices158 bits1397 plan3166

def plan5052 : Plan := .step choices158 bits1399 plan3167

def plan5053 : Plan := .step choices158 bits1396 plan3168

def plan5054 : Plan := .step choices158 bits1397 plan3169

def plan5055 : Plan := .step choices158 bits1396 plan3171

def plan5056 : Plan := .step choices158 bits1398 plan3172

def plan5057 : Plan := .step choices158 bits1397 plan3173

def plan5058 : Plan := .step choices158 bits1400 plan3174

def plan5059 : Plan := .step choices158 bits1399 plan3175

def plan5060 : Plan := .step choices158 bits1398 plan3176

def plan5061 : Plan := .step choices158 bits1399 plan3177

def plan5062 : Plan := .step choices158 bits1400 plan3178

def plan5063 : Plan := .step choices158 bits1399 plan3179

def plan5064 : Plan := .step choices158 bits1401 plan3180

def plan5065 : Plan := .step choices158 bits1400 plan3181

def plan5066 : Plan := .step choices158 bits1399 plan3182

def plan5067 : Plan := .step choices158 bits1402 plan3183

def plan5068 : Plan := .step choices158 bits1401 plan3184

def plan5069 : Plan := .step choices158 bits1400 plan3185

def plan5070 : Plan := .step choices158 bits1399 plan3186

def plan5071 : Plan := .step choices158 bits1403 plan3187

def plan5072 : Plan := .step choices158 bits1396 plan3188

def plan5073 : Plan := .step choices158 bits1396 plan3189

def plan5074 : Plan := .step choices158 bits1397 plan3190

def plan5075 : Plan := .step choices158 bits1396 plan3191

def plan5076 : Plan := .step choices158 bits1398 plan3192

def plan5077 : Plan := .step choices158 bits1396 plan3193

def plan5078 : Plan := .step choices158 bits1397 plan3194

def plan5079 : Plan := .step choices158 bits1396 plan3195

def plan5080 : Plan := .step choices158 bits1397 plan3196

def plan5081 : Plan := .step choices158 bits1398 plan3197

def plan5082 : Plan := .step choices158 bits1397 plan3198

def plan5083 : Plan := .step choices158 bits1399 plan3199

def plan5084 : Plan := .step choices158 bits1398 plan3200

def plan5085 : Plan := .step choices158 bits1397 plan3201

def plan5086 : Plan := .step choices158 bits1400 plan3202

def plan5087 : Plan := .step choices158 bits1396 plan3203

def plan5088 : Plan := .step choices158 bits1397 plan3204

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


