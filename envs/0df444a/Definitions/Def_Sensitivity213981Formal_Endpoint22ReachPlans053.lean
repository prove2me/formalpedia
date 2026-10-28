-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans053
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:14.866468+00:00
-- url     : https://prove2.me/theorems/a160c15d-2084-43da-b414-12d68d8fa02a
-- title:
--   Endpoint22 Reach Plans053 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans053 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5157`, `ThreeBoundEndpoint22Reachable.plan5158`, `ThreeBoundEndpoint22Reachable.plan5159`, `ThreeBoundEndpoint22Reachable.plan5160`, `ThreeBoundEndpoint22Reachable.plan5161`, `ThreeBoundEndpoint22Reachable.plan5162`, `ThreeBoundEndpoint22Reachable.plan5094`, `ThreeBoundEndpoint22Reachable.plan5163`, `ThreeBoundEndpoint22Reachable.plan5164`, `ThreeBoundEndpoint22Reachable.plan5165`, `ThreeBoundEndpoint22Reachable.plan5166`, `ThreeBoundEndpoint22Reachable.plan5167`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans053.lean, lines 1–204.

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
def plan5089 : Plan := .step choices158 bits1396 plan3205

def plan5090 : Plan := .step choices158 bits1396 plan3206

def plan5091 : Plan := .step choices158 bits1397 plan3207

def plan5092 : Plan := .step choices158 bits1396 plan3208

def plan5093 : Plan := .step choices158 bits1398 plan3209

def plan5094 : Plan := .step choices158 bits1396 plan3210

def plan5095 : Plan := .step choices158 bits1397 plan3211

def plan5096 : Plan := .step choices158 bits1396 plan3212

def plan5097 : Plan := .step choices158 bits1399 plan3213

def plan5098 : Plan := .step choices158 bits1398 plan3214

def plan5099 : Plan := .step choices158 bits1397 plan3215

def plan5100 : Plan := .step choices158 bits1398 plan3216

def plan5101 : Plan := .step choices158 bits1399 plan3217

def plan5102 : Plan := .step choices158 bits1398 plan3218

def plan5103 : Plan := .step choices158 bits1400 plan3219

def plan5104 : Plan := .step choices158 bits1399 plan3220

def plan5105 : Plan := .step choices158 bits1398 plan3221

def plan5106 : Plan := .step choices158 bits1401 plan3222

def plan5107 : Plan := .step choices158 bits1397 plan3223

def plan5108 : Plan := .step choices158 bits1398 plan3224

def plan5109 : Plan := .step choices158 bits1397 plan3225

def plan5110 : Plan := .step choices158 bits1399 plan3226

def plan5111 : Plan := .step choices158 bits1396 plan3227

def plan5112 : Plan := .step choices158 bits1397 plan3228

def plan5113 : Plan := .step choices158 bits1396 plan3230

def plan5114 : Plan := .step choices158 bits1398 plan3231

def plan5115 : Plan := .step choices158 bits1397 plan3232

def plan5116 : Plan := .step choices158 bits1400 plan3233

def plan5117 : Plan := .step choices158 bits1399 plan3234

def plan5118 : Plan := .step choices158 bits1398 plan3235

def plan5119 : Plan := .step choices158 bits1402 plan3236

def plan5120 : Plan := .step choices158 bits1401 plan3237

def plan5121 : Plan := .step choices158 bits1400 plan3238

def plan5122 : Plan := .step choices158 bits1399 plan3239

def plan5123 : Plan := .step choices159 bits1396 plan3142

def plan5124 : Plan := .step choices159 bits1397 plan3143

def plan5125 : Plan := .step choices159 bits1398 plan3144

def plan5126 : Plan := .step choices159 bits1396 plan3145

def plan5127 : Plan := .step choices159 bits1397 plan3146

def plan5128 : Plan := .step choices159 bits1398 plan3147

def plan5129 : Plan := .step choices159 bits1399 plan3148

def plan5130 : Plan := .step choices159 bits1398 plan3149

def plan5131 : Plan := .step choices159 bits1400 plan3150

def plan5132 : Plan := .step choices159 bits1397 plan3151

def plan5133 : Plan := .step choices159 bits1398 plan3152

def plan5134 : Plan := .step choices159 bits1396 plan3153

def plan5135 : Plan := .step choices159 bits1397 plan3154

def plan5136 : Plan := .step choices159 bits1399 plan3155

def plan5137 : Plan := .step choices159 bits1398 plan3156

def plan5138 : Plan := .step choices159 bits1399 plan3157

def plan5139 : Plan := .step choices159 bits1400 plan3158

def plan5140 : Plan := .step choices159 bits1399 plan3159

def plan5141 : Plan := .step choices159 bits1401 plan3160

def plan5142 : Plan := .step choices159 bits1400 plan3161

def plan5143 : Plan := .step choices159 bits1399 plan3162

def plan5144 : Plan := .step choices159 bits1402 plan3163

def plan5145 : Plan := .step choices159 bits1398 plan3164

def plan5146 : Plan := .step choices159 bits1399 plan3165

def plan5147 : Plan := .step choices159 bits1398 plan3166

def plan5148 : Plan := .step choices159 bits1400 plan3167

def plan5149 : Plan := .step choices159 bits1397 plan3168

def plan5150 : Plan := .step choices159 bits1398 plan3169

def plan5151 : Plan := .step choices159 bits1396 plan3170

def plan5152 : Plan := .step choices159 bits1397 plan3171

def plan5153 : Plan := .step choices159 bits1399 plan3172

def plan5154 : Plan := .step choices159 bits1398 plan3173

def plan5155 : Plan := .step choices159 bits1401 plan3174

def plan5156 : Plan := .step choices159 bits1400 plan3175

def plan5157 : Plan := .step choices159 bits1399 plan3176

def plan5158 : Plan := .step choices159 bits1400 plan3177

def plan5159 : Plan := .step choices159 bits1401 plan3178

def plan5160 : Plan := .step choices159 bits1400 plan3179

def plan5161 : Plan := .step choices159 bits1402 plan3180

def plan5162 : Plan := .step choices159 bits1401 plan3181

def plan5163 : Plan := .step choices159 bits1400 plan3182

def plan5164 : Plan := .step choices159 bits1403 plan3183

def plan5165 : Plan := .step choices159 bits1402 plan3184

def plan5166 : Plan := .step choices159 bits1401 plan3185

def plan5167 : Plan := .step choices159 bits1400 plan3186

def plan5168 : Plan := .step choices159 bits1404 plan3187

def plan5169 : Plan := .step choices159 bits1399 plan3216

def plan5170 : Plan := .step choices159 bits1400 plan3217

def plan5171 : Plan := .step choices159 bits1399 plan3218

def plan5172 : Plan := .step choices159 bits1401 plan3219

def plan5173 : Plan := .step choices159 bits1400 plan3220

def plan5174 : Plan := .step choices159 bits1399 plan3221

def plan5175 : Plan := .step choices159 bits1402 plan3222

def plan5176 : Plan := .step choices159 bits1398 plan3223

def plan5177 : Plan := .step choices159 bits1399 plan3224

def plan5178 : Plan := .step choices159 bits1398 plan3225

def plan5179 : Plan := .step choices159 bits1400 plan3226

def plan5180 : Plan := .step choices159 bits1397 plan3227

def plan5181 : Plan := .step choices159 bits1398 plan3228

def plan5182 : Plan := .step choices159 bits1396 plan3229

def plan5183 : Plan := .step choices159 bits1397 plan3230

def plan5184 : Plan := .step choices159 bits1399 plan3231

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


