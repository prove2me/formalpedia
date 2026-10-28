-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans054
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans054
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:40.264207+00:00
-- url     : https://prove2.me/theorems/48259b03-1c57-45e7-a497-bb2636bac9e9
-- title:
--   Endpoint22 Reach Plans054 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans054 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5253`, `ThreeBoundEndpoint22Reachable.plan5254`, `ThreeBoundEndpoint22Reachable.plan5255`, `ThreeBoundEndpoint22Reachable.plan5256`, `ThreeBoundEndpoint22Reachable.plan5257`, `ThreeBoundEndpoint22Reachable.plan5258`, `ThreeBoundEndpoint22Reachable.plan5190`, `ThreeBoundEndpoint22Reachable.plan5259`, `ThreeBoundEndpoint22Reachable.plan5260`, `ThreeBoundEndpoint22Reachable.plan5261`, `ThreeBoundEndpoint22Reachable.plan5262`, `ThreeBoundEndpoint22Reachable.plan5263`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans054.lean, lines 1–204.

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
def plan5185 : Plan := .step choices159 bits1398 plan3232

def plan5186 : Plan := .step choices159 bits1401 plan3233

def plan5187 : Plan := .step choices159 bits1400 plan3234

def plan5188 : Plan := .step choices159 bits1399 plan3235

def plan5189 : Plan := .step choices159 bits1403 plan3236

def plan5190 : Plan := .step choices159 bits1402 plan3237

def plan5191 : Plan := .step choices159 bits1401 plan3238

def plan5192 : Plan := .step choices159 bits1400 plan3239

def plan5193 : Plan := .step choices160 bits1401 plan3177

def plan5194 : Plan := .step choices160 bits1402 plan3178

def plan5195 : Plan := .step choices160 bits1401 plan3179

def plan5196 : Plan := .step choices160 bits1403 plan3180

def plan5197 : Plan := .step choices160 bits1402 plan3181

def plan5198 : Plan := .step choices160 bits1401 plan3182

def plan5199 : Plan := .step choices160 bits1404 plan3183

def plan5200 : Plan := .step choices160 bits1403 plan3184

def plan5201 : Plan := .step choices160 bits1402 plan3185

def plan5202 : Plan := .step choices160 bits1401 plan3186

def plan5203 : Plan := .step choices160 bits1405 plan3187

def plan5204 : Plan := .step choices160 bits1404 plan3236

def plan5205 : Plan := .step choices160 bits1403 plan3237

def plan5206 : Plan := .step choices160 bits1402 plan3238

def plan5207 : Plan := .step choices160 bits1401 plan3239

def plan5208 : Plan := .step choices161 bits1406 plan3187

def plan5209 : Plan := .step choices162 bits1396 plan3143

def plan5210 : Plan := .step choices162 bits1397 plan3144

def plan5211 : Plan := .step choices162 bits1396 plan3146

def plan5212 : Plan := .step choices162 bits1397 plan3147

def plan5213 : Plan := .step choices162 bits1398 plan3148

def plan5214 : Plan := .step choices162 bits1397 plan3149

def plan5215 : Plan := .step choices162 bits1399 plan3150

def plan5216 : Plan := .step choices162 bits1396 plan3151

def plan5217 : Plan := .step choices162 bits1397 plan3152

def plan5218 : Plan := .step choices162 bits1396 plan3154

def plan5219 : Plan := .step choices162 bits1398 plan3155

def plan5220 : Plan := .step choices162 bits1397 plan3156

def plan5221 : Plan := .step choices162 bits1398 plan3157

def plan5222 : Plan := .step choices162 bits1399 plan3158

def plan5223 : Plan := .step choices162 bits1398 plan3159

def plan5224 : Plan := .step choices162 bits1400 plan3160

def plan5225 : Plan := .step choices162 bits1399 plan3161

def plan5226 : Plan := .step choices162 bits1398 plan3162

def plan5227 : Plan := .step choices162 bits1401 plan3163

def plan5228 : Plan := .step choices162 bits1397 plan3164

def plan5229 : Plan := .step choices162 bits1398 plan3165

def plan5230 : Plan := .step choices162 bits1397 plan3166

def plan5231 : Plan := .step choices162 bits1399 plan3167

def plan5232 : Plan := .step choices162 bits1396 plan3168

def plan5233 : Plan := .step choices162 bits1397 plan3169

def plan5234 : Plan := .step choices162 bits1396 plan3171

def plan5235 : Plan := .step choices162 bits1398 plan3172

def plan5236 : Plan := .step choices162 bits1397 plan3173

def plan5237 : Plan := .step choices162 bits1400 plan3174

def plan5238 : Plan := .step choices162 bits1399 plan3175

def plan5239 : Plan := .step choices162 bits1398 plan3176

def plan5240 : Plan := .step choices162 bits1399 plan3177

def plan5241 : Plan := .step choices162 bits1400 plan3178

def plan5242 : Plan := .step choices162 bits1399 plan3179

def plan5243 : Plan := .step choices162 bits1401 plan3180

def plan5244 : Plan := .step choices162 bits1400 plan3181

def plan5245 : Plan := .step choices162 bits1399 plan3182

def plan5246 : Plan := .step choices162 bits1402 plan3183

def plan5247 : Plan := .step choices162 bits1401 plan3184

def plan5248 : Plan := .step choices162 bits1400 plan3185

def plan5249 : Plan := .step choices162 bits1399 plan3186

def plan5250 : Plan := .step choices162 bits1403 plan3187

def plan5251 : Plan := .step choices162 bits1396 plan3188

def plan5252 : Plan := .step choices162 bits1396 plan3189

def plan5253 : Plan := .step choices162 bits1397 plan3190

def plan5254 : Plan := .step choices162 bits1396 plan3191

def plan5255 : Plan := .step choices162 bits1398 plan3192

def plan5256 : Plan := .step choices162 bits1396 plan3193

def plan5257 : Plan := .step choices162 bits1397 plan3194

def plan5258 : Plan := .step choices162 bits1396 plan3195

def plan5259 : Plan := .step choices162 bits1397 plan3196

def plan5260 : Plan := .step choices162 bits1398 plan3197

def plan5261 : Plan := .step choices162 bits1397 plan3198

def plan5262 : Plan := .step choices162 bits1399 plan3199

def plan5263 : Plan := .step choices162 bits1398 plan3200

def plan5264 : Plan := .step choices162 bits1397 plan3201

def plan5265 : Plan := .step choices162 bits1400 plan3202

def plan5266 : Plan := .step choices162 bits1396 plan3203

def plan5267 : Plan := .step choices162 bits1397 plan3204

def plan5268 : Plan := .step choices162 bits1396 plan3205

def plan5269 : Plan := .step choices162 bits1396 plan3206

def plan5270 : Plan := .step choices162 bits1397 plan3207

def plan5271 : Plan := .step choices162 bits1396 plan3208

def plan5272 : Plan := .step choices162 bits1398 plan3209

def plan5273 : Plan := .step choices162 bits1396 plan3210

def plan5274 : Plan := .step choices162 bits1397 plan3211

def plan5275 : Plan := .step choices162 bits1396 plan3212

def plan5276 : Plan := .step choices162 bits1399 plan3213

def plan5277 : Plan := .step choices162 bits1398 plan3214

def plan5278 : Plan := .step choices162 bits1397 plan3215

def plan5279 : Plan := .step choices162 bits1398 plan3216

def plan5280 : Plan := .step choices162 bits1399 plan3217

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


