-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans055
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:50:17.97146+00:00
-- url     : https://prove2.me/theorems/f69b5cf8-6612-44b7-a37b-36bb7cda16c4
-- title:
--   Endpoint22 Reach Plans055 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans055 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan5348`, `ThreeBoundEndpoint22Reachable.plan5349`, `ThreeBoundEndpoint22Reachable.plan5350`, `ThreeBoundEndpoint22Reachable.plan5351`, `ThreeBoundEndpoint22Reachable.plan5352`, `ThreeBoundEndpoint22Reachable.plan5353`, `ThreeBoundEndpoint22Reachable.plan5285`, `ThreeBoundEndpoint22Reachable.plan5354`, `ThreeBoundEndpoint22Reachable.plan5355`, `ThreeBoundEndpoint22Reachable.plan5356`, `ThreeBoundEndpoint22Reachable.plan5357`, `ThreeBoundEndpoint22Reachable.plan5358`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans055.lean, lines 1–209.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
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
def plan5281 : Plan := .step choices162 bits1398 plan3218

def plan5282 : Plan := .step choices162 bits1400 plan3219

def plan5283 : Plan := .step choices162 bits1399 plan3220

def plan5284 : Plan := .step choices162 bits1398 plan3221

def plan5285 : Plan := .step choices162 bits1401 plan3222

def plan5286 : Plan := .step choices162 bits1397 plan3223

def plan5287 : Plan := .step choices162 bits1398 plan3224

def plan5288 : Plan := .step choices162 bits1397 plan3225

def plan5289 : Plan := .step choices162 bits1399 plan3226

def plan5290 : Plan := .step choices162 bits1396 plan3227

def plan5291 : Plan := .step choices162 bits1397 plan3228

def plan5292 : Plan := .step choices162 bits1396 plan3230

def plan5293 : Plan := .step choices162 bits1398 plan3231

def plan5294 : Plan := .step choices162 bits1397 plan3232

def plan5295 : Plan := .step choices162 bits1400 plan3233

def plan5296 : Plan := .step choices162 bits1399 plan3234

def plan5297 : Plan := .step choices162 bits1398 plan3235

def plan5298 : Plan := .step choices162 bits1402 plan3236

def plan5299 : Plan := .step choices162 bits1401 plan3237

def plan5300 : Plan := .step choices162 bits1400 plan3238

def plan5301 : Plan := .step choices162 bits1399 plan3239

def plan5302 : Plan := .step choices163 bits1400 plan3177

def plan5303 : Plan := .step choices163 bits1401 plan3178

def plan5304 : Plan := .step choices163 bits1400 plan3179

def plan5305 : Plan := .step choices163 bits1402 plan3180

def plan5306 : Plan := .step choices163 bits1401 plan3181

def plan5307 : Plan := .step choices163 bits1400 plan3182

def plan5308 : Plan := .step choices163 bits1403 plan3183

def plan5309 : Plan := .step choices163 bits1402 plan3184

def plan5310 : Plan := .step choices163 bits1401 plan3185

def plan5311 : Plan := .step choices163 bits1400 plan3186

def plan5312 : Plan := .step choices163 bits1404 plan3187

def plan5313 : Plan := .step choices163 bits1399 plan3216

def plan5314 : Plan := .step choices163 bits1400 plan3217

def plan5315 : Plan := .step choices163 bits1399 plan3218

def plan5316 : Plan := .step choices163 bits1401 plan3219

def plan5317 : Plan := .step choices163 bits1400 plan3220

def plan5318 : Plan := .step choices163 bits1399 plan3221

def plan5319 : Plan := .step choices163 bits1402 plan3222

def plan5320 : Plan := .step choices163 bits1398 plan3223

def plan5321 : Plan := .step choices163 bits1399 plan3224

def plan5322 : Plan := .step choices163 bits1398 plan3225

def plan5323 : Plan := .step choices163 bits1400 plan3226

def plan5324 : Plan := .step choices163 bits1397 plan3227

def plan5325 : Plan := .step choices163 bits1398 plan3228

def plan5326 : Plan := .step choices163 bits1396 plan3229

def plan5327 : Plan := .step choices163 bits1397 plan3230

def plan5328 : Plan := .step choices163 bits1399 plan3231

def plan5329 : Plan := .step choices163 bits1398 plan3232

def plan5330 : Plan := .step choices163 bits1401 plan3233

def plan5331 : Plan := .step choices163 bits1400 plan3234

def plan5332 : Plan := .step choices163 bits1399 plan3235

def plan5333 : Plan := .step choices163 bits1403 plan3236

def plan5334 : Plan := .step choices163 bits1402 plan3237

def plan5335 : Plan := .step choices163 bits1401 plan3238

def plan5336 : Plan := .step choices163 bits1400 plan3239

def plan5337 : Plan := .step choices164 bits1405 plan3187

def plan5338 : Plan := .step choices164 bits1404 plan3236

def plan5339 : Plan := .step choices164 bits1403 plan3237

def plan5340 : Plan := .step choices164 bits1402 plan3238

def plan5341 : Plan := .step choices164 bits1401 plan3239

def plan5342 : Plan := .step choices167 bits430 plan3240

def plan5343 : Plan := .step choices167 bits431 plan3241

def plan5344 : Plan := .step choices168 bits432 plan3241

def plan5345 : Plan := .step choices170 bits608 plan3248

def plan5346 : Plan := .step choices171 bits604 plan3242

def plan5347 : Plan := .step choices171 bits607 plan3243

def plan5348 : Plan := .step choices171 bits608 plan3244

def plan5349 : Plan := .step choices171 bits607 plan3245

def plan5350 : Plan := .step choices171 bits639 plan3246

def plan5351 : Plan := .step choices171 bits611 plan3247

def plan5352 : Plan := .step choices171 bits612 plan3248

def plan5353 : Plan := .step choices171 bits611 plan3249

def plan5354 : Plan := .step choices171 bits610 plan3250

def plan5355 : Plan := .step choices171 bits610 plan3251

def plan5356 : Plan := .step choices172 bits640 plan3246

def plan5357 : Plan := .step choices172 bits616 plan3247

def plan5358 : Plan := .step choices172 bits617 plan3248

def plan5359 : Plan := .step choices172 bits616 plan3249

def plan5360 : Plan := .step choices174 bits615 plan3246

def plan5361 : Plan := .step choices178 bits615 plan3246

def plan5362 : Plan := .step choices181 bits835 plan3259

def plan5363 : Plan := .step choices181 bits844 plan3269

def plan5364 : Plan := .step choices181 bits846 plan3271

def plan5365 : Plan := .step choices181 bits844 plan3272

def plan5366 : Plan := .step choices182 bits828 plan3252

def plan5367 : Plan := .step choices182 bits836 plan3253

def plan5368 : Plan := .step choices182 bits828 plan3254

def plan5369 : Plan := .step choices182 bits918 plan3255

def plan5370 : Plan := .step choices182 bits843 plan3256

def plan5371 : Plan := .step choices182 bits845 plan3257

def plan5372 : Plan := .step choices182 bits843 plan3258

def plan5373 : Plan := .step choices182 bits847 plan3259

def plan5374 : Plan := .step choices182 bits845 plan3260

def plan5375 : Plan := .step choices182 bits843 plan3261

def plan5376 : Plan := .step choices182 bits843 plan3262

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


