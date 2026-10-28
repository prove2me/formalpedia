-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans086
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:06:12.5263+00:00
-- url     : https://prove2.me/theorems/ffd85bda-9914-4eb2-a0fe-63c058f0198f
-- title:
--   Endpoint22 Reach Plans086 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans086 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8325`, `ThreeBoundEndpoint22Reachable.plan8326`, `ThreeBoundEndpoint22Reachable.plan8327`, `ThreeBoundEndpoint22Reachable.plan8328`, `ThreeBoundEndpoint22Reachable.plan8329`, `ThreeBoundEndpoint22Reachable.plan8330`, `ThreeBoundEndpoint22Reachable.plan8262`, `ThreeBoundEndpoint22Reachable.plan8331`, `ThreeBoundEndpoint22Reachable.plan8332`, `ThreeBoundEndpoint22Reachable.plan8333`, `ThreeBoundEndpoint22Reachable.plan8334`, `ThreeBoundEndpoint22Reachable.plan8335`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans086.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
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
def plan8257 : Plan := .step choices283 bits1699 plan6208

def plan8258 : Plan := .step choices283 bits1698 plan6209

def plan8259 : Plan := .step choices283 bits1698 plan6213

def plan8260 : Plan := .step choices283 bits1699 plan6216

def plan8261 : Plan := .step choices283 bits1698 plan6217

def plan8262 : Plan := .step choices283 bits1700 plan6220

def plan8263 : Plan := .step choices283 bits1699 plan6221

def plan8264 : Plan := .step choices283 bits1698 plan6222

def plan8265 : Plan := .step choices283 bits1701 plan6225

def plan8266 : Plan := .step choices283 bits1710 plan6226

def plan8267 : Plan := .step choices283 bits1698 plan6227

def plan8268 : Plan := .step choices283 bits1699 plan6228

def plan8269 : Plan := .step choices283 bits1698 plan6229

def plan8270 : Plan := .step choices283 bits1700 plan6230

def plan8271 : Plan := .step choices283 bits1699 plan6231

def plan8272 : Plan := .step choices283 bits1698 plan6232

def plan8273 : Plan := .step choices284 bits1697 plan6210

def plan8274 : Plan := .step choices284 bits1698 plan6211

def plan8275 : Plan := .step choices284 bits1697 plan6212

def plan8276 : Plan := .step choices284 bits1699 plan6213

def plan8277 : Plan := .step choices284 bits1698 plan6214

def plan8278 : Plan := .step choices284 bits1697 plan6215

def plan8279 : Plan := .step choices284 bits1700 plan6216

def plan8280 : Plan := .step choices284 bits1699 plan6217

def plan8281 : Plan := .step choices284 bits1698 plan6218

def plan8282 : Plan := .step choices284 bits1697 plan6219

def plan8283 : Plan := .step choices284 bits1701 plan6220

def plan8284 : Plan := .step choices284 bits1700 plan6221

def plan8285 : Plan := .step choices284 bits1699 plan6222

def plan8286 : Plan := .step choices284 bits1698 plan6223

def plan8287 : Plan := .step choices284 bits1697 plan6224

def plan8288 : Plan := .step choices284 bits1702 plan6225

def plan8289 : Plan := .step choices284 bits1701 plan6230

def plan8290 : Plan := .step choices284 bits1700 plan6231

def plan8291 : Plan := .step choices284 bits1699 plan6232

def plan8292 : Plan := .step choices284 bits1698 plan6233

def plan8293 : Plan := .step choices284 bits1697 plan6234

def plan8294 : Plan := .step choices285 bits1703 plan6225

def plan8295 : Plan := .step choices286 bits1711 plan6203

def plan8296 : Plan := .step choices286 bits1699 plan6220

def plan8297 : Plan := .step choices286 bits1700 plan6225

def plan8298 : Plan := .step choices286 bits1699 plan6230

def plan8299 : Plan := .step choices287 bits1710 plan6200

def plan8300 : Plan := .step choices287 bits1711 plan6201

def plan8301 : Plan := .step choices287 bits1710 plan6202

def plan8302 : Plan := .step choices287 bits1712 plan6203

def plan8303 : Plan := .step choices287 bits1711 plan6204

def plan8304 : Plan := .step choices287 bits1710 plan6205

def plan8305 : Plan := .step choices287 bits1698 plan6213

def plan8306 : Plan := .step choices287 bits1699 plan6216

def plan8307 : Plan := .step choices287 bits1698 plan6217

def plan8308 : Plan := .step choices287 bits1700 plan6220

def plan8309 : Plan := .step choices287 bits1699 plan6221

def plan8310 : Plan := .step choices287 bits1698 plan6222

def plan8311 : Plan := .step choices287 bits1701 plan6225

def plan8312 : Plan := .step choices287 bits1710 plan6226

def plan8313 : Plan := .step choices287 bits1698 plan6227

def plan8314 : Plan := .step choices287 bits1699 plan6228

def plan8315 : Plan := .step choices287 bits1698 plan6229

def plan8316 : Plan := .step choices287 bits1700 plan6230

def plan8317 : Plan := .step choices287 bits1699 plan6231

def plan8318 : Plan := .step choices287 bits1698 plan6232

def plan8319 : Plan := .step choices288 bits1702 plan6225

def plan8320 : Plan := .step choices288 bits1701 plan6230

def plan8321 : Plan := .step choices288 bits1700 plan6231

def plan8322 : Plan := .step choices288 bits1699 plan6232

def plan8323 : Plan := .step choices288 bits1698 plan6233

def plan8324 : Plan := .step choices288 bits1697 plan6234

def plan8325 : Plan := .step choices289 bits1755 plan6248

def plan8326 : Plan := .step choices289 bits1756 plan6253

def plan8327 : Plan := .step choices289 bits1755 plan6257

def plan8328 : Plan := .step choices290 bits1754 plan6235

def plan8329 : Plan := .step choices290 bits1755 plan6236

def plan8330 : Plan := .step choices290 bits1754 plan6237

def plan8331 : Plan := .step choices290 bits1754 plan6241

def plan8332 : Plan := .step choices290 bits1755 plan6244

def plan8333 : Plan := .step choices290 bits1754 plan6245

def plan8334 : Plan := .step choices290 bits1756 plan6248

def plan8335 : Plan := .step choices290 bits1755 plan6249

def plan8336 : Plan := .step choices290 bits1754 plan6250

def plan8337 : Plan := .step choices290 bits1757 plan6253

def plan8338 : Plan := .step choices290 bits1754 plan6254

def plan8339 : Plan := .step choices290 bits1755 plan6255

def plan8340 : Plan := .step choices290 bits1754 plan6256

def plan8341 : Plan := .step choices290 bits1756 plan6257

def plan8342 : Plan := .step choices290 bits1755 plan6258

def plan8343 : Plan := .step choices290 bits1754 plan6259

def plan8344 : Plan := .step choices291 bits1753 plan6238

def plan8345 : Plan := .step choices291 bits1754 plan6239

def plan8346 : Plan := .step choices291 bits1753 plan6240

def plan8347 : Plan := .step choices291 bits1755 plan6241

def plan8348 : Plan := .step choices291 bits1754 plan6242

def plan8349 : Plan := .step choices291 bits1753 plan6243

def plan8350 : Plan := .step choices291 bits1756 plan6244

def plan8351 : Plan := .step choices291 bits1755 plan6245

def plan8352 : Plan := .step choices291 bits1754 plan6246

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


