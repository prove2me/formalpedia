-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans066
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:52:13.748116+00:00
-- url     : https://prove2.me/theorems/48736bf5-6d87-4cb2-a2c0-19a53f19e797
-- title:
--   Endpoint22 Reach Plans066 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans066 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6405`, `ThreeBoundEndpoint22Reachable.plan6406`, `ThreeBoundEndpoint22Reachable.plan6407`, `ThreeBoundEndpoint22Reachable.plan6408`, `ThreeBoundEndpoint22Reachable.plan6409`, `ThreeBoundEndpoint22Reachable.plan6410`, `ThreeBoundEndpoint22Reachable.plan6411`, `ThreeBoundEndpoint22Reachable.plan6342`, `ThreeBoundEndpoint22Reachable.plan6412`, `ThreeBoundEndpoint22Reachable.plan6413`, `ThreeBoundEndpoint22Reachable.plan6414`, `ThreeBoundEndpoint22Reachable.plan6415`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans066.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
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
def plan6337 : Plan := .step choices181 bits1127 plan5367

def plan6338 : Plan := .step choices181 bits1129 plan5371

def plan6339 : Plan := .step choices181 bits1132 plan5373

def plan6340 : Plan := .step choices181 bits1129 plan5374

def plan6341 : Plan := .step choices181 bits1135 plan5381

def plan6342 : Plan := .step choices181 bits1138 plan5382

def plan6343 : Plan := .step choices181 bits1135 plan5383

def plan6344 : Plan := .step choices181 bits1141 plan5384

def plan6345 : Plan := .step choices181 bits1138 plan5385

def plan6346 : Plan := .step choices181 bits1135 plan5386

def plan6347 : Plan := .step choices181 bits1135 plan5388

def plan6348 : Plan := .step choices181 bits1135 plan5391

def plan6349 : Plan := .step choices181 bits1145 plan5396

def plan6350 : Plan := .step choices181 bits1147 plan5397

def plan6351 : Plan := .step choices181 bits1145 plan5398

def plan6352 : Plan := .step choices181 bits1149 plan5399

def plan6353 : Plan := .step choices181 bits1147 plan5400

def plan6354 : Plan := .step choices181 bits1145 plan5401

def plan6355 : Plan := .step choices181 bits1143 plan5402

def plan6356 : Plan := .step choices181 bits1143 plan5404

def plan6357 : Plan := .step choices181 bits1145 plan5405

def plan6358 : Plan := .step choices181 bits1143 plan5406

def plan6359 : Plan := .step choices181 bits1143 plan5409

def plan6360 : Plan := .step choices181 bits1143 plan5411

def plan6361 : Plan := .step choices181 bits1145 plan5412

def plan6362 : Plan := .step choices181 bits1143 plan5413

def plan6363 : Plan := .step choices182 bits1130 plan5366

def plan6364 : Plan := .step choices182 bits1133 plan5367

def plan6365 : Plan := .step choices182 bits1130 plan5368

def plan6366 : Plan := .step choices182 bits1136 plan5370

def plan6367 : Plan := .step choices182 bits1139 plan5371

def plan6368 : Plan := .step choices182 bits1136 plan5372

def plan6369 : Plan := .step choices182 bits1142 plan5373

def plan6370 : Plan := .step choices182 bits1139 plan5374

def plan6371 : Plan := .step choices182 bits1136 plan5375

def plan6372 : Plan := .step choices182 bits1136 plan5376

def plan6373 : Plan := .step choices182 bits1136 plan5377

def plan6374 : Plan := .step choices182 bits1146 plan5381

def plan6375 : Plan := .step choices182 bits1148 plan5382

def plan6376 : Plan := .step choices182 bits1146 plan5383

def plan6377 : Plan := .step choices182 bits1150 plan5384

def plan6378 : Plan := .step choices182 bits1148 plan5385

def plan6379 : Plan := .step choices182 bits1146 plan5386

def plan6380 : Plan := .step choices182 bits1144 plan5387

def plan6381 : Plan := .step choices182 bits1146 plan5388

def plan6382 : Plan := .step choices182 bits1144 plan5389

def plan6383 : Plan := .step choices182 bits1144 plan5390

def plan6384 : Plan := .step choices182 bits1146 plan5391

def plan6385 : Plan := .step choices182 bits1144 plan5392

def plan6386 : Plan := .step choices182 bits1153 plan5396

def plan6387 : Plan := .step choices182 bits1154 plan5397

def plan6388 : Plan := .step choices182 bits1153 plan5398

def plan6389 : Plan := .step choices182 bits1155 plan5399

def plan6390 : Plan := .step choices182 bits1154 plan5400

def plan6391 : Plan := .step choices182 bits1153 plan5401

def plan6392 : Plan := .step choices182 bits1152 plan5404

def plan6393 : Plan := .step choices182 bits1153 plan5405

def plan6394 : Plan := .step choices182 bits1152 plan5406

def plan6395 : Plan := .step choices182 bits1151 plan5407

def plan6396 : Plan := .step choices182 bits1151 plan5408

def plan6397 : Plan := .step choices182 bits1152 plan5411

def plan6398 : Plan := .step choices182 bits1153 plan5412

def plan6399 : Plan := .step choices182 bits1152 plan5413

def plan6400 : Plan := .step choices182 bits1151 plan5414

def plan6401 : Plan := .step choices183 bits1159 plan5396

def plan6402 : Plan := .step choices183 bits1160 plan5397

def plan6403 : Plan := .step choices183 bits1159 plan5398

def plan6404 : Plan := .step choices183 bits1161 plan5399

def plan6405 : Plan := .step choices183 bits1160 plan5400

def plan6406 : Plan := .step choices183 bits1159 plan5401

def plan6407 : Plan := .step choices184 bits1144 plan5369

def plan6408 : Plan := .step choices184 bits1151 plan5378

def plan6409 : Plan := .step choices184 bits1152 plan5379

def plan6410 : Plan := .step choices184 bits1151 plan5380

def plan6411 : Plan := .step choices184 bits1157 plan5393

def plan6412 : Plan := .step choices184 bits1158 plan5394

def plan6413 : Plan := .step choices184 bits1157 plan5395

def plan6414 : Plan := .step choices184 bits1156 plan5403

def plan6415 : Plan := .step choices184 bits1156 plan5410

def plan6416 : Plan := .step choices185 bits1158 plan5393

def plan6417 : Plan := .step choices185 bits1159 plan5394

def plan6418 : Plan := .step choices185 bits1158 plan5395

def plan6419 : Plan := .step choices185 bits1157 plan5403

def plan6420 : Plan := .step choices185 bits1157 plan5410

def plan6421 : Plan := .step choices188 bits1144 plan5369

def plan6422 : Plan := .step choices188 bits1151 plan5378

def plan6423 : Plan := .step choices188 bits1152 plan5379

def plan6424 : Plan := .step choices188 bits1151 plan5380

def plan6425 : Plan := .step choices188 bits1157 plan5393

def plan6426 : Plan := .step choices188 bits1158 plan5394

def plan6427 : Plan := .step choices188 bits1157 plan5395

def plan6428 : Plan := .step choices188 bits1156 plan5403

def plan6429 : Plan := .step choices188 bits1156 plan5410

def plan6430 : Plan := .step choices189 bits1158 plan5393

def plan6431 : Plan := .step choices189 bits1159 plan5394

def plan6432 : Plan := .step choices189 bits1158 plan5395

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


