-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans065
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T01:58:10.910982+00:00
-- url     : https://prove2.me/theorems/67ccf3dc-14ae-4922-a2be-138a466e65e0
-- title:
--   Endpoint22 Reach Plans065 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans065 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6307`, `ThreeBoundEndpoint22Reachable.plan6308`, `ThreeBoundEndpoint22Reachable.plan6309`, `ThreeBoundEndpoint22Reachable.plan6244`, `ThreeBoundEndpoint22Reachable.plan6310`, `ThreeBoundEndpoint22Reachable.plan6311`, `ThreeBoundEndpoint22Reachable.plan6312`, `ThreeBoundEndpoint22Reachable.plan6313`, `ThreeBoundEndpoint22Reachable.plan6314`, `ThreeBoundEndpoint22Reachable.plan6315`, `ThreeBoundEndpoint22Reachable.plan6316`, `ThreeBoundEndpoint22Reachable.plan6317`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans065.lean, lines 1–212.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
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
def plan6241 : Plan := .step choices291 bits1647 plan3640

def plan6242 : Plan := .step choices291 bits1646 plan3641

def plan6243 : Plan := .step choices291 bits1645 plan3642

def plan6244 : Plan := .step choices291 bits1648 plan3643

def plan6245 : Plan := .step choices291 bits1647 plan3644

def plan6246 : Plan := .step choices291 bits1646 plan3645

def plan6247 : Plan := .step choices291 bits1645 plan3646

def plan6248 : Plan := .step choices291 bits1649 plan3647

def plan6249 : Plan := .step choices291 bits1648 plan3648

def plan6250 : Plan := .step choices291 bits1647 plan3649

def plan6251 : Plan := .step choices291 bits1646 plan3650

def plan6252 : Plan := .step choices291 bits1645 plan3651

def plan6253 : Plan := .step choices292 bits1650 plan3647

def plan6254 : Plan := .step choices294 bits1647 plan3643

def plan6255 : Plan := .step choices294 bits1648 plan3647

def plan6256 : Plan := .step choices294 bits1647 plan3648

def plan6257 : Plan := .step choices295 bits1649 plan3647

def plan6258 : Plan := .step choices295 bits1648 plan3648

def plan6259 : Plan := .step choices295 bits1647 plan3649

def plan6260 : Plan := .step choices295 bits1646 plan3650

def plan6261 : Plan := .step choices295 bits1645 plan3651

def plan6262 : Plan := .step choices296 bits1283 plan3652

def plan6263 : Plan := .step choices300 bits1421 plan3653

def plan6264 : Plan := .step choices301 bits1422 plan3653

def plan6265 : Plan := .step choices302 bits1421 plan3653

def plan6266 : Plan := .step choices307 bits1587 plan3654

def plan6267 : Plan := .step choices308 bits1588 plan3654

def plan6268 : Plan := .step choices310 bits1587 plan3654

def plan6269 : Plan := .step choices317 bits1651 plan3655

def plan6270 : Plan := .step choices318 bits1652 plan3655

def plan6271 : Plan := .step choices321 bits1651 plan3655

def plan6272 : Plan := .step choices324 bits1716 plan3656

def plan6273 : Plan := .step choices325 bits1717 plan3656

def plan6274 : Plan := .step choices328 bits1716 plan3656

def plan6275 : Plan := .step choices329 bits1763 plan3657

def plan6276 : Plan := .step choices165 bits618 plan5344

def plan6277 : Plan := .step choices166 bits618 plan5343

def plan6278 : Plan := .step choices166 bits619 plan5344

def plan6279 : Plan := .step choices167 bits618 plan5342

def plan6280 : Plan := .step choices167 bits619 plan5343

def plan6281 : Plan := .step choices167 bits620 plan5344

def plan6282 : Plan := .step choices168 bits621 plan5344

def plan6283 : Plan := .step choices169 bits901 plan5352

def plan6284 : Plan := .step choices169 bits903 plan5357

def plan6285 : Plan := .step choices169 bits905 plan5358

def plan6286 : Plan := .step choices169 bits903 plan5359

def plan6287 : Plan := .step choices170 bits902 plan5345

def plan6288 : Plan := .step choices170 bits902 plan5348

def plan6289 : Plan := .step choices170 bits904 plan5351

def plan6290 : Plan := .step choices170 bits906 plan5352

def plan6291 : Plan := .step choices170 bits904 plan5353

def plan6292 : Plan := .step choices170 bits908 plan5357

def plan6293 : Plan := .step choices170 bits909 plan5358

def plan6294 : Plan := .step choices170 bits908 plan5359

def plan6295 : Plan := .step choices170 bits907 plan5360

def plan6296 : Plan := .step choices170 bits907 plan5361

def plan6297 : Plan := .step choices171 bits902 plan5346

def plan6298 : Plan := .step choices171 bits904 plan5347

def plan6299 : Plan := .step choices171 bits906 plan5348

def plan6300 : Plan := .step choices171 bits904 plan5349

def plan6301 : Plan := .step choices171 bits908 plan5351

def plan6302 : Plan := .step choices171 bits909 plan5352

def plan6303 : Plan := .step choices171 bits908 plan5353

def plan6304 : Plan := .step choices171 bits907 plan5354

def plan6305 : Plan := .step choices171 bits907 plan5355

def plan6306 : Plan := .step choices171 bits912 plan5357

def plan6307 : Plan := .step choices171 bits913 plan5358

def plan6308 : Plan := .step choices171 bits912 plan5359

def plan6309 : Plan := .step choices171 bits911 plan5360

def plan6310 : Plan := .step choices171 bits911 plan5361

def plan6311 : Plan := .step choices172 bits916 plan5357

def plan6312 : Plan := .step choices172 bits917 plan5358

def plan6313 : Plan := .step choices172 bits916 plan5359

def plan6314 : Plan := .step choices173 bits910 plan5350

def plan6315 : Plan := .step choices173 bits914 plan5356

def plan6316 : Plan := .step choices174 bits915 plan5356

def plan6317 : Plan := .step choices177 bits910 plan5350

def plan6318 : Plan := .step choices177 bits914 plan5356

def plan6319 : Plan := .step choices178 bits915 plan5356

def plan6320 : Plan := .step choices180 bits1125 plan5364

def plan6321 : Plan := .step choices180 bits1126 plan5373

def plan6322 : Plan := .step choices180 bits1128 plan5382

def plan6323 : Plan := .step choices180 bits1131 plan5384

def plan6324 : Plan := .step choices180 bits1128 plan5385

def plan6325 : Plan := .step choices180 bits1134 plan5396

def plan6326 : Plan := .step choices180 bits1137 plan5397

def plan6327 : Plan := .step choices180 bits1134 plan5398

def plan6328 : Plan := .step choices180 bits1140 plan5399

def plan6329 : Plan := .step choices180 bits1137 plan5400

def plan6330 : Plan := .step choices180 bits1134 plan5401

def plan6331 : Plan := .step choices180 bits1134 plan5405

def plan6332 : Plan := .step choices180 bits1134 plan5412

def plan6333 : Plan := .step choices181 bits1126 plan5362

def plan6334 : Plan := .step choices181 bits1128 plan5363

def plan6335 : Plan := .step choices181 bits1131 plan5364

def plan6336 : Plan := .step choices181 bits1128 plan5365

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


