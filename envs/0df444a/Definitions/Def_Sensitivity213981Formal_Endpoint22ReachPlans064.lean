-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans064
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:00:52.35434+00:00
-- url     : https://prove2.me/theorems/aa20a52a-54b5-48cf-9dd2-7414156e7c57
-- title:
--   Endpoint22 Reach Plans064 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans064 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6212`, `ThreeBoundEndpoint22Reachable.plan6213`, `ThreeBoundEndpoint22Reachable.plan6214`, `ThreeBoundEndpoint22Reachable.plan6215`, `ThreeBoundEndpoint22Reachable.plan6216`, `ThreeBoundEndpoint22Reachable.plan6217`, `ThreeBoundEndpoint22Reachable.plan6218`, `ThreeBoundEndpoint22Reachable.plan6219`, `ThreeBoundEndpoint22Reachable.plan6220`, `ThreeBoundEndpoint22Reachable.plan6221`, `ThreeBoundEndpoint22Reachable.plan6150`, `ThreeBoundEndpoint22Reachable.plan6222`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans064.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
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
def plan6145 : Plan := .step choices259 bits1278 plan3593

def plan6146 : Plan := .step choices259 bits1281 plan3594

def plan6147 : Plan := .step choices259 bits1280 plan3595

def plan6148 : Plan := .step choices259 bits1279 plan3596

def plan6149 : Plan := .step choices259 bits1278 plan3597

def plan6150 : Plan := .step choices259 bits1282 plan3598

def plan6151 : Plan := .step choices259 bits1281 plan3599

def plan6152 : Plan := .step choices259 bits1280 plan3600

def plan6153 : Plan := .step choices259 bits1279 plan3601

def plan6154 : Plan := .step choices259 bits1278 plan3602

def plan6155 : Plan := .step choices261 bits1275 plan3585

def plan6156 : Plan := .step choices265 bits1275 plan3585

def plan6157 : Plan := .step choices269 bits1441 plan3616

def plan6158 : Plan := .step choices270 bits1446 plan3603

def plan6159 : Plan := .step choices270 bits1447 plan3604

def plan6160 : Plan := .step choices270 bits1446 plan3605

def plan6161 : Plan := .step choices270 bits1442 plan3607

def plan6162 : Plan := .step choices270 bits1443 plan3609

def plan6163 : Plan := .step choices270 bits1442 plan3610

def plan6164 : Plan := .step choices270 bits1444 plan3612

def plan6165 : Plan := .step choices270 bits1443 plan3613

def plan6166 : Plan := .step choices270 bits1442 plan3614

def plan6167 : Plan := .step choices270 bits1445 plan3616

def plan6168 : Plan := .step choices270 bits1444 plan3617

def plan6169 : Plan := .step choices270 bits1443 plan3618

def plan6170 : Plan := .step choices270 bits1442 plan3619

def plan6171 : Plan := .step choices272 bits1443 plan3604

def plan6172 : Plan := .step choices272 bits1417 plan3612

def plan6173 : Plan := .step choices272 bits1418 plan3616

def plan6174 : Plan := .step choices272 bits1417 plan3617

def plan6175 : Plan := .step choices273 bits1415 plan3606

def plan6176 : Plan := .step choices273 bits1416 plan3607

def plan6177 : Plan := .step choices273 bits1415 plan3608

def plan6178 : Plan := .step choices273 bits1417 plan3609

def plan6179 : Plan := .step choices273 bits1416 plan3610

def plan6180 : Plan := .step choices273 bits1415 plan3611

def plan6181 : Plan := .step choices273 bits1418 plan3612

def plan6182 : Plan := .step choices273 bits1417 plan3613

def plan6183 : Plan := .step choices273 bits1416 plan3614

def plan6184 : Plan := .step choices273 bits1415 plan3615

def plan6185 : Plan := .step choices273 bits1419 plan3616

def plan6186 : Plan := .step choices273 bits1418 plan3617

def plan6187 : Plan := .step choices273 bits1417 plan3618

def plan6188 : Plan := .step choices273 bits1416 plan3619

def plan6189 : Plan := .step choices273 bits1415 plan3620

def plan6190 : Plan := .step choices274 bits1420 plan3616

def plan6191 : Plan := .step choices276 bits1443 plan3604

def plan6192 : Plan := .step choices276 bits1417 plan3612

def plan6193 : Plan := .step choices276 bits1418 plan3616

def plan6194 : Plan := .step choices276 bits1417 plan3617

def plan6195 : Plan := .step choices277 bits1419 plan3616

def plan6196 : Plan := .step choices277 bits1418 plan3617

def plan6197 : Plan := .step choices277 bits1417 plan3618

def plan6198 : Plan := .step choices277 bits1416 plan3619

def plan6199 : Plan := .step choices277 bits1415 plan3620

def plan6200 : Plan := .step choices281 bits1589 plan3625

def plan6201 : Plan := .step choices281 bits1590 plan3628

def plan6202 : Plan := .step choices281 bits1589 plan3629

def plan6203 : Plan := .step choices281 bits1591 plan3632

def plan6204 : Plan := .step choices281 bits1590 plan3633

def plan6205 : Plan := .step choices281 bits1589 plan3634

def plan6206 : Plan := .step choices283 bits1589 plan3621

def plan6207 : Plan := .step choices283 bits1583 plan3628

def plan6208 : Plan := .step choices283 bits1584 plan3632

def plan6209 : Plan := .step choices283 bits1583 plan3633

def plan6210 : Plan := .step choices284 bits1581 plan3622

def plan6211 : Plan := .step choices284 bits1582 plan3623

def plan6212 : Plan := .step choices284 bits1581 plan3624

def plan6213 : Plan := .step choices284 bits1583 plan3625

def plan6214 : Plan := .step choices284 bits1582 plan3626

def plan6215 : Plan := .step choices284 bits1581 plan3627

def plan6216 : Plan := .step choices284 bits1584 plan3628

def plan6217 : Plan := .step choices284 bits1583 plan3629

def plan6218 : Plan := .step choices284 bits1582 plan3630

def plan6219 : Plan := .step choices284 bits1581 plan3631

def plan6220 : Plan := .step choices284 bits1585 plan3632

def plan6221 : Plan := .step choices284 bits1584 plan3633

def plan6222 : Plan := .step choices284 bits1583 plan3634

def plan6223 : Plan := .step choices284 bits1582 plan3635

def plan6224 : Plan := .step choices284 bits1581 plan3636

def plan6225 : Plan := .step choices285 bits1586 plan3632

def plan6226 : Plan := .step choices287 bits1589 plan3621

def plan6227 : Plan := .step choices287 bits1583 plan3628

def plan6228 : Plan := .step choices287 bits1584 plan3632

def plan6229 : Plan := .step choices287 bits1583 plan3633

def plan6230 : Plan := .step choices288 bits1585 plan3632

def plan6231 : Plan := .step choices288 bits1584 plan3633

def plan6232 : Plan := .step choices288 bits1583 plan3634

def plan6233 : Plan := .step choices288 bits1582 plan3635

def plan6234 : Plan := .step choices288 bits1581 plan3636

def plan6235 : Plan := .step choices290 bits1647 plan3643

def plan6236 : Plan := .step choices290 bits1648 plan3647

def plan6237 : Plan := .step choices290 bits1647 plan3648

def plan6238 : Plan := .step choices291 bits1645 plan3637

def plan6239 : Plan := .step choices291 bits1646 plan3638

def plan6240 : Plan := .step choices291 bits1645 plan3639

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


