-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans087
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:05:20.607731+00:00
-- url     : https://prove2.me/theorems/db5d55b3-6372-41e4-9e82-980dfc572532
-- title:
--   Endpoint22 Reach Plans087 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans087 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8420`, `ThreeBoundEndpoint22Reachable.plan8421`, `ThreeBoundEndpoint22Reachable.plan8422`, `ThreeBoundEndpoint22Reachable.plan8423`, `ThreeBoundEndpoint22Reachable.plan8424`, `ThreeBoundEndpoint22Reachable.plan8425`, `ThreeBoundEndpoint22Reachable.plan8357`, `ThreeBoundEndpoint22Reachable.plan8426`, `ThreeBoundEndpoint22Reachable.plan8427`, `ThreeBoundEndpoint22Reachable.plan8428`, `ThreeBoundEndpoint22Reachable.plan8429`, `ThreeBoundEndpoint22Reachable.plan8430`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans087.lean, lines 1–209.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
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
def plan8353 : Plan := .step choices291 bits1753 plan6247

def plan8354 : Plan := .step choices291 bits1757 plan6248

def plan8355 : Plan := .step choices291 bits1756 plan6249

def plan8356 : Plan := .step choices291 bits1755 plan6250

def plan8357 : Plan := .step choices291 bits1754 plan6251

def plan8358 : Plan := .step choices291 bits1753 plan6252

def plan8359 : Plan := .step choices291 bits1758 plan6253

def plan8360 : Plan := .step choices291 bits1757 plan6257

def plan8361 : Plan := .step choices291 bits1756 plan6258

def plan8362 : Plan := .step choices291 bits1755 plan6259

def plan8363 : Plan := .step choices291 bits1754 plan6260

def plan8364 : Plan := .step choices291 bits1753 plan6261

def plan8365 : Plan := .step choices292 bits1759 plan6253

def plan8366 : Plan := .step choices293 bits1755 plan6248

def plan8367 : Plan := .step choices293 bits1756 plan6253

def plan8368 : Plan := .step choices293 bits1755 plan6257

def plan8369 : Plan := .step choices294 bits1754 plan6241

def plan8370 : Plan := .step choices294 bits1755 plan6244

def plan8371 : Plan := .step choices294 bits1754 plan6245

def plan8372 : Plan := .step choices294 bits1756 plan6248

def plan8373 : Plan := .step choices294 bits1755 plan6249

def plan8374 : Plan := .step choices294 bits1754 plan6250

def plan8375 : Plan := .step choices294 bits1757 plan6253

def plan8376 : Plan := .step choices294 bits1754 plan6254

def plan8377 : Plan := .step choices294 bits1755 plan6255

def plan8378 : Plan := .step choices294 bits1754 plan6256

def plan8379 : Plan := .step choices294 bits1756 plan6257

def plan8380 : Plan := .step choices294 bits1755 plan6258

def plan8381 : Plan := .step choices294 bits1754 plan6259

def plan8382 : Plan := .step choices295 bits1758 plan6253

def plan8383 : Plan := .step choices295 bits1757 plan6257

def plan8384 : Plan := .step choices295 bits1756 plan6258

def plan8385 : Plan := .step choices295 bits1755 plan6259

def plan8386 : Plan := .step choices295 bits1754 plan6260

def plan8387 : Plan := .step choices295 bits1753 plan6261

def plan8388 : Plan := .step choices296 bits1555 plan6262

def plan8389 : Plan := .step choices299 bits1636 plan6263

def plan8390 : Plan := .step choices299 bits1637 plan6264

def plan8391 : Plan := .step choices299 bits1636 plan6265

def plan8392 : Plan := .step choices305 bits1715 plan6267

def plan8393 : Plan := .step choices307 bits1704 plan6266

def plan8394 : Plan := .step choices307 bits1705 plan6267

def plan8395 : Plan := .step choices307 bits1704 plan6268

def plan8396 : Plan := .step choices308 bits1706 plan6267

def plan8397 : Plan := .step choices310 bits1705 plan6267

def plan8398 : Plan := .step choices310 bits1704 plan6268

def plan8399 : Plan := .step choices317 bits1760 plan6269

def plan8400 : Plan := .step choices317 bits1761 plan6270

def plan8401 : Plan := .step choices317 bits1760 plan6271

def plan8402 : Plan := .step choices318 bits1762 plan6270

def plan8403 : Plan := .step choices321 bits1761 plan6270

def plan8404 : Plan := .step choices321 bits1760 plan6271

def plan8405 : Plan := .step choices324 bits1794 plan6272

def plan8406 : Plan := .step choices324 bits1795 plan6273

def plan8407 : Plan := .step choices324 bits1794 plan6274

def plan8408 : Plan := .step choices325 bits1796 plan6273

def plan8409 : Plan := .step choices328 bits1795 plan6273

def plan8410 : Plan := .step choices328 bits1794 plan6274

def plan8411 : Plan := .step choices329 bits1811 plan6275

def plan8412 : Plan := .step choices231 bits762 plan8072

def plan8413 : Plan := .step choices232 bits1122 plan8074

def plan8414 : Plan := .step choices233 bits1123 plan8073

def plan8415 : Plan := .step choices233 bits1124 plan8074

def plan8416 : Plan := .step choices233 bits1123 plan8075

def plan8417 : Plan := .step choices237 bits1387 plan8081

def plan8418 : Plan := .step choices238 bits1388 plan8076

def plan8419 : Plan := .step choices238 bits1389 plan8079

def plan8420 : Plan := .step choices238 bits1390 plan8081

def plan8421 : Plan := .step choices238 bits1389 plan8082

def plan8422 : Plan := .step choices239 bits1391 plan8078

def plan8423 : Plan := .step choices239 bits1392 plan8079

def plan8424 : Plan := .step choices239 bits1391 plan8080

def plan8425 : Plan := .step choices239 bits1393 plan8081

def plan8426 : Plan := .step choices239 bits1392 plan8082

def plan8427 : Plan := .step choices239 bits1391 plan8083

def plan8428 : Plan := .step choices240 bits1391 plan8077

def plan8429 : Plan := .step choices243 bits1391 plan8077

def plan8430 : Plan := .step choices245 bits1562 plan8097

def plan8431 : Plan := .step choices246 bits1562 plan8086

def plan8432 : Plan := .step choices246 bits1563 plan8094

def plan8433 : Plan := .step choices246 bits1564 plan8097

def plan8434 : Plan := .step choices246 bits1563 plan8098

def plan8435 : Plan := .step choices247 bits1562 plan8084

def plan8436 : Plan := .step choices247 bits1563 plan8085

def plan8437 : Plan := .step choices247 bits1564 plan8086

def plan8438 : Plan := .step choices247 bits1563 plan8087

def plan8439 : Plan := .step choices247 bits1565 plan8092

def plan8440 : Plan := .step choices247 bits1566 plan8094

def plan8441 : Plan := .step choices247 bits1565 plan8095

def plan8442 : Plan := .step choices247 bits1567 plan8097

def plan8443 : Plan := .step choices247 bits1566 plan8098

def plan8444 : Plan := .step choices247 bits1565 plan8099

def plan8445 : Plan := .step choices247 bits1565 plan8101

def plan8446 : Plan := .step choices247 bits1565 plan8102

def plan8447 : Plan := .step choices248 bits1569 plan8091

def plan8448 : Plan := .step choices248 bits1570 plan8092

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


