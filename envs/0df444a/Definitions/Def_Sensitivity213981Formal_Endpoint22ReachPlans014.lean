-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans014
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:11.161826+00:00
-- url     : https://prove2.me/theorems/329c7bb9-e868-4f1a-8471-23a008f22ccc
-- title:
--   Endpoint22 Reach Plans014 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans014 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1414`, `ThreeBoundEndpoint22Reachable.plan1415`, `ThreeBoundEndpoint22Reachable.plan1416`, `ThreeBoundEndpoint22Reachable.plan1417`, `ThreeBoundEndpoint22Reachable.plan1418`, `ThreeBoundEndpoint22Reachable.plan1419`, `ThreeBoundEndpoint22Reachable.plan1420`, `ThreeBoundEndpoint22Reachable.plan1350`, `ThreeBoundEndpoint22Reachable.plan1421`, `ThreeBoundEndpoint22Reachable.plan1422`, `ThreeBoundEndpoint22Reachable.plan1423`, `ThreeBoundEndpoint22Reachable.plan1424`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans014.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
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
def plan1345 : Plan := .step choices140 bits406 plan486

def plan1346 : Plan := .step choices140 bits321 plan495

def plan1347 : Plan := .step choices140 bits322 plan497

def plan1348 : Plan := .step choices140 bits321 plan503

def plan1349 : Plan := .step choices141 bits436 plan484

def plan1350 : Plan := .step choices141 bits412 plan485

def plan1351 : Plan := .step choices141 bits413 plan486

def plan1352 : Plan := .step choices141 bits412 plan487

def plan1353 : Plan := .step choices141 bits411 plan488

def plan1354 : Plan := .step choices141 bits323 plan489

def plan1355 : Plan := .step choices141 bits324 plan490

def plan1356 : Plan := .step choices141 bits325 plan491

def plan1357 : Plan := .step choices141 bits323 plan492

def plan1358 : Plan := .step choices141 bits324 plan493

def plan1359 : Plan := .step choices141 bits325 plan494

def plan1360 : Plan := .step choices141 bits326 plan495

def plan1361 : Plan := .step choices141 bits325 plan496

def plan1362 : Plan := .step choices141 bits327 plan497

def plan1363 : Plan := .step choices141 bits411 plan498

def plan1364 : Plan := .step choices141 bits324 plan499

def plan1365 : Plan := .step choices141 bits325 plan500

def plan1366 : Plan := .step choices141 bits323 plan501

def plan1367 : Plan := .step choices141 bits324 plan502

def plan1368 : Plan := .step choices141 bits326 plan503

def plan1369 : Plan := .step choices141 bits325 plan504

def plan1370 : Plan := .step choices142 bits326 plan494

def plan1371 : Plan := .step choices142 bits327 plan495

def plan1372 : Plan := .step choices142 bits326 plan496

def plan1373 : Plan := .step choices142 bits328 plan497

def plan1374 : Plan := .step choices142 bits327 plan503

def plan1375 : Plan := .step choices142 bits326 plan504

def plan1376 : Plan := .step choices143 bits329 plan497

def plan1377 : Plan := .step choices144 bits406 plan486

def plan1378 : Plan := .step choices144 bits321 plan495

def plan1379 : Plan := .step choices144 bits322 plan497

def plan1380 : Plan := .step choices144 bits321 plan503

def plan1381 : Plan := .step choices145 bits436 plan484

def plan1382 : Plan := .step choices145 bits412 plan485

def plan1383 : Plan := .step choices145 bits413 plan486

def plan1384 : Plan := .step choices145 bits412 plan487

def plan1385 : Plan := .step choices145 bits325 plan494

def plan1386 : Plan := .step choices145 bits326 plan495

def plan1387 : Plan := .step choices145 bits325 plan496

def plan1388 : Plan := .step choices145 bits327 plan497

def plan1389 : Plan := .step choices145 bits411 plan498

def plan1390 : Plan := .step choices145 bits324 plan499

def plan1391 : Plan := .step choices145 bits325 plan500

def plan1392 : Plan := .step choices145 bits323 plan501

def plan1393 : Plan := .step choices145 bits324 plan502

def plan1394 : Plan := .step choices145 bits326 plan503

def plan1395 : Plan := .step choices145 bits325 plan504

def plan1396 : Plan := .step choices146 bits328 plan497

def plan1397 : Plan := .step choices146 bits327 plan503

def plan1398 : Plan := .step choices146 bits326 plan504

def plan1399 : Plan := .step choices149 bits549 plan511

def plan1400 : Plan := .step choices149 bits550 plan514

def plan1401 : Plan := .step choices149 bits551 plan515

def plan1402 : Plan := .step choices149 bits550 plan516

def plan1403 : Plan := .step choices149 bits552 plan517

def plan1404 : Plan := .step choices149 bits549 plan520

def plan1405 : Plan := .step choices149 bits551 plan523

def plan1406 : Plan := .step choices149 bits550 plan524

def plan1407 : Plan := .step choices150 bits557 plan514

def plan1408 : Plan := .step choices150 bits558 plan515

def plan1409 : Plan := .step choices150 bits557 plan516

def plan1410 : Plan := .step choices150 bits559 plan517

def plan1411 : Plan := .step choices150 bits558 plan523

def plan1412 : Plan := .step choices150 bits557 plan524

def plan1413 : Plan := .step choices151 bits554 plan506

def plan1414 : Plan := .step choices151 bits453 plan515

def plan1415 : Plan := .step choices151 bits455 plan517

def plan1416 : Plan := .step choices151 bits453 plan523

def plan1417 : Plan := .step choices152 bits555 plan505

def plan1418 : Plan := .step choices152 bits556 plan506

def plan1419 : Plan := .step choices152 bits555 plan507

def plan1420 : Plan := .step choices152 bits553 plan508

def plan1421 : Plan := .step choices152 bits451 plan509

def plan1422 : Plan := .step choices152 bits452 plan510

def plan1423 : Plan := .step choices152 bits453 plan511

def plan1424 : Plan := .step choices152 bits451 plan512

def plan1425 : Plan := .step choices152 bits452 plan513

def plan1426 : Plan := .step choices152 bits454 plan514

def plan1427 : Plan := .step choices152 bits456 plan515

def plan1428 : Plan := .step choices152 bits454 plan516

def plan1429 : Plan := .step choices152 bits458 plan517

def plan1430 : Plan := .step choices152 bits553 plan518

def plan1431 : Plan := .step choices152 bits452 plan519

def plan1432 : Plan := .step choices152 bits453 plan520

def plan1433 : Plan := .step choices152 bits451 plan521

def plan1434 : Plan := .step choices152 bits452 plan522

def plan1435 : Plan := .step choices152 bits456 plan523

def plan1436 : Plan := .step choices152 bits454 plan524

def plan1437 : Plan := .step choices153 bits457 plan514

def plan1438 : Plan := .step choices153 bits459 plan515

def plan1439 : Plan := .step choices153 bits457 plan516

def plan1440 : Plan := .step choices153 bits460 plan517

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


