-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans015
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:16.717751+00:00
-- url     : https://prove2.me/theorems/be404258-4fde-4ba1-836f-c4adc523a925
-- title:
--   Endpoint22 Reach Plans015 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans015 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1510`, `ThreeBoundEndpoint22Reachable.plan1511`, `ThreeBoundEndpoint22Reachable.plan1512`, `ThreeBoundEndpoint22Reachable.plan1513`, `ThreeBoundEndpoint22Reachable.plan1514`, `ThreeBoundEndpoint22Reachable.plan1515`, `ThreeBoundEndpoint22Reachable.plan1516`, `ThreeBoundEndpoint22Reachable.plan1517`, `ThreeBoundEndpoint22Reachable.plan1518`, `ThreeBoundEndpoint22Reachable.plan1446`, `ThreeBoundEndpoint22Reachable.plan1519`, `ThreeBoundEndpoint22Reachable.plan1520`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans015.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
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
def plan1441 : Plan := .step choices153 bits459 plan523

def plan1442 : Plan := .step choices153 bits457 plan524

def plan1443 : Plan := .step choices154 bits461 plan517

def plan1444 : Plan := .step choices155 bits554 plan506

def plan1445 : Plan := .step choices155 bits453 plan515

def plan1446 : Plan := .step choices155 bits455 plan517

def plan1447 : Plan := .step choices155 bits453 plan523

def plan1448 : Plan := .step choices156 bits555 plan505

def plan1449 : Plan := .step choices156 bits556 plan506

def plan1450 : Plan := .step choices156 bits555 plan507

def plan1451 : Plan := .step choices156 bits454 plan514

def plan1452 : Plan := .step choices156 bits456 plan515

def plan1453 : Plan := .step choices156 bits454 plan516

def plan1454 : Plan := .step choices156 bits458 plan517

def plan1455 : Plan := .step choices156 bits553 plan518

def plan1456 : Plan := .step choices156 bits452 plan519

def plan1457 : Plan := .step choices156 bits453 plan520

def plan1458 : Plan := .step choices156 bits451 plan521

def plan1459 : Plan := .step choices156 bits452 plan522

def plan1460 : Plan := .step choices156 bits456 plan523

def plan1461 : Plan := .step choices156 bits454 plan524

def plan1462 : Plan := .step choices157 bits460 plan517

def plan1463 : Plan := .step choices157 bits459 plan523

def plan1464 : Plan := .step choices157 bits457 plan524

def plan1465 : Plan := .step choices158 bits624 plan531

def plan1466 : Plan := .step choices158 bits625 plan533

def plan1467 : Plan := .step choices158 bits624 plan538

def plan1468 : Plan := .step choices159 bits622 plan525

def plan1469 : Plan := .step choices159 bits623 plan526

def plan1470 : Plan := .step choices159 bits624 plan527

def plan1471 : Plan := .step choices159 bits622 plan528

def plan1472 : Plan := .step choices159 bits623 plan529

def plan1473 : Plan := .step choices159 bits624 plan530

def plan1474 : Plan := .step choices159 bits625 plan531

def plan1475 : Plan := .step choices159 bits624 plan532

def plan1476 : Plan := .step choices159 bits626 plan533

def plan1477 : Plan := .step choices159 bits623 plan534

def plan1478 : Plan := .step choices159 bits624 plan535

def plan1479 : Plan := .step choices159 bits622 plan536

def plan1480 : Plan := .step choices159 bits623 plan537

def plan1481 : Plan := .step choices159 bits625 plan538

def plan1482 : Plan := .step choices159 bits624 plan539

def plan1483 : Plan := .step choices160 bits625 plan530

def plan1484 : Plan := .step choices160 bits626 plan531

def plan1485 : Plan := .step choices160 bits625 plan532

def plan1486 : Plan := .step choices160 bits627 plan533

def plan1487 : Plan := .step choices160 bits626 plan538

def plan1488 : Plan := .step choices160 bits625 plan539

def plan1489 : Plan := .step choices161 bits628 plan533

def plan1490 : Plan := .step choices162 bits624 plan531

def plan1491 : Plan := .step choices162 bits625 plan533

def plan1492 : Plan := .step choices162 bits624 plan538

def plan1493 : Plan := .step choices163 bits624 plan530

def plan1494 : Plan := .step choices163 bits625 plan531

def plan1495 : Plan := .step choices163 bits624 plan532

def plan1496 : Plan := .step choices163 bits626 plan533

def plan1497 : Plan := .step choices163 bits623 plan534

def plan1498 : Plan := .step choices163 bits624 plan535

def plan1499 : Plan := .step choices163 bits622 plan536

def plan1500 : Plan := .step choices163 bits623 plan537

def plan1501 : Plan := .step choices163 bits625 plan538

def plan1502 : Plan := .step choices163 bits624 plan539

def plan1503 : Plan := .step choices164 bits627 plan533

def plan1504 : Plan := .step choices164 bits626 plan538

def plan1505 : Plan := .step choices164 bits625 plan539

def plan1506 : Plan := .step choices168 bits135 plan540

def plan1507 : Plan := .step choices171 bits194 plan543

def plan1508 : Plan := .step choices172 bits220 plan541

def plan1509 : Plan := .step choices172 bits196 plan542

def plan1510 : Plan := .step choices172 bits197 plan543

def plan1511 : Plan := .step choices172 bits196 plan544

def plan1512 : Plan := .step choices182 bits269 plan550

def plan1513 : Plan := .step choices182 bits270 plan552

def plan1514 : Plan := .step choices182 bits269 plan553

def plan1515 : Plan := .step choices183 bits308 plan545

def plan1516 : Plan := .step choices183 bits303 plan546

def plan1517 : Plan := .step choices183 bits304 plan547

def plan1518 : Plan := .step choices183 bits303 plan548

def plan1519 : Plan := .step choices183 bits271 plan549

def plan1520 : Plan := .step choices183 bits272 plan550

def plan1521 : Plan := .step choices183 bits271 plan551

def plan1522 : Plan := .step choices183 bits273 plan552

def plan1523 : Plan := .step choices183 bits272 plan553

def plan1524 : Plan := .step choices183 bits271 plan554

def plan1525 : Plan := .step choices185 bits271 plan547

def plan1526 : Plan := .step choices189 bits271 plan547

def plan1527 : Plan := .step choices193 bits417 plan562

def plan1528 : Plan := .step choices194 bits445 plan555

def plan1529 : Plan := .step choices194 bits439 plan556

def plan1530 : Plan := .step choices194 bits440 plan557

def plan1531 : Plan := .step choices194 bits439 plan558

def plan1532 : Plan := .step choices194 bits418 plan559

def plan1533 : Plan := .step choices194 bits419 plan560

def plan1534 : Plan := .step choices194 bits418 plan561

def plan1535 : Plan := .step choices194 bits420 plan562

def plan1536 : Plan := .step choices194 bits419 plan563

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


