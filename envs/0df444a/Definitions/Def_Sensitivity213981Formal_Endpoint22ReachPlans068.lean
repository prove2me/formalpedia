-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans068
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:52:05.225186+00:00
-- url     : https://prove2.me/theorems/6260d8b6-e1ac-417d-9218-90e41b0b8ca9
-- title:
--   Endpoint22 Reach Plans068 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans068 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6597`, `ThreeBoundEndpoint22Reachable.plan6598`, `ThreeBoundEndpoint22Reachable.plan6599`, `ThreeBoundEndpoint22Reachable.plan6600`, `ThreeBoundEndpoint22Reachable.plan6601`, `ThreeBoundEndpoint22Reachable.plan6602`, `ThreeBoundEndpoint22Reachable.plan6534`, `ThreeBoundEndpoint22Reachable.plan6603`, `ThreeBoundEndpoint22Reachable.plan6604`, `ThreeBoundEndpoint22Reachable.plan6605`, `ThreeBoundEndpoint22Reachable.plan6606`, `ThreeBoundEndpoint22Reachable.plan6607`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans068.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
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
def plan6529 : Plan := .step choices192 bits1344 plan5526

def plan6530 : Plan := .step choices192 bits1345 plan5527

def plan6531 : Plan := .step choices192 bits1344 plan5528

def plan6532 : Plan := .step choices192 bits1346 plan5529

def plan6533 : Plan := .step choices192 bits1345 plan5530

def plan6534 : Plan := .step choices192 bits1344 plan5531

def plan6535 : Plan := .step choices192 bits1341 plan5534

def plan6536 : Plan := .step choices193 bits1355 plan5431

def plan6537 : Plan := .step choices193 bits1357 plan5432

def plan6538 : Plan := .step choices193 bits1355 plan5433

def plan6539 : Plan := .step choices193 bits1359 plan5434

def plan6540 : Plan := .step choices193 bits1362 plan5435

def plan6541 : Plan := .step choices193 bits1359 plan5436

def plan6542 : Plan := .step choices193 bits1363 plan5437

def plan6543 : Plan := .step choices193 bits1362 plan5438

def plan6544 : Plan := .step choices193 bits1359 plan5439

def plan6545 : Plan := .step choices193 bits1364 plan5440

def plan6546 : Plan := .step choices193 bits1355 plan5441

def plan6547 : Plan := .step choices193 bits1357 plan5442

def plan6548 : Plan := .step choices193 bits1355 plan5443

def plan6549 : Plan := .step choices193 bits1363 plan5444

def plan6550 : Plan := .step choices193 bits1362 plan5445

def plan6551 : Plan := .step choices193 bits1359 plan5446

def plan6552 : Plan := .step choices193 bits1366 plan5453

def plan6553 : Plan := .step choices193 bits1369 plan5454

def plan6554 : Plan := .step choices193 bits1366 plan5455

def plan6555 : Plan := .step choices193 bits1370 plan5456

def plan6556 : Plan := .step choices193 bits1369 plan5457

def plan6557 : Plan := .step choices193 bits1366 plan5458

def plan6558 : Plan := .step choices193 bits1371 plan5459

def plan6559 : Plan := .step choices193 bits1370 plan5460

def plan6560 : Plan := .step choices193 bits1369 plan5461

def plan6561 : Plan := .step choices193 bits1366 plan5462

def plan6562 : Plan := .step choices193 bits1359 plan5464

def plan6563 : Plan := .step choices193 bits1362 plan5465

def plan6564 : Plan := .step choices193 bits1359 plan5466

def plan6565 : Plan := .step choices193 bits1363 plan5467

def plan6566 : Plan := .step choices193 bits1362 plan5468

def plan6567 : Plan := .step choices193 bits1359 plan5469

def plan6568 : Plan := .step choices193 bits1355 plan5470

def plan6569 : Plan := .step choices193 bits1355 plan5471

def plan6570 : Plan := .step choices193 bits1359 plan5473

def plan6571 : Plan := .step choices193 bits1362 plan5474

def plan6572 : Plan := .step choices193 bits1359 plan5475

def plan6573 : Plan := .step choices193 bits1363 plan5476

def plan6574 : Plan := .step choices193 bits1362 plan5477

def plan6575 : Plan := .step choices193 bits1359 plan5478

def plan6576 : Plan := .step choices193 bits1355 plan5479

def plan6577 : Plan := .step choices193 bits1372 plan5486

def plan6578 : Plan := .step choices193 bits1373 plan5487

def plan6579 : Plan := .step choices193 bits1372 plan5488

def plan6580 : Plan := .step choices193 bits1374 plan5489

def plan6581 : Plan := .step choices193 bits1373 plan5490

def plan6582 : Plan := .step choices193 bits1372 plan5491

def plan6583 : Plan := .step choices193 bits1375 plan5492

def plan6584 : Plan := .step choices193 bits1374 plan5493

def plan6585 : Plan := .step choices193 bits1373 plan5494

def plan6586 : Plan := .step choices193 bits1372 plan5495

def plan6587 : Plan := .step choices193 bits1366 plan5504

def plan6588 : Plan := .step choices193 bits1369 plan5505

def plan6589 : Plan := .step choices193 bits1366 plan5506

def plan6590 : Plan := .step choices193 bits1370 plan5507

def plan6591 : Plan := .step choices193 bits1369 plan5508

def plan6592 : Plan := .step choices193 bits1366 plan5509

def plan6593 : Plan := .step choices193 bits1359 plan5511

def plan6594 : Plan := .step choices193 bits1362 plan5512

def plan6595 : Plan := .step choices193 bits1359 plan5513

def plan6596 : Plan := .step choices193 bits1359 plan5515

def plan6597 : Plan := .step choices193 bits1362 plan5516

def plan6598 : Plan := .step choices193 bits1359 plan5517

def plan6599 : Plan := .step choices193 bits1366 plan5526

def plan6600 : Plan := .step choices193 bits1369 plan5527

def plan6601 : Plan := .step choices193 bits1366 plan5528

def plan6602 : Plan := .step choices193 bits1370 plan5529

def plan6603 : Plan := .step choices193 bits1369 plan5530

def plan6604 : Plan := .step choices193 bits1366 plan5531

def plan6605 : Plan := .step choices193 bits1359 plan5533

def plan6606 : Plan := .step choices193 bits1362 plan5534

def plan6607 : Plan := .step choices193 bits1359 plan5535

def plan6608 : Plan := .step choices194 bits1376 plan5486

def plan6609 : Plan := .step choices194 bits1377 plan5487

def plan6610 : Plan := .step choices194 bits1376 plan5488

def plan6611 : Plan := .step choices194 bits1378 plan5489

def plan6612 : Plan := .step choices194 bits1377 plan5490

def plan6613 : Plan := .step choices194 bits1376 plan5491

def plan6614 : Plan := .step choices194 bits1379 plan5492

def plan6615 : Plan := .step choices194 bits1378 plan5493

def plan6616 : Plan := .step choices194 bits1377 plan5494

def plan6617 : Plan := .step choices194 bits1376 plan5495

def plan6618 : Plan := .step choices195 bits1352 plan5427

def plan6619 : Plan := .step choices195 bits1354 plan5428

def plan6620 : Plan := .step choices195 bits1356 plan5429

def plan6621 : Plan := .step choices195 bits1354 plan5430

def plan6622 : Plan := .step choices195 bits1358 plan5447

def plan6623 : Plan := .step choices195 bits1360 plan5448

def plan6624 : Plan := .step choices195 bits1358 plan5449

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


