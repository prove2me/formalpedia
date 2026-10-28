-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans067
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:52:37.102435+00:00
-- url     : https://prove2.me/theorems/8c388f95-f5f0-4fb4-a976-c409716ca2c3
-- title:
--   Endpoint22 Reach Plans067 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans067 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6501`, `ThreeBoundEndpoint22Reachable.plan6502`, `ThreeBoundEndpoint22Reachable.plan6503`, `ThreeBoundEndpoint22Reachable.plan6504`, `ThreeBoundEndpoint22Reachable.plan6505`, `ThreeBoundEndpoint22Reachable.plan6506`, `ThreeBoundEndpoint22Reachable.plan6507`, `ThreeBoundEndpoint22Reachable.plan6438`, `ThreeBoundEndpoint22Reachable.plan6508`, `ThreeBoundEndpoint22Reachable.plan6509`, `ThreeBoundEndpoint22Reachable.plan6510`, `ThreeBoundEndpoint22Reachable.plan6511`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans067.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
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
def plan6433 : Plan := .step choices189 bits1157 plan5410

def plan6434 : Plan := .step choices191 bits1324 plan5417

def plan6435 : Plan := .step choices191 bits1325 plan5420

def plan6436 : Plan := .step choices191 bits1326 plan5422

def plan6437 : Plan := .step choices191 bits1325 plan5423

def plan6438 : Plan := .step choices191 bits1328 plan5437

def plan6439 : Plan := .step choices191 bits1329 plan5440

def plan6440 : Plan := .step choices191 bits1328 plan5444

def plan6441 : Plan := .step choices191 bits1330 plan5454

def plan6442 : Plan := .step choices191 bits1331 plan5456

def plan6443 : Plan := .step choices191 bits1330 plan5457

def plan6444 : Plan := .step choices191 bits1332 plan5459

def plan6445 : Plan := .step choices191 bits1331 plan5460

def plan6446 : Plan := .step choices191 bits1330 plan5461

def plan6447 : Plan := .step choices191 bits1328 plan5467

def plan6448 : Plan := .step choices191 bits1328 plan5476

def plan6449 : Plan := .step choices191 bits1333 plan5486

def plan6450 : Plan := .step choices191 bits1334 plan5487

def plan6451 : Plan := .step choices191 bits1333 plan5488

def plan6452 : Plan := .step choices191 bits1335 plan5489

def plan6453 : Plan := .step choices191 bits1334 plan5490

def plan6454 : Plan := .step choices191 bits1333 plan5491

def plan6455 : Plan := .step choices191 bits1336 plan5492

def plan6456 : Plan := .step choices191 bits1335 plan5493

def plan6457 : Plan := .step choices191 bits1334 plan5494

def plan6458 : Plan := .step choices191 bits1333 plan5495

def plan6459 : Plan := .step choices191 bits1327 plan5499

def plan6460 : Plan := .step choices191 bits1330 plan5505

def plan6461 : Plan := .step choices191 bits1331 plan5507

def plan6462 : Plan := .step choices191 bits1330 plan5508

def plan6463 : Plan := .step choices191 bits1327 plan5521

def plan6464 : Plan := .step choices191 bits1330 plan5527

def plan6465 : Plan := .step choices191 bits1331 plan5529

def plan6466 : Plan := .step choices191 bits1330 plan5530

def plan6467 : Plan := .step choices192 bits1324 plan5415

def plan6468 : Plan := .step choices192 bits1328 plan5416

def plan6469 : Plan := .step choices192 bits1329 plan5417

def plan6470 : Plan := .step choices192 bits1328 plan5418

def plan6471 : Plan := .step choices192 bits1330 plan5419

def plan6472 : Plan := .step choices192 bits1331 plan5420

def plan6473 : Plan := .step choices192 bits1330 plan5421

def plan6474 : Plan := .step choices192 bits1332 plan5422

def plan6475 : Plan := .step choices192 bits1331 plan5423

def plan6476 : Plan := .step choices192 bits1330 plan5424

def plan6477 : Plan := .step choices192 bits1328 plan5425

def plan6478 : Plan := .step choices192 bits1328 plan5426

def plan6479 : Plan := .step choices192 bits1338 plan5432

def plan6480 : Plan := .step choices192 bits1341 plan5435

def plan6481 : Plan := .step choices192 bits1342 plan5437

def plan6482 : Plan := .step choices192 bits1341 plan5438

def plan6483 : Plan := .step choices192 bits1343 plan5440

def plan6484 : Plan := .step choices192 bits1338 plan5442

def plan6485 : Plan := .step choices192 bits1342 plan5444

def plan6486 : Plan := .step choices192 bits1341 plan5445

def plan6487 : Plan := .step choices192 bits1344 plan5453

def plan6488 : Plan := .step choices192 bits1345 plan5454

def plan6489 : Plan := .step choices192 bits1344 plan5455

def plan6490 : Plan := .step choices192 bits1346 plan5456

def plan6491 : Plan := .step choices192 bits1345 plan5457

def plan6492 : Plan := .step choices192 bits1344 plan5458

def plan6493 : Plan := .step choices192 bits1347 plan5459

def plan6494 : Plan := .step choices192 bits1346 plan5460

def plan6495 : Plan := .step choices192 bits1345 plan5461

def plan6496 : Plan := .step choices192 bits1344 plan5462

def plan6497 : Plan := .step choices192 bits1341 plan5465

def plan6498 : Plan := .step choices192 bits1342 plan5467

def plan6499 : Plan := .step choices192 bits1341 plan5468

def plan6500 : Plan := .step choices192 bits1341 plan5474

def plan6501 : Plan := .step choices192 bits1342 plan5476

def plan6502 : Plan := .step choices192 bits1341 plan5477

def plan6503 : Plan := .step choices192 bits1348 plan5486

def plan6504 : Plan := .step choices192 bits1349 plan5487

def plan6505 : Plan := .step choices192 bits1348 plan5488

def plan6506 : Plan := .step choices192 bits1350 plan5489

def plan6507 : Plan := .step choices192 bits1349 plan5490

def plan6508 : Plan := .step choices192 bits1348 plan5491

def plan6509 : Plan := .step choices192 bits1351 plan5492

def plan6510 : Plan := .step choices192 bits1350 plan5493

def plan6511 : Plan := .step choices192 bits1349 plan5494

def plan6512 : Plan := .step choices192 bits1348 plan5495

def plan6513 : Plan := .step choices192 bits1337 plan5496

def plan6514 : Plan := .step choices192 bits1339 plan5498

def plan6515 : Plan := .step choices192 bits1340 plan5499

def plan6516 : Plan := .step choices192 bits1339 plan5500

def plan6517 : Plan := .step choices192 bits1344 plan5504

def plan6518 : Plan := .step choices192 bits1345 plan5505

def plan6519 : Plan := .step choices192 bits1344 plan5506

def plan6520 : Plan := .step choices192 bits1346 plan5507

def plan6521 : Plan := .step choices192 bits1345 plan5508

def plan6522 : Plan := .step choices192 bits1344 plan5509

def plan6523 : Plan := .step choices192 bits1341 plan5512

def plan6524 : Plan := .step choices192 bits1341 plan5516

def plan6525 : Plan := .step choices192 bits1337 plan5518

def plan6526 : Plan := .step choices192 bits1339 plan5520

def plan6527 : Plan := .step choices192 bits1340 plan5521

def plan6528 : Plan := .step choices192 bits1339 plan5522

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


