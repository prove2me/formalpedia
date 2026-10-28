-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans069
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:52:49.579224+00:00
-- url     : https://prove2.me/theorems/761e2d85-d248-48bd-9d85-c4eacee59300
-- title:
--   Endpoint22 Reach Plans069 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans069 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6692`, `ThreeBoundEndpoint22Reachable.plan6693`, `ThreeBoundEndpoint22Reachable.plan6694`, `ThreeBoundEndpoint22Reachable.plan6695`, `ThreeBoundEndpoint22Reachable.plan6696`, `ThreeBoundEndpoint22Reachable.plan6697`, `ThreeBoundEndpoint22Reachable.plan6698`, `ThreeBoundEndpoint22Reachable.plan6699`, `ThreeBoundEndpoint22Reachable.plan6700`, `ThreeBoundEndpoint22Reachable.plan6701`, `ThreeBoundEndpoint22Reachable.plan6630`, `ThreeBoundEndpoint22Reachable.plan6702`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans069.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
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
def plan6625 : Plan := .step choices195 bits1361 plan5450

def plan6626 : Plan := .step choices195 bits1360 plan5451

def plan6627 : Plan := .step choices195 bits1358 plan5452

def plan6628 : Plan := .step choices195 bits1354 plan5463

def plan6629 : Plan := .step choices195 bits1354 plan5472

def plan6630 : Plan := .step choices195 bits1365 plan5480

def plan6631 : Plan := .step choices195 bits1367 plan5481

def plan6632 : Plan := .step choices195 bits1365 plan5482

def plan6633 : Plan := .step choices195 bits1368 plan5483

def plan6634 : Plan := .step choices195 bits1367 plan5484

def plan6635 : Plan := .step choices195 bits1365 plan5485

def plan6636 : Plan := .step choices195 bits1353 plan5497

def plan6637 : Plan := .step choices195 bits1358 plan5501

def plan6638 : Plan := .step choices195 bits1360 plan5502

def plan6639 : Plan := .step choices195 bits1358 plan5503

def plan6640 : Plan := .step choices195 bits1353 plan5519

def plan6641 : Plan := .step choices195 bits1358 plan5523

def plan6642 : Plan := .step choices195 bits1360 plan5524

def plan6643 : Plan := .step choices195 bits1358 plan5525

def plan6644 : Plan := .step choices196 bits1372 plan5480

def plan6645 : Plan := .step choices196 bits1373 plan5481

def plan6646 : Plan := .step choices196 bits1372 plan5482

def plan6647 : Plan := .step choices196 bits1374 plan5483

def plan6648 : Plan := .step choices196 bits1373 plan5484

def plan6649 : Plan := .step choices196 bits1372 plan5485

def plan6650 : Plan := .step choices196 bits1366 plan5501

def plan6651 : Plan := .step choices196 bits1369 plan5502

def plan6652 : Plan := .step choices196 bits1366 plan5503

def plan6653 : Plan := .step choices196 bits1359 plan5510

def plan6654 : Plan := .step choices196 bits1359 plan5514

def plan6655 : Plan := .step choices196 bits1366 plan5523

def plan6656 : Plan := .step choices196 bits1369 plan5524

def plan6657 : Plan := .step choices196 bits1366 plan5525

def plan6658 : Plan := .step choices196 bits1359 plan5532

def plan6659 : Plan := .step choices199 bits1352 plan5427

def plan6660 : Plan := .step choices199 bits1354 plan5428

def plan6661 : Plan := .step choices199 bits1356 plan5429

def plan6662 : Plan := .step choices199 bits1354 plan5430

def plan6663 : Plan := .step choices199 bits1358 plan5447

def plan6664 : Plan := .step choices199 bits1360 plan5448

def plan6665 : Plan := .step choices199 bits1358 plan5449

def plan6666 : Plan := .step choices199 bits1361 plan5450

def plan6667 : Plan := .step choices199 bits1360 plan5451

def plan6668 : Plan := .step choices199 bits1358 plan5452

def plan6669 : Plan := .step choices199 bits1354 plan5463

def plan6670 : Plan := .step choices199 bits1354 plan5472

def plan6671 : Plan := .step choices199 bits1365 plan5480

def plan6672 : Plan := .step choices199 bits1367 plan5481

def plan6673 : Plan := .step choices199 bits1365 plan5482

def plan6674 : Plan := .step choices199 bits1368 plan5483

def plan6675 : Plan := .step choices199 bits1367 plan5484

def plan6676 : Plan := .step choices199 bits1365 plan5485

def plan6677 : Plan := .step choices199 bits1358 plan5501

def plan6678 : Plan := .step choices199 bits1360 plan5502

def plan6679 : Plan := .step choices199 bits1358 plan5503

def plan6680 : Plan := .step choices199 bits1353 plan5519

def plan6681 : Plan := .step choices199 bits1358 plan5523

def plan6682 : Plan := .step choices199 bits1360 plan5524

def plan6683 : Plan := .step choices199 bits1358 plan5525

def plan6684 : Plan := .step choices200 bits1372 plan5480

def plan6685 : Plan := .step choices200 bits1373 plan5481

def plan6686 : Plan := .step choices200 bits1372 plan5482

def plan6687 : Plan := .step choices200 bits1374 plan5483

def plan6688 : Plan := .step choices200 bits1373 plan5484

def plan6689 : Plan := .step choices200 bits1372 plan5485

def plan6690 : Plan := .step choices200 bits1366 plan5523

def plan6691 : Plan := .step choices200 bits1369 plan5524

def plan6692 : Plan := .step choices200 bits1366 plan5525

def plan6693 : Plan := .step choices200 bits1359 plan5532

def plan6694 : Plan := .step choices202 bits1449 plan5538

def plan6695 : Plan := .step choices202 bits1450 plan5541

def plan6696 : Plan := .step choices202 bits1451 plan5543

def plan6697 : Plan := .step choices202 bits1450 plan5544

def plan6698 : Plan := .step choices202 bits1452 plan5546

def plan6699 : Plan := .step choices202 bits1449 plan5549

def plan6700 : Plan := .step choices202 bits1451 plan5551

def plan6701 : Plan := .step choices202 bits1450 plan5552

def plan6702 : Plan := .step choices202 bits1454 plan5581

def plan6703 : Plan := .step choices202 bits1457 plan5584

def plan6704 : Plan := .step choices202 bits1454 plan5588

def plan6705 : Plan := .step choices202 bits1455 plan5592

def plan6706 : Plan := .step choices202 bits1458 plan5594

def plan6707 : Plan := .step choices202 bits1455 plan5595

def plan6708 : Plan := .step choices202 bits1459 plan5597

def plan6709 : Plan := .step choices202 bits1458 plan5598

def plan6710 : Plan := .step choices202 bits1455 plan5599

def plan6711 : Plan := .step choices202 bits1460 plan5601

def plan6712 : Plan := .step choices202 bits1454 plan5608

def plan6713 : Plan := .step choices202 bits1457 plan5611

def plan6714 : Plan := .step choices202 bits1454 plan5615

def plan6715 : Plan := .step choices202 bits1459 plan5618

def plan6716 : Plan := .step choices202 bits1458 plan5619

def plan6717 : Plan := .step choices202 bits1455 plan5620

def plan6718 : Plan := .step choices202 bits1463 plan5632

def plan6719 : Plan := .step choices202 bits1465 plan5633

def plan6720 : Plan := .step choices202 bits1463 plan5634

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


