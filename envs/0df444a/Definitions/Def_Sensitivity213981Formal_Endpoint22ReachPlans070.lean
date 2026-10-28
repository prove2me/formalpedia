-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans070
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:00:52.603332+00:00
-- url     : https://prove2.me/theorems/dc1c3f41-f87c-48c9-8b65-6cf482781b82
-- title:
--   Endpoint22 Reach Plans070 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans070 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6789`, `ThreeBoundEndpoint22Reachable.plan6790`, `ThreeBoundEndpoint22Reachable.plan6791`, `ThreeBoundEndpoint22Reachable.plan6792`, `ThreeBoundEndpoint22Reachable.plan6793`, `ThreeBoundEndpoint22Reachable.plan6794`, `ThreeBoundEndpoint22Reachable.plan6795`, `ThreeBoundEndpoint22Reachable.plan6726`, `ThreeBoundEndpoint22Reachable.plan6796`, `ThreeBoundEndpoint22Reachable.plan6797`, `ThreeBoundEndpoint22Reachable.plan6798`, `ThreeBoundEndpoint22Reachable.plan6799`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans070.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
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
def plan6721 : Plan := .step choices202 bits1467 plan5635

def plan6722 : Plan := .step choices202 bits1465 plan5636

def plan6723 : Plan := .step choices202 bits1463 plan5637

def plan6724 : Plan := .step choices202 bits1468 plan5638

def plan6725 : Plan := .step choices202 bits1467 plan5639

def plan6726 : Plan := .step choices202 bits1465 plan5640

def plan6727 : Plan := .step choices202 bits1463 plan5641

def plan6728 : Plan := .step choices202 bits1469 plan5642

def plan6729 : Plan := .step choices202 bits1468 plan5643

def plan6730 : Plan := .step choices202 bits1467 plan5644

def plan6731 : Plan := .step choices202 bits1465 plan5645

def plan6732 : Plan := .step choices202 bits1463 plan5646

def plan6733 : Plan := .step choices202 bits1448 plan5649

def plan6734 : Plan := .step choices202 bits1453 plan5655

def plan6735 : Plan := .step choices202 bits1456 plan5657

def plan6736 : Plan := .step choices202 bits1453 plan5658

def plan6737 : Plan := .step choices202 bits1462 plan5669

def plan6738 : Plan := .step choices202 bits1464 plan5671

def plan6739 : Plan := .step choices202 bits1462 plan5672

def plan6740 : Plan := .step choices202 bits1466 plan5674

def plan6741 : Plan := .step choices202 bits1464 plan5675

def plan6742 : Plan := .step choices202 bits1462 plan5676

def plan6743 : Plan := .step choices202 bits1461 plan5684

def plan6744 : Plan := .step choices202 bits1461 plan5695

def plan6745 : Plan := .step choices202 bits1448 plan5701

def plan6746 : Plan := .step choices202 bits1453 plan5707

def plan6747 : Plan := .step choices202 bits1456 plan5709

def plan6748 : Plan := .step choices202 bits1453 plan5710

def plan6749 : Plan := .step choices202 bits1462 plan5721

def plan6750 : Plan := .step choices202 bits1464 plan5723

def plan6751 : Plan := .step choices202 bits1462 plan5724

def plan6752 : Plan := .step choices202 bits1466 plan5726

def plan6753 : Plan := .step choices202 bits1464 plan5727

def plan6754 : Plan := .step choices202 bits1462 plan5728

def plan6755 : Plan := .step choices202 bits1461 plan5736

def plan6756 : Plan := .step choices203 bits1470 plan5536

def plan6757 : Plan := .step choices203 bits1472 plan5537

def plan6758 : Plan := .step choices203 bits1475 plan5538

def plan6759 : Plan := .step choices203 bits1472 plan5539

def plan6760 : Plan := .step choices203 bits1473 plan5540

def plan6761 : Plan := .step choices203 bits1476 plan5541

def plan6762 : Plan := .step choices203 bits1473 plan5542

def plan6763 : Plan := .step choices203 bits1477 plan5543

def plan6764 : Plan := .step choices203 bits1476 plan5544

def plan6765 : Plan := .step choices203 bits1473 plan5545

def plan6766 : Plan := .step choices203 bits1478 plan5546

def plan6767 : Plan := .step choices203 bits1470 plan5547

def plan6768 : Plan := .step choices203 bits1472 plan5548

def plan6769 : Plan := .step choices203 bits1475 plan5549

def plan6770 : Plan := .step choices203 bits1472 plan5550

def plan6771 : Plan := .step choices203 bits1477 plan5551

def plan6772 : Plan := .step choices203 bits1476 plan5552

def plan6773 : Plan := .step choices203 bits1473 plan5553

def plan6774 : Plan := .step choices203 bits1481 plan5576

def plan6775 : Plan := .step choices203 bits1482 plan5579

def plan6776 : Plan := .step choices203 bits1485 plan5581

def plan6777 : Plan := .step choices203 bits1482 plan5582

def plan6778 : Plan := .step choices203 bits1488 plan5584

def plan6779 : Plan := .step choices203 bits1481 plan5586

def plan6780 : Plan := .step choices203 bits1485 plan5588

def plan6781 : Plan := .step choices203 bits1482 plan5589

def plan6782 : Plan := .step choices203 bits1483 plan5591

def plan6783 : Plan := .step choices203 bits1486 plan5592

def plan6784 : Plan := .step choices203 bits1483 plan5593

def plan6785 : Plan := .step choices203 bits1489 plan5594

def plan6786 : Plan := .step choices203 bits1486 plan5595

def plan6787 : Plan := .step choices203 bits1483 plan5596

def plan6788 : Plan := .step choices203 bits1490 plan5597

def plan6789 : Plan := .step choices203 bits1489 plan5598

def plan6790 : Plan := .step choices203 bits1486 plan5599

def plan6791 : Plan := .step choices203 bits1483 plan5600

def plan6792 : Plan := .step choices203 bits1491 plan5601

def plan6793 : Plan := .step choices203 bits1482 plan5606

def plan6794 : Plan := .step choices203 bits1485 plan5608

def plan6795 : Plan := .step choices203 bits1482 plan5609

def plan6796 : Plan := .step choices203 bits1488 plan5611

def plan6797 : Plan := .step choices203 bits1481 plan5613

def plan6798 : Plan := .step choices203 bits1485 plan5615

def plan6799 : Plan := .step choices203 bits1482 plan5616

def plan6800 : Plan := .step choices203 bits1490 plan5618

def plan6801 : Plan := .step choices203 bits1489 plan5619

def plan6802 : Plan := .step choices203 bits1486 plan5620

def plan6803 : Plan := .step choices203 bits1483 plan5621

def plan6804 : Plan := .step choices203 bits1500 plan5632

def plan6805 : Plan := .step choices203 bits1503 plan5633

def plan6806 : Plan := .step choices203 bits1500 plan5634

def plan6807 : Plan := .step choices203 bits1506 plan5635

def plan6808 : Plan := .step choices203 bits1503 plan5636

def plan6809 : Plan := .step choices203 bits1500 plan5637

def plan6810 : Plan := .step choices203 bits1507 plan5638

def plan6811 : Plan := .step choices203 bits1506 plan5639

def plan6812 : Plan := .step choices203 bits1503 plan5640

def plan6813 : Plan := .step choices203 bits1500 plan5641

def plan6814 : Plan := .step choices203 bits1508 plan5642

def plan6815 : Plan := .step choices203 bits1507 plan5643

def plan6816 : Plan := .step choices203 bits1506 plan5644

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


