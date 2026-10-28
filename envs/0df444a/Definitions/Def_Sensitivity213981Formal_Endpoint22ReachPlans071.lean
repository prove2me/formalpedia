-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans071
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:00:26.405106+00:00
-- url     : https://prove2.me/theorems/e5e78ad5-94b8-466a-8e2b-17e1ec2f78d6
-- title:
--   Endpoint22 Reach Plans071 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans071 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6885`, `ThreeBoundEndpoint22Reachable.plan6886`, `ThreeBoundEndpoint22Reachable.plan6887`, `ThreeBoundEndpoint22Reachable.plan6888`, `ThreeBoundEndpoint22Reachable.plan6889`, `ThreeBoundEndpoint22Reachable.plan6890`, `ThreeBoundEndpoint22Reachable.plan6822`, `ThreeBoundEndpoint22Reachable.plan6891`, `ThreeBoundEndpoint22Reachable.plan6892`, `ThreeBoundEndpoint22Reachable.plan6893`, `ThreeBoundEndpoint22Reachable.plan6894`, `ThreeBoundEndpoint22Reachable.plan6895`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans071.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan6817 : Plan := .step choices203 bits1503 plan5645

def plan6818 : Plan := .step choices203 bits1500 plan5646

def plan6819 : Plan := .step choices203 bits1471 plan5648

def plan6820 : Plan := .step choices203 bits1474 plan5649

def plan6821 : Plan := .step choices203 bits1471 plan5650

def plan6822 : Plan := .step choices203 bits1481 plan5654

def plan6823 : Plan := .step choices203 bits1484 plan5655

def plan6824 : Plan := .step choices203 bits1481 plan5656

def plan6825 : Plan := .step choices203 bits1487 plan5657

def plan6826 : Plan := .step choices203 bits1484 plan5658

def plan6827 : Plan := .step choices203 bits1481 plan5659

def plan6828 : Plan := .step choices203 bits1480 plan5660

def plan6829 : Plan := .step choices203 bits1480 plan5661

def plan6830 : Plan := .step choices203 bits1495 plan5668

def plan6831 : Plan := .step choices203 bits1499 plan5669

def plan6832 : Plan := .step choices203 bits1495 plan5670

def plan6833 : Plan := .step choices203 bits1502 plan5671

def plan6834 : Plan := .step choices203 bits1499 plan5672

def plan6835 : Plan := .step choices203 bits1495 plan5673

def plan6836 : Plan := .step choices203 bits1505 plan5674

def plan6837 : Plan := .step choices203 bits1502 plan5675

def plan6838 : Plan := .step choices203 bits1499 plan5676

def plan6839 : Plan := .step choices203 bits1495 plan5677

def plan6840 : Plan := .step choices203 bits1494 plan5682

def plan6841 : Plan := .step choices203 bits1498 plan5684

def plan6842 : Plan := .step choices203 bits1494 plan5685

def plan6843 : Plan := .step choices203 bits1494 plan5693

def plan6844 : Plan := .step choices203 bits1498 plan5695

def plan6845 : Plan := .step choices203 bits1494 plan5696

def plan6846 : Plan := .step choices203 bits1471 plan5700

def plan6847 : Plan := .step choices203 bits1474 plan5701

def plan6848 : Plan := .step choices203 bits1471 plan5702

def plan6849 : Plan := .step choices203 bits1481 plan5706

def plan6850 : Plan := .step choices203 bits1484 plan5707

def plan6851 : Plan := .step choices203 bits1481 plan5708

def plan6852 : Plan := .step choices203 bits1487 plan5709

def plan6853 : Plan := .step choices203 bits1484 plan5710

def plan6854 : Plan := .step choices203 bits1481 plan5711

def plan6855 : Plan := .step choices203 bits1480 plan5712

def plan6856 : Plan := .step choices203 bits1480 plan5713

def plan6857 : Plan := .step choices203 bits1495 plan5720

def plan6858 : Plan := .step choices203 bits1499 plan5721

def plan6859 : Plan := .step choices203 bits1495 plan5722

def plan6860 : Plan := .step choices203 bits1502 plan5723

def plan6861 : Plan := .step choices203 bits1499 plan5724

def plan6862 : Plan := .step choices203 bits1495 plan5725

def plan6863 : Plan := .step choices203 bits1505 plan5726

def plan6864 : Plan := .step choices203 bits1502 plan5727

def plan6865 : Plan := .step choices203 bits1499 plan5728

def plan6866 : Plan := .step choices203 bits1495 plan5729

def plan6867 : Plan := .step choices203 bits1494 plan5734

def plan6868 : Plan := .step choices203 bits1498 plan5736

def plan6869 : Plan := .step choices203 bits1494 plan5737

def plan6870 : Plan := .step choices204 bits1494 plan5575

def plan6871 : Plan := .step choices204 bits1498 plan5576

def plan6872 : Plan := .step choices204 bits1494 plan5577

def plan6873 : Plan := .step choices204 bits1495 plan5578

def plan6874 : Plan := .step choices204 bits1499 plan5579

def plan6875 : Plan := .step choices204 bits1495 plan5580

def plan6876 : Plan := .step choices204 bits1502 plan5581

def plan6877 : Plan := .step choices204 bits1499 plan5582

def plan6878 : Plan := .step choices204 bits1495 plan5583

def plan6879 : Plan := .step choices204 bits1505 plan5584

def plan6880 : Plan := .step choices204 bits1494 plan5585

def plan6881 : Plan := .step choices204 bits1498 plan5586

def plan6882 : Plan := .step choices204 bits1494 plan5587

def plan6883 : Plan := .step choices204 bits1502 plan5588

def plan6884 : Plan := .step choices204 bits1499 plan5589

def plan6885 : Plan := .step choices204 bits1495 plan5590

def plan6886 : Plan := .step choices204 bits1500 plan5591

def plan6887 : Plan := .step choices204 bits1503 plan5592

def plan6888 : Plan := .step choices204 bits1500 plan5593

def plan6889 : Plan := .step choices204 bits1506 plan5594

def plan6890 : Plan := .step choices204 bits1503 plan5595

def plan6891 : Plan := .step choices204 bits1500 plan5596

def plan6892 : Plan := .step choices204 bits1507 plan5597

def plan6893 : Plan := .step choices204 bits1506 plan5598

def plan6894 : Plan := .step choices204 bits1503 plan5599

def plan6895 : Plan := .step choices204 bits1500 plan5600

def plan6896 : Plan := .step choices204 bits1508 plan5601

def plan6897 : Plan := .step choices204 bits1495 plan5605

def plan6898 : Plan := .step choices204 bits1499 plan5606

def plan6899 : Plan := .step choices204 bits1495 plan5607

def plan6900 : Plan := .step choices204 bits1502 plan5608

def plan6901 : Plan := .step choices204 bits1499 plan5609

def plan6902 : Plan := .step choices204 bits1495 plan5610

def plan6903 : Plan := .step choices204 bits1505 plan5611

def plan6904 : Plan := .step choices204 bits1494 plan5612

def plan6905 : Plan := .step choices204 bits1498 plan5613

def plan6906 : Plan := .step choices204 bits1494 plan5614

def plan6907 : Plan := .step choices204 bits1502 plan5615

def plan6908 : Plan := .step choices204 bits1499 plan5616

def plan6909 : Plan := .step choices204 bits1495 plan5617

def plan6910 : Plan := .step choices204 bits1507 plan5618

def plan6911 : Plan := .step choices204 bits1506 plan5619

def plan6912 : Plan := .step choices204 bits1503 plan5620

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


