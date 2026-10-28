-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans079
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:02:05.698691+00:00
-- url     : https://prove2.me/theorems/1900664c-b80e-42b3-b808-a792d9184831
-- title:
--   Endpoint22 Reach Plans079 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans079 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7589`, `ThreeBoundEndpoint22Reachable.plan7652`, `ThreeBoundEndpoint22Reachable.plan7653`, `ThreeBoundEndpoint22Reachable.plan7654`, `ThreeBoundEndpoint22Reachable.plan7655`, `ThreeBoundEndpoint22Reachable.plan7656`, `ThreeBoundEndpoint22Reachable.plan7657`, `ThreeBoundEndpoint22Reachable.plan7658`, `ThreeBoundEndpoint22Reachable.plan7659`, `ThreeBoundEndpoint22Reachable.plan7660`, `ThreeBoundEndpoint22Reachable.plan7661`, `ThreeBoundEndpoint22Reachable.plan7590`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans079.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
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
def plan7585 : Plan := .step choices218 bits1614 plan5953

def plan7586 : Plan := .step choices218 bits1614 plan5961

def plan7587 : Plan := .step choices221 bits1606 plan5740

def plan7588 : Plan := .step choices221 bits1606 plan5741

def plan7589 : Plan := .step choices221 bits1607 plan5742

def plan7590 : Plan := .step choices221 bits1606 plan5743

def plan7591 : Plan := .step choices221 bits1608 plan5744

def plan7592 : Plan := .step choices221 bits1606 plan5745

def plan7593 : Plan := .step choices221 bits1607 plan5746

def plan7594 : Plan := .step choices221 bits1606 plan5747

def plan7595 : Plan := .step choices221 bits1606 plan5748

def plan7596 : Plan := .step choices221 bits1607 plan5749

def plan7597 : Plan := .step choices221 bits1606 plan5750

def plan7598 : Plan := .step choices221 bits1608 plan5751

def plan7599 : Plan := .step choices221 bits1607 plan5752

def plan7600 : Plan := .step choices221 bits1606 plan5753

def plan7601 : Plan := .step choices221 bits1609 plan5754

def plan7602 : Plan := .step choices221 bits1608 plan5755

def plan7603 : Plan := .step choices221 bits1607 plan5756

def plan7604 : Plan := .step choices221 bits1606 plan5757

def plan7605 : Plan := .step choices221 bits1610 plan5758

def plan7606 : Plan := .step choices221 bits1606 plan5759

def plan7607 : Plan := .step choices221 bits1607 plan5760

def plan7608 : Plan := .step choices221 bits1606 plan5761

def plan7609 : Plan := .step choices221 bits1608 plan5762

def plan7610 : Plan := .step choices221 bits1606 plan5763

def plan7611 : Plan := .step choices221 bits1607 plan5764

def plan7612 : Plan := .step choices221 bits1606 plan5765

def plan7613 : Plan := .step choices221 bits1609 plan5766

def plan7614 : Plan := .step choices221 bits1608 plan5767

def plan7615 : Plan := .step choices221 bits1607 plan5768

def plan7616 : Plan := .step choices221 bits1606 plan5769

def plan7617 : Plan := .step choices221 bits1615 plan5770

def plan7618 : Plan := .step choices221 bits1616 plan5771

def plan7619 : Plan := .step choices221 bits1615 plan5772

def plan7620 : Plan := .step choices221 bits1617 plan5773

def plan7621 : Plan := .step choices221 bits1616 plan5774

def plan7622 : Plan := .step choices221 bits1615 plan5775

def plan7623 : Plan := .step choices221 bits1618 plan5776

def plan7624 : Plan := .step choices221 bits1617 plan5777

def plan7625 : Plan := .step choices221 bits1616 plan5778

def plan7626 : Plan := .step choices221 bits1615 plan5779

def plan7627 : Plan := .step choices221 bits1619 plan5780

def plan7628 : Plan := .step choices221 bits1618 plan5781

def plan7629 : Plan := .step choices221 bits1617 plan5782

def plan7630 : Plan := .step choices221 bits1616 plan5783

def plan7631 : Plan := .step choices221 bits1615 plan5784

def plan7632 : Plan := .step choices221 bits1614 plan5814

def plan7633 : Plan := .step choices221 bits1615 plan5815

def plan7634 : Plan := .step choices221 bits1614 plan5816

def plan7635 : Plan := .step choices221 bits1616 plan5817

def plan7636 : Plan := .step choices221 bits1615 plan5818

def plan7637 : Plan := .step choices221 bits1614 plan5819

def plan7638 : Plan := .step choices221 bits1617 plan5820

def plan7639 : Plan := .step choices221 bits1616 plan5821

def plan7640 : Plan := .step choices221 bits1615 plan5822

def plan7641 : Plan := .step choices221 bits1614 plan5823

def plan7642 : Plan := .step choices221 bits1614 plan5825

def plan7643 : Plan := .step choices221 bits1615 plan5827

def plan7644 : Plan := .step choices221 bits1614 plan5828

def plan7645 : Plan := .step choices221 bits1614 plan5860

def plan7646 : Plan := .step choices221 bits1615 plan5862

def plan7647 : Plan := .step choices221 bits1614 plan5863

def plan7648 : Plan := .step choices221 bits1606 plan5899

def plan7649 : Plan := .step choices221 bits1607 plan5900

def plan7650 : Plan := .step choices221 bits1606 plan5901

def plan7651 : Plan := .step choices221 bits1614 plan5902

def plan7652 : Plan := .step choices221 bits1615 plan5903

def plan7653 : Plan := .step choices221 bits1614 plan5904

def plan7654 : Plan := .step choices221 bits1616 plan5905

def plan7655 : Plan := .step choices221 bits1615 plan5906

def plan7656 : Plan := .step choices221 bits1614 plan5907

def plan7657 : Plan := .step choices221 bits1614 plan5908

def plan7658 : Plan := .step choices221 bits1614 plan5920

def plan7659 : Plan := .step choices221 bits1614 plan5927

def plan7660 : Plan := .step choices221 bits1615 plan5928

def plan7661 : Plan := .step choices221 bits1614 plan5929

def plan7662 : Plan := .step choices221 bits1616 plan5930

def plan7663 : Plan := .step choices221 bits1615 plan5931

def plan7664 : Plan := .step choices221 bits1614 plan5932

def plan7665 : Plan := .step choices221 bits1617 plan5933

def plan7666 : Plan := .step choices221 bits1616 plan5934

def plan7667 : Plan := .step choices221 bits1615 plan5935

def plan7668 : Plan := .step choices221 bits1614 plan5936

def plan7669 : Plan := .step choices221 bits1614 plan5949

def plan7670 : Plan := .step choices221 bits1615 plan5951

def plan7671 : Plan := .step choices221 bits1614 plan5952

def plan7672 : Plan := .step choices222 bits1616 plan5770

def plan7673 : Plan := .step choices222 bits1617 plan5771

def plan7674 : Plan := .step choices222 bits1616 plan5772

def plan7675 : Plan := .step choices222 bits1618 plan5773

def plan7676 : Plan := .step choices222 bits1617 plan5774

def plan7677 : Plan := .step choices222 bits1616 plan5775

def plan7678 : Plan := .step choices222 bits1619 plan5776

def plan7679 : Plan := .step choices222 bits1618 plan5777

def plan7680 : Plan := .step choices222 bits1617 plan5778

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


