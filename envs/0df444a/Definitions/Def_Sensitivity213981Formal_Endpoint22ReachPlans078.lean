-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans078
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:01:10.574774+00:00
-- url     : https://prove2.me/theorems/8c79a00c-1adf-460e-8fb7-1bdbdf4bb211
-- title:
--   Endpoint22 Reach Plans078 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans078 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7557`, `ThreeBoundEndpoint22Reachable.plan7558`, `ThreeBoundEndpoint22Reachable.plan7559`, `ThreeBoundEndpoint22Reachable.plan7560`, `ThreeBoundEndpoint22Reachable.plan7561`, `ThreeBoundEndpoint22Reachable.plan7562`, `ThreeBoundEndpoint22Reachable.plan7494`, `ThreeBoundEndpoint22Reachable.plan7563`, `ThreeBoundEndpoint22Reachable.plan7564`, `ThreeBoundEndpoint22Reachable.plan7565`, `ThreeBoundEndpoint22Reachable.plan7566`, `ThreeBoundEndpoint22Reachable.plan7567`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans078.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
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
def plan7489 : Plan := .step choices217 bits1614 plan5807

def plan7490 : Plan := .step choices217 bits1614 plan5814

def plan7491 : Plan := .step choices217 bits1615 plan5815

def plan7492 : Plan := .step choices217 bits1614 plan5816

def plan7493 : Plan := .step choices217 bits1616 plan5817

def plan7494 : Plan := .step choices217 bits1615 plan5818

def plan7495 : Plan := .step choices217 bits1614 plan5819

def plan7496 : Plan := .step choices217 bits1617 plan5820

def plan7497 : Plan := .step choices217 bits1616 plan5821

def plan7498 : Plan := .step choices217 bits1615 plan5822

def plan7499 : Plan := .step choices217 bits1614 plan5823

def plan7500 : Plan := .step choices217 bits1614 plan5825

def plan7501 : Plan := .step choices217 bits1615 plan5827

def plan7502 : Plan := .step choices217 bits1614 plan5828

def plan7503 : Plan := .step choices217 bits1614 plan5860

def plan7504 : Plan := .step choices217 bits1615 plan5862

def plan7505 : Plan := .step choices217 bits1614 plan5863

def plan7506 : Plan := .step choices217 bits1606 plan5899

def plan7507 : Plan := .step choices217 bits1607 plan5900

def plan7508 : Plan := .step choices217 bits1606 plan5901

def plan7509 : Plan := .step choices217 bits1614 plan5902

def plan7510 : Plan := .step choices217 bits1615 plan5903

def plan7511 : Plan := .step choices217 bits1614 plan5904

def plan7512 : Plan := .step choices217 bits1616 plan5905

def plan7513 : Plan := .step choices217 bits1615 plan5906

def plan7514 : Plan := .step choices217 bits1614 plan5907

def plan7515 : Plan := .step choices217 bits1614 plan5908

def plan7516 : Plan := .step choices217 bits1614 plan5920

def plan7517 : Plan := .step choices217 bits1614 plan5927

def plan7518 : Plan := .step choices217 bits1615 plan5928

def plan7519 : Plan := .step choices217 bits1614 plan5929

def plan7520 : Plan := .step choices217 bits1616 plan5930

def plan7521 : Plan := .step choices217 bits1615 plan5931

def plan7522 : Plan := .step choices217 bits1614 plan5932

def plan7523 : Plan := .step choices217 bits1617 plan5933

def plan7524 : Plan := .step choices217 bits1616 plan5934

def plan7525 : Plan := .step choices217 bits1615 plan5935

def plan7526 : Plan := .step choices217 bits1614 plan5936

def plan7527 : Plan := .step choices217 bits1614 plan5949

def plan7528 : Plan := .step choices217 bits1615 plan5951

def plan7529 : Plan := .step choices217 bits1614 plan5952

def plan7530 : Plan := .step choices218 bits1616 plan5770

def plan7531 : Plan := .step choices218 bits1617 plan5771

def plan7532 : Plan := .step choices218 bits1616 plan5772

def plan7533 : Plan := .step choices218 bits1618 plan5773

def plan7534 : Plan := .step choices218 bits1617 plan5774

def plan7535 : Plan := .step choices218 bits1616 plan5775

def plan7536 : Plan := .step choices218 bits1619 plan5776

def plan7537 : Plan := .step choices218 bits1618 plan5777

def plan7538 : Plan := .step choices218 bits1617 plan5778

def plan7539 : Plan := .step choices218 bits1616 plan5779

def plan7540 : Plan := .step choices218 bits1620 plan5780

def plan7541 : Plan := .step choices218 bits1619 plan5781

def plan7542 : Plan := .step choices218 bits1618 plan5782

def plan7543 : Plan := .step choices218 bits1617 plan5783

def plan7544 : Plan := .step choices218 bits1616 plan5784

def plan7545 : Plan := .step choices218 bits1615 plan5814

def plan7546 : Plan := .step choices218 bits1616 plan5815

def plan7547 : Plan := .step choices218 bits1615 plan5816

def plan7548 : Plan := .step choices218 bits1617 plan5817

def plan7549 : Plan := .step choices218 bits1616 plan5818

def plan7550 : Plan := .step choices218 bits1615 plan5819

def plan7551 : Plan := .step choices218 bits1618 plan5820

def plan7552 : Plan := .step choices218 bits1617 plan5821

def plan7553 : Plan := .step choices218 bits1616 plan5822

def plan7554 : Plan := .step choices218 bits1615 plan5823

def plan7555 : Plan := .step choices218 bits1614 plan5824

def plan7556 : Plan := .step choices218 bits1615 plan5825

def plan7557 : Plan := .step choices218 bits1614 plan5826

def plan7558 : Plan := .step choices218 bits1616 plan5827

def plan7559 : Plan := .step choices218 bits1615 plan5828

def plan7560 : Plan := .step choices218 bits1614 plan5829

def plan7561 : Plan := .step choices218 bits1614 plan5830

def plan7562 : Plan := .step choices218 bits1614 plan5841

def plan7563 : Plan := .step choices218 bits1614 plan5859

def plan7564 : Plan := .step choices218 bits1615 plan5860

def plan7565 : Plan := .step choices218 bits1614 plan5861

def plan7566 : Plan := .step choices218 bits1616 plan5862

def plan7567 : Plan := .step choices218 bits1615 plan5863

def plan7568 : Plan := .step choices218 bits1614 plan5864

def plan7569 : Plan := .step choices218 bits1614 plan5872

def plan7570 : Plan := .step choices218 bits1615 plan5927

def plan7571 : Plan := .step choices218 bits1616 plan5928

def plan7572 : Plan := .step choices218 bits1615 plan5929

def plan7573 : Plan := .step choices218 bits1617 plan5930

def plan7574 : Plan := .step choices218 bits1616 plan5931

def plan7575 : Plan := .step choices218 bits1615 plan5932

def plan7576 : Plan := .step choices218 bits1618 plan5933

def plan7577 : Plan := .step choices218 bits1617 plan5934

def plan7578 : Plan := .step choices218 bits1616 plan5935

def plan7579 : Plan := .step choices218 bits1615 plan5936

def plan7580 : Plan := .step choices218 bits1614 plan5948

def plan7581 : Plan := .step choices218 bits1615 plan5949

def plan7582 : Plan := .step choices218 bits1614 plan5950

def plan7583 : Plan := .step choices218 bits1616 plan5951

def plan7584 : Plan := .step choices218 bits1615 plan5952

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


