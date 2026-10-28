-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans077
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:01:00.423933+00:00
-- url     : https://prove2.me/theorems/9315f281-7df8-434b-94ea-80ec24ad9cb5
-- title:
--   Endpoint22 Reach Plans077 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans077 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7397`, `ThreeBoundEndpoint22Reachable.plan7460`, `ThreeBoundEndpoint22Reachable.plan7461`, `ThreeBoundEndpoint22Reachable.plan7462`, `ThreeBoundEndpoint22Reachable.plan7463`, `ThreeBoundEndpoint22Reachable.plan7464`, `ThreeBoundEndpoint22Reachable.plan7465`, `ThreeBoundEndpoint22Reachable.plan7466`, `ThreeBoundEndpoint22Reachable.plan7467`, `ThreeBoundEndpoint22Reachable.plan7468`, `ThreeBoundEndpoint22Reachable.plan7469`, `ThreeBoundEndpoint22Reachable.plan7398`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans077.lean, lines 1–206.

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
def plan7393 : Plan := .step choices215 bits1606 plan5956

def plan7394 : Plan := .step choices215 bits1608 plan5957

def plan7395 : Plan := .step choices215 bits1607 plan5958

def plan7396 : Plan := .step choices215 bits1606 plan5959

def plan7397 : Plan := .step choices215 bits1609 plan5960

def plan7398 : Plan := .step choices215 bits1606 plan5962

def plan7399 : Plan := .step choices215 bits1607 plan5963

def plan7400 : Plan := .step choices215 bits1606 plan5964

def plan7401 : Plan := .step choices215 bits1608 plan5965

def plan7402 : Plan := .step choices215 bits1607 plan5966

def plan7403 : Plan := .step choices215 bits1606 plan5967

def plan7404 : Plan := .step choices215 bits1610 plan5968

def plan7405 : Plan := .step choices215 bits1609 plan5969

def plan7406 : Plan := .step choices215 bits1608 plan5970

def plan7407 : Plan := .step choices215 bits1607 plan5971

def plan7408 : Plan := .step choices215 bits1612 plan5972

def plan7409 : Plan := .step choices215 bits1611 plan5973

def plan7410 : Plan := .step choices215 bits1610 plan5974

def plan7411 : Plan := .step choices215 bits1609 plan5975

def plan7412 : Plan := .step choices215 bits1608 plan5976

def plan7413 : Plan := .step choices216 bits1617 plan5883

def plan7414 : Plan := .step choices216 bits1618 plan5884

def plan7415 : Plan := .step choices216 bits1617 plan5885

def plan7416 : Plan := .step choices216 bits1619 plan5886

def plan7417 : Plan := .step choices216 bits1618 plan5887

def plan7418 : Plan := .step choices216 bits1617 plan5888

def plan7419 : Plan := .step choices216 bits1620 plan5889

def plan7420 : Plan := .step choices216 bits1619 plan5890

def plan7421 : Plan := .step choices216 bits1618 plan5891

def plan7422 : Plan := .step choices216 bits1617 plan5892

def plan7423 : Plan := .step choices216 bits1621 plan5893

def plan7424 : Plan := .step choices216 bits1620 plan5894

def plan7425 : Plan := .step choices216 bits1619 plan5895

def plan7426 : Plan := .step choices216 bits1618 plan5896

def plan7427 : Plan := .step choices216 bits1617 plan5897

def plan7428 : Plan := .step choices216 bits1622 plan5898

def plan7429 : Plan := .step choices216 bits1621 plan5972

def plan7430 : Plan := .step choices216 bits1620 plan5973

def plan7431 : Plan := .step choices216 bits1619 plan5974

def plan7432 : Plan := .step choices216 bits1618 plan5975

def plan7433 : Plan := .step choices216 bits1617 plan5976

def plan7434 : Plan := .step choices217 bits1606 plan5740

def plan7435 : Plan := .step choices217 bits1606 plan5741

def plan7436 : Plan := .step choices217 bits1607 plan5742

def plan7437 : Plan := .step choices217 bits1606 plan5743

def plan7438 : Plan := .step choices217 bits1608 plan5744

def plan7439 : Plan := .step choices217 bits1606 plan5745

def plan7440 : Plan := .step choices217 bits1607 plan5746

def plan7441 : Plan := .step choices217 bits1606 plan5747

def plan7442 : Plan := .step choices217 bits1606 plan5748

def plan7443 : Plan := .step choices217 bits1607 plan5749

def plan7444 : Plan := .step choices217 bits1606 plan5750

def plan7445 : Plan := .step choices217 bits1608 plan5751

def plan7446 : Plan := .step choices217 bits1607 plan5752

def plan7447 : Plan := .step choices217 bits1606 plan5753

def plan7448 : Plan := .step choices217 bits1609 plan5754

def plan7449 : Plan := .step choices217 bits1608 plan5755

def plan7450 : Plan := .step choices217 bits1607 plan5756

def plan7451 : Plan := .step choices217 bits1606 plan5757

def plan7452 : Plan := .step choices217 bits1610 plan5758

def plan7453 : Plan := .step choices217 bits1606 plan5759

def plan7454 : Plan := .step choices217 bits1607 plan5760

def plan7455 : Plan := .step choices217 bits1606 plan5761

def plan7456 : Plan := .step choices217 bits1608 plan5762

def plan7457 : Plan := .step choices217 bits1606 plan5763

def plan7458 : Plan := .step choices217 bits1607 plan5764

def plan7459 : Plan := .step choices217 bits1606 plan5765

def plan7460 : Plan := .step choices217 bits1609 plan5766

def plan7461 : Plan := .step choices217 bits1608 plan5767

def plan7462 : Plan := .step choices217 bits1607 plan5768

def plan7463 : Plan := .step choices217 bits1606 plan5769

def plan7464 : Plan := .step choices217 bits1615 plan5770

def plan7465 : Plan := .step choices217 bits1616 plan5771

def plan7466 : Plan := .step choices217 bits1615 plan5772

def plan7467 : Plan := .step choices217 bits1617 plan5773

def plan7468 : Plan := .step choices217 bits1616 plan5774

def plan7469 : Plan := .step choices217 bits1615 plan5775

def plan7470 : Plan := .step choices217 bits1618 plan5776

def plan7471 : Plan := .step choices217 bits1617 plan5777

def plan7472 : Plan := .step choices217 bits1616 plan5778

def plan7473 : Plan := .step choices217 bits1615 plan5779

def plan7474 : Plan := .step choices217 bits1619 plan5780

def plan7475 : Plan := .step choices217 bits1618 plan5781

def plan7476 : Plan := .step choices217 bits1617 plan5782

def plan7477 : Plan := .step choices217 bits1616 plan5783

def plan7478 : Plan := .step choices217 bits1615 plan5784

def plan7479 : Plan := .step choices217 bits1606 plan5785

def plan7480 : Plan := .step choices217 bits1607 plan5786

def plan7481 : Plan := .step choices217 bits1606 plan5787

def plan7482 : Plan := .step choices217 bits1614 plan5788

def plan7483 : Plan := .step choices217 bits1615 plan5789

def plan7484 : Plan := .step choices217 bits1614 plan5790

def plan7485 : Plan := .step choices217 bits1616 plan5791

def plan7486 : Plan := .step choices217 bits1615 plan5792

def plan7487 : Plan := .step choices217 bits1614 plan5793

def plan7488 : Plan := .step choices217 bits1614 plan5795

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


