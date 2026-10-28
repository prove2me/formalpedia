-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans088
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:05:51.920859+00:00
-- url     : https://prove2.me/theorems/c733f6bc-567e-4b2f-bc5e-30d75b42f6d5
-- title:
--   Endpoint22 Reach Plans088 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans088 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8517`, `ThreeBoundEndpoint22Reachable.plan8518`, `ThreeBoundEndpoint22Reachable.plan8519`, `ThreeBoundEndpoint22Reachable.plan8520`, `ThreeBoundEndpoint22Reachable.plan8521`, `ThreeBoundEndpoint22Reachable.plan8454`, `ThreeBoundEndpoint22Reachable.plan8522`, `ThreeBoundEndpoint22Reachable.plan8523`, `ThreeBoundEndpoint22Reachable.plan8524`, `ThreeBoundEndpoint22Reachable.plan8525`, `ThreeBoundEndpoint22Reachable.plan8526`, `ThreeBoundEndpoint22Reachable.plan8527`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans088.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
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
def plan8449 : Plan := .step choices248 bits1569 plan8093

def plan8450 : Plan := .step choices248 bits1571 plan8094

def plan8451 : Plan := .step choices248 bits1570 plan8095

def plan8452 : Plan := .step choices248 bits1569 plan8096

def plan8453 : Plan := .step choices248 bits1572 plan8097

def plan8454 : Plan := .step choices248 bits1571 plan8098

def plan8455 : Plan := .step choices248 bits1570 plan8099

def plan8456 : Plan := .step choices248 bits1569 plan8100

def plan8457 : Plan := .step choices249 bits1568 plan8089

def plan8458 : Plan := .step choices250 bits1569 plan8088

def plan8459 : Plan := .step choices250 bits1570 plan8089

def plan8460 : Plan := .step choices250 bits1569 plan8090

def plan8461 : Plan := .step choices253 bits1568 plan8089

def plan8462 : Plan := .step choices254 bits1569 plan8088

def plan8463 : Plan := .step choices254 bits1570 plan8089

def plan8464 : Plan := .step choices254 bits1569 plan8090

def plan8465 : Plan := .step choices256 bits1653 plan8111

def plan8466 : Plan := .step choices256 bits1654 plan8128

def plan8467 : Plan := .step choices256 bits1655 plan8132

def plan8468 : Plan := .step choices256 bits1654 plan8133

def plan8469 : Plan := .step choices257 bits1653 plan8103

def plan8470 : Plan := .step choices257 bits1656 plan8105

def plan8471 : Plan := .step choices257 bits1658 plan8109

def plan8472 : Plan := .step choices257 bits1659 plan8111

def plan8473 : Plan := .step choices257 bits1658 plan8112

def plan8474 : Plan := .step choices257 bits1660 plan8125

def plan8475 : Plan := .step choices257 bits1661 plan8128

def plan8476 : Plan := .step choices257 bits1660 plan8129

def plan8477 : Plan := .step choices257 bits1662 plan8132

def plan8478 : Plan := .step choices257 bits1661 plan8133

def plan8479 : Plan := .step choices257 bits1660 plan8134

def plan8480 : Plan := .step choices257 bits1657 plan8139

def plan8481 : Plan := .step choices257 bits1657 plan8143

def plan8482 : Plan := .step choices258 bits1665 plan8104

def plan8483 : Plan := .step choices258 bits1666 plan8105

def plan8484 : Plan := .step choices258 bits1665 plan8106

def plan8485 : Plan := .step choices258 bits1669 plan8108

def plan8486 : Plan := .step choices258 bits1672 plan8109

def plan8487 : Plan := .step choices258 bits1669 plan8110

def plan8488 : Plan := .step choices258 bits1673 plan8111

def plan8489 : Plan := .step choices258 bits1672 plan8112

def plan8490 : Plan := .step choices258 bits1669 plan8113

def plan8491 : Plan := .step choices258 bits1664 plan8114

def plan8492 : Plan := .step choices258 bits1664 plan8115

def plan8493 : Plan := .step choices258 bits1675 plan8123

def plan8494 : Plan := .step choices258 bits1677 plan8125

def plan8495 : Plan := .step choices258 bits1675 plan8126

def plan8496 : Plan := .step choices258 bits1679 plan8128

def plan8497 : Plan := .step choices258 bits1677 plan8129

def plan8498 : Plan := .step choices258 bits1675 plan8130

def plan8499 : Plan := .step choices258 bits1680 plan8132

def plan8500 : Plan := .step choices258 bits1679 plan8133

def plan8501 : Plan := .step choices258 bits1677 plan8134

def plan8502 : Plan := .step choices258 bits1675 plan8135

def plan8503 : Plan := .step choices258 bits1668 plan8138

def plan8504 : Plan := .step choices258 bits1671 plan8139

def plan8505 : Plan := .step choices258 bits1668 plan8140

def plan8506 : Plan := .step choices258 bits1668 plan8142

def plan8507 : Plan := .step choices258 bits1671 plan8143

def plan8508 : Plan := .step choices258 bits1668 plan8144

def plan8509 : Plan := .step choices259 bits1681 plan8122

def plan8510 : Plan := .step choices259 bits1682 plan8123

def plan8511 : Plan := .step choices259 bits1681 plan8124

def plan8512 : Plan := .step choices259 bits1683 plan8125

def plan8513 : Plan := .step choices259 bits1682 plan8126

def plan8514 : Plan := .step choices259 bits1681 plan8127

def plan8515 : Plan := .step choices259 bits1684 plan8128

def plan8516 : Plan := .step choices259 bits1683 plan8129

def plan8517 : Plan := .step choices259 bits1682 plan8130

def plan8518 : Plan := .step choices259 bits1681 plan8131

def plan8519 : Plan := .step choices259 bits1685 plan8132

def plan8520 : Plan := .step choices259 bits1684 plan8133

def plan8521 : Plan := .step choices259 bits1683 plan8134

def plan8522 : Plan := .step choices259 bits1682 plan8135

def plan8523 : Plan := .step choices259 bits1681 plan8136

def plan8524 : Plan := .step choices260 bits1663 plan8107

def plan8525 : Plan := .step choices260 bits1667 plan8117

def plan8526 : Plan := .step choices260 bits1670 plan8119

def plan8527 : Plan := .step choices260 bits1667 plan8120

def plan8528 : Plan := .step choices261 bits1674 plan8116

def plan8529 : Plan := .step choices261 bits1676 plan8117

def plan8530 : Plan := .step choices261 bits1674 plan8118

def plan8531 : Plan := .step choices261 bits1678 plan8119

def plan8532 : Plan := .step choices261 bits1676 plan8120

def plan8533 : Plan := .step choices261 bits1674 plan8121

def plan8534 : Plan := .step choices261 bits1667 plan8137

def plan8535 : Plan := .step choices261 bits1667 plan8141

def plan8536 : Plan := .step choices264 bits1663 plan8107

def plan8537 : Plan := .step choices264 bits1667 plan8117

def plan8538 : Plan := .step choices264 bits1670 plan8119

def plan8539 : Plan := .step choices264 bits1667 plan8120

def plan8540 : Plan := .step choices265 bits1674 plan8116

def plan8541 : Plan := .step choices265 bits1676 plan8117

def plan8542 : Plan := .step choices265 bits1674 plan8118

def plan8543 : Plan := .step choices265 bits1678 plan8119

def plan8544 : Plan := .step choices265 bits1676 plan8120

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


