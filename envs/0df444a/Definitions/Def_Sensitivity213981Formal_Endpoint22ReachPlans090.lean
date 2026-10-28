-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans090
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:07:38.924992+00:00
-- url     : https://prove2.me/theorems/70d809ec-6b82-4194-962f-d70f7999d32b
-- title:
--   Endpoint22 Reach Plans090 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans090 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8709`, `ThreeBoundEndpoint22Reachable.plan8710`, `ThreeBoundEndpoint22Reachable.plan8711`, `ThreeBoundEndpoint22Reachable.plan8712`, `ThreeBoundEndpoint22Reachable.plan8713`, `ThreeBoundEndpoint22Reachable.plan8714`, `ThreeBoundEndpoint22Reachable.plan8715`, `ThreeBoundEndpoint22Reachable.plan8646`, `ThreeBoundEndpoint22Reachable.plan8716`, `ThreeBoundEndpoint22Reachable.plan8717`, `ThreeBoundEndpoint22Reachable.plan8718`, `ThreeBoundEndpoint22Reachable.plan8719`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans090.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
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
def plan8641 : Plan := .step choices270 bits1746 plan8185

def plan8642 : Plan := .step choices270 bits1745 plan8186

def plan8643 : Plan := .step choices270 bits1744 plan8187

def plan8644 : Plan := .step choices270 bits1748 plan8188

def plan8645 : Plan := .step choices270 bits1747 plan8189

def plan8646 : Plan := .step choices270 bits1746 plan8190

def plan8647 : Plan := .step choices270 bits1745 plan8191

def plan8648 : Plan := .step choices270 bits1744 plan8192

def plan8649 : Plan := .step choices270 bits1749 plan8193

def plan8650 : Plan := .step choices270 bits1748 plan8194

def plan8651 : Plan := .step choices270 bits1747 plan8195

def plan8652 : Plan := .step choices270 bits1746 plan8196

def plan8653 : Plan := .step choices270 bits1745 plan8197

def plan8654 : Plan := .step choices270 bits1744 plan8198

def plan8655 : Plan := .step choices271 bits1726 plan8148

def plan8656 : Plan := .step choices271 bits1730 plan8149

def plan8657 : Plan := .step choices271 bits1732 plan8150

def plan8658 : Plan := .step choices271 bits1730 plan8151

def plan8659 : Plan := .step choices271 bits1736 plan8169

def plan8660 : Plan := .step choices271 bits1738 plan8171

def plan8661 : Plan := .step choices271 bits1736 plan8172

def plan8662 : Plan := .step choices271 bits1740 plan8174

def plan8663 : Plan := .step choices271 bits1738 plan8175

def plan8664 : Plan := .step choices271 bits1736 plan8176

def plan8665 : Plan := .step choices271 bits1736 plan8201

def plan8666 : Plan := .step choices271 bits1736 plan8213

def plan8667 : Plan := .step choices272 bits1744 plan8168

def plan8668 : Plan := .step choices272 bits1745 plan8169

def plan8669 : Plan := .step choices272 bits1744 plan8170

def plan8670 : Plan := .step choices272 bits1746 plan8171

def plan8671 : Plan := .step choices272 bits1745 plan8172

def plan8672 : Plan := .step choices272 bits1744 plan8173

def plan8673 : Plan := .step choices272 bits1747 plan8174

def plan8674 : Plan := .step choices272 bits1746 plan8175

def plan8675 : Plan := .step choices272 bits1745 plan8176

def plan8676 : Plan := .step choices272 bits1744 plan8177

def plan8677 : Plan := .step choices272 bits1744 plan8200

def plan8678 : Plan := .step choices272 bits1745 plan8201

def plan8679 : Plan := .step choices272 bits1744 plan8202

def plan8680 : Plan := .step choices272 bits1744 plan8212

def plan8681 : Plan := .step choices272 bits1745 plan8213

def plan8682 : Plan := .step choices272 bits1744 plan8214

def plan8683 : Plan := .step choices275 bits1726 plan8148

def plan8684 : Plan := .step choices275 bits1730 plan8149

def plan8685 : Plan := .step choices275 bits1732 plan8150

def plan8686 : Plan := .step choices275 bits1730 plan8151

def plan8687 : Plan := .step choices275 bits1736 plan8169

def plan8688 : Plan := .step choices275 bits1738 plan8171

def plan8689 : Plan := .step choices275 bits1736 plan8172

def plan8690 : Plan := .step choices275 bits1740 plan8174

def plan8691 : Plan := .step choices275 bits1738 plan8175

def plan8692 : Plan := .step choices275 bits1736 plan8176

def plan8693 : Plan := .step choices275 bits1736 plan8201

def plan8694 : Plan := .step choices275 bits1736 plan8213

def plan8695 : Plan := .step choices276 bits1744 plan8168

def plan8696 : Plan := .step choices276 bits1745 plan8169

def plan8697 : Plan := .step choices276 bits1744 plan8170

def plan8698 : Plan := .step choices276 bits1746 plan8171

def plan8699 : Plan := .step choices276 bits1745 plan8172

def plan8700 : Plan := .step choices276 bits1744 plan8173

def plan8701 : Plan := .step choices276 bits1747 plan8174

def plan8702 : Plan := .step choices276 bits1746 plan8175

def plan8703 : Plan := .step choices276 bits1745 plan8176

def plan8704 : Plan := .step choices276 bits1744 plan8177

def plan8705 : Plan := .step choices276 bits1744 plan8212

def plan8706 : Plan := .step choices276 bits1745 plan8213

def plan8707 : Plan := .step choices276 bits1744 plan8214

def plan8708 : Plan := .step choices278 bits1764 plan8247

def plan8709 : Plan := .step choices278 bits1764 plan8262

def plan8710 : Plan := .step choices278 bits1765 plan8265

def plan8711 : Plan := .step choices278 bits1764 plan8270

def plan8712 : Plan := .step choices278 bits1764 plan8279

def plan8713 : Plan := .step choices278 bits1765 plan8283

def plan8714 : Plan := .step choices278 bits1764 plan8284

def plan8715 : Plan := .step choices278 bits1766 plan8288

def plan8716 : Plan := .step choices278 bits1765 plan8289

def plan8717 : Plan := .step choices278 bits1764 plan8290

def plan8718 : Plan := .step choices278 bits1767 plan8294

def plan8719 : Plan := .step choices278 bits1764 plan8297

def plan8720 : Plan := .step choices278 bits1764 plan8308

def plan8721 : Plan := .step choices278 bits1765 plan8311

def plan8722 : Plan := .step choices278 bits1764 plan8316

def plan8723 : Plan := .step choices278 bits1766 plan8319

def plan8724 : Plan := .step choices278 bits1765 plan8320

def plan8725 : Plan := .step choices278 bits1764 plan8321

def plan8726 : Plan := .step choices279 bits1768 plan8246

def plan8727 : Plan := .step choices279 bits1769 plan8247

def plan8728 : Plan := .step choices279 bits1768 plan8248

def plan8729 : Plan := .step choices279 bits1768 plan8257

def plan8730 : Plan := .step choices279 bits1768 plan8260

def plan8731 : Plan := .step choices279 bits1769 plan8262

def plan8732 : Plan := .step choices279 bits1768 plan8263

def plan8733 : Plan := .step choices279 bits1770 plan8265

def plan8734 : Plan := .step choices279 bits1768 plan8268

def plan8735 : Plan := .step choices279 bits1769 plan8270

def plan8736 : Plan := .step choices279 bits1768 plan8271

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


