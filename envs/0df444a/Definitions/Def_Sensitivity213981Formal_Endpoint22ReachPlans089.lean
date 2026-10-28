-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans089
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:07:41.557802+00:00
-- url     : https://prove2.me/theorems/d0b13492-f2a0-4148-ab9d-020de68bf3fd
-- title:
--   Endpoint22 Reach Plans089 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans089 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8613`, `ThreeBoundEndpoint22Reachable.plan8614`, `ThreeBoundEndpoint22Reachable.plan8615`, `ThreeBoundEndpoint22Reachable.plan8616`, `ThreeBoundEndpoint22Reachable.plan8617`, `ThreeBoundEndpoint22Reachable.plan8618`, `ThreeBoundEndpoint22Reachable.plan8550`, `ThreeBoundEndpoint22Reachable.plan8619`, `ThreeBoundEndpoint22Reachable.plan8620`, `ThreeBoundEndpoint22Reachable.plan8621`, `ThreeBoundEndpoint22Reachable.plan8622`, `ThreeBoundEndpoint22Reachable.plan8623`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans089.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
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
def plan8545 : Plan := .step choices265 bits1674 plan8121

def plan8546 : Plan := .step choices265 bits1667 plan8141

def plan8547 : Plan := .step choices267 bits1718 plan8146

def plan8548 : Plan := .step choices267 bits1719 plan8158

def plan8549 : Plan := .step choices267 bits1720 plan8161

def plan8550 : Plan := .step choices267 bits1719 plan8165

def plan8551 : Plan := .step choices267 bits1721 plan8184

def plan8552 : Plan := .step choices267 bits1722 plan8188

def plan8553 : Plan := .step choices267 bits1721 plan8189

def plan8554 : Plan := .step choices267 bits1723 plan8193

def plan8555 : Plan := .step choices267 bits1722 plan8194

def plan8556 : Plan := .step choices267 bits1721 plan8195

def plan8557 : Plan := .step choices267 bits1721 plan8206

def plan8558 : Plan := .step choices267 bits1721 plan8218

def plan8559 : Plan := .step choices268 bits1724 plan8145

def plan8560 : Plan := .step choices268 bits1725 plan8146

def plan8561 : Plan := .step choices268 bits1724 plan8147

def plan8562 : Plan := .step choices268 bits1727 plan8153

def plan8563 : Plan := .step choices268 bits1727 plan8156

def plan8564 : Plan := .step choices268 bits1728 plan8158

def plan8565 : Plan := .step choices268 bits1727 plan8159

def plan8566 : Plan := .step choices268 bits1729 plan8161

def plan8567 : Plan := .step choices268 bits1727 plan8163

def plan8568 : Plan := .step choices268 bits1728 plan8165

def plan8569 : Plan := .step choices268 bits1727 plan8166

def plan8570 : Plan := .step choices268 bits1731 plan8181

def plan8571 : Plan := .step choices268 bits1733 plan8184

def plan8572 : Plan := .step choices268 bits1731 plan8185

def plan8573 : Plan := .step choices268 bits1734 plan8188

def plan8574 : Plan := .step choices268 bits1733 plan8189

def plan8575 : Plan := .step choices268 bits1731 plan8190

def plan8576 : Plan := .step choices268 bits1735 plan8193

def plan8577 : Plan := .step choices268 bits1734 plan8194

def plan8578 : Plan := .step choices268 bits1733 plan8195

def plan8579 : Plan := .step choices268 bits1731 plan8196

def plan8580 : Plan := .step choices268 bits1726 plan8199

def plan8581 : Plan := .step choices268 bits1731 plan8204

def plan8582 : Plan := .step choices268 bits1733 plan8206

def plan8583 : Plan := .step choices268 bits1731 plan8207

def plan8584 : Plan := .step choices268 bits1726 plan8211

def plan8585 : Plan := .step choices268 bits1731 plan8216

def plan8586 : Plan := .step choices268 bits1733 plan8218

def plan8587 : Plan := .step choices268 bits1731 plan8219

def plan8588 : Plan := .step choices269 bits1731 plan8152

def plan8589 : Plan := .step choices269 bits1733 plan8153

def plan8590 : Plan := .step choices269 bits1731 plan8154

def plan8591 : Plan := .step choices269 bits1731 plan8155

def plan8592 : Plan := .step choices269 bits1733 plan8156

def plan8593 : Plan := .step choices269 bits1731 plan8157

def plan8594 : Plan := .step choices269 bits1734 plan8158

def plan8595 : Plan := .step choices269 bits1733 plan8159

def plan8596 : Plan := .step choices269 bits1731 plan8160

def plan8597 : Plan := .step choices269 bits1735 plan8161

def plan8598 : Plan := .step choices269 bits1731 plan8162

def plan8599 : Plan := .step choices269 bits1733 plan8163

def plan8600 : Plan := .step choices269 bits1731 plan8164

def plan8601 : Plan := .step choices269 bits1734 plan8165

def plan8602 : Plan := .step choices269 bits1733 plan8166

def plan8603 : Plan := .step choices269 bits1731 plan8167

def plan8604 : Plan := .step choices269 bits1737 plan8179

def plan8605 : Plan := .step choices269 bits1739 plan8181

def plan8606 : Plan := .step choices269 bits1737 plan8182

def plan8607 : Plan := .step choices269 bits1741 plan8184

def plan8608 : Plan := .step choices269 bits1739 plan8185

def plan8609 : Plan := .step choices269 bits1737 plan8186

def plan8610 : Plan := .step choices269 bits1742 plan8188

def plan8611 : Plan := .step choices269 bits1741 plan8189

def plan8612 : Plan := .step choices269 bits1739 plan8190

def plan8613 : Plan := .step choices269 bits1737 plan8191

def plan8614 : Plan := .step choices269 bits1743 plan8193

def plan8615 : Plan := .step choices269 bits1742 plan8194

def plan8616 : Plan := .step choices269 bits1741 plan8195

def plan8617 : Plan := .step choices269 bits1739 plan8196

def plan8618 : Plan := .step choices269 bits1737 plan8197

def plan8619 : Plan := .step choices269 bits1737 plan8203

def plan8620 : Plan := .step choices269 bits1739 plan8204

def plan8621 : Plan := .step choices269 bits1737 plan8205

def plan8622 : Plan := .step choices269 bits1741 plan8206

def plan8623 : Plan := .step choices269 bits1739 plan8207

def plan8624 : Plan := .step choices269 bits1737 plan8208

def plan8625 : Plan := .step choices269 bits1737 plan8209

def plan8626 : Plan := .step choices269 bits1737 plan8210

def plan8627 : Plan := .step choices269 bits1737 plan8215

def plan8628 : Plan := .step choices269 bits1739 plan8216

def plan8629 : Plan := .step choices269 bits1737 plan8217

def plan8630 : Plan := .step choices269 bits1741 plan8218

def plan8631 : Plan := .step choices269 bits1739 plan8219

def plan8632 : Plan := .step choices269 bits1737 plan8220

def plan8633 : Plan := .step choices269 bits1737 plan8221

def plan8634 : Plan := .step choices270 bits1744 plan8178

def plan8635 : Plan := .step choices270 bits1745 plan8179

def plan8636 : Plan := .step choices270 bits1744 plan8180

def plan8637 : Plan := .step choices270 bits1746 plan8181

def plan8638 : Plan := .step choices270 bits1745 plan8182

def plan8639 : Plan := .step choices270 bits1744 plan8183

def plan8640 : Plan := .step choices270 bits1747 plan8184

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


