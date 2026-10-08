-- Prove2me | Definitions.Def_CK_CKLaneM06_CapXHB_B022
-- name    : CK_CKLaneM06_CapXHB_B022
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:22:06.044226+00:00
-- url     : https://prove2.me/theorems/d4a0f765-0bb7-4eb3-b532-d826db3889cc
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapXHB.B022` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapXHB.B022` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapXHB.B022` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapXHB.B022 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapXHB/B022.lean)

import Definitions.Def_CK_CKLaneM06_CapXHB_B022_part00

/-! Cap cover `cross` (root `xhRoot`) bundle B022: 6 cut pieces, 331 non-vacuous checker leaves
(331 secant), depth `S = 3/40`.  Tree literals copied verbatim from the generated CapXH/Cnnn sources
(M06/work/rebundle_xh.py). -/

set_option autoImplicit false

namespace CKLaneM06.Cap.CapXHB.B022

open CKLaneM06.Cap

theorem cap_4 : CapOn (cpathBox xhRoot path_4) (3 / 40) := CTree2.sound_path check_ok_4

/-- piece `030303031` (was `CapXH.C167`): 38 non-vacuous leaves,
38 secant. -/
def path_5 : List ℕ := [0, 3, 0, 3, 0, 3, 0, 3, 1]

def tree_5 : CTree2 :=
  (.node 1 (.node 0 (.node 1 (.node 0 (.node 1 (.node 0 (.node 1 (.sec ⟨(25726594481 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(102156848511 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 1 (.sec ⟨(51839871543 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(102928659065 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩))) (.node 0 (.node 1 (.sec ⟨(101405659817 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(100652785961 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 1 (.sec ⟨(25543975683 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(101421448011 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)))) (.node 1 (.node 0 (.node 1 (.sec ⟨(52225616145 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(51849303643 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 1 (.sec ⟨(105220875931 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(52233361681 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩))) (.node 0 (.node 1 (.sec ⟨(102944296997 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(51094137579 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 1 (.sec ⟨(51855436297 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(25738324293 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩))))) (.node 0 (.node 1 (.node 0 (.node 1 (.sec ⟨(24974550085 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(24785468901 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 1 (.sec ⟨(100665268105 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(99907335457 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩))) (.node 0 (.node 1 (.sec ⟨(98383783619 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(97623319027 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 1 (.sec ⟨(99147041071 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(24595945905 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)))) (.node 1 (.node 0 (.node 1 (.sec ⟨(50715257387 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(12583800399 / 137438953472 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.sec ⟨(50715257387 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 0 (.node 1 (.sec ⟨(99907335457 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) .vac) .vac)))) (.node 1 (.node 0 (.node 1 (.node 0 (.node 1 (.sec ⟨(52994351773 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(52616518315 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.sec ⟨(105997575609 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 0 (.sec ⟨(51857974797 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(104475658657 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩))) (.node 1 (.node 0 (.sec ⟨(106759766133 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) (.sec ⟨(53759512381 / 549755813888 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩)) (.node 0 (.sec ⟨(105232439003 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) .vac))) (.node 0 (.node 1 (.node 0 (.node 1 (.sec ⟨(102953297173 / 1099511627776 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) .vac) .vac) .vac) .vac))) (.node 0 (.node 1 (.node 0 (.node 1 (.node 0 (.node 1 (.sec ⟨(24214971025 / 274877906944 : ℚ), (46755299213 / 137438953472 : ℚ), true, (0 : ℚ)⟩) .vac) .vac) .vac) .vac) .vac) .vac))

theorem check_ok_5 : tree_5.check (3 / 40) (cpathBox xhRoot path_5) = true := by decide +kernel

theorem cap_5 : CapOn (cpathBox xhRoot path_5) (3 / 40) := CTree2.sound_path check_ok_5

end CKLaneM06.Cap.CapXHB.B022


