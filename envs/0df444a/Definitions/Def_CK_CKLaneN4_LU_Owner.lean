-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Owner
-- name    : CK_CKLaneN4_LU_Owner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T14:17:15.729043+00:00
-- url     : https://prove2.me/theorems/c1128afc-c6b8-4ba2-9cb9-b2e16884cc6f
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Owner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Owner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Owner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Owner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Owner.lean)

import Definitions.Def_CK_CKLaneN4_LU_Cover
import Definitions.Def_CK_CKLaneN4_LU_OwnerBridge

-- ===== source module CKLaneN4.LU.Owner =====
section
/-
Lane N4b — the left-upper owner proposition from the certified cover (F-C consumer root).

`leftUpperOwner : GeneralCK.LeftUpperOutsideWideHalfCollarAndNarrowOwner` (unconditional: the
cover `root_good` is the conjunction of 1131 kernel-checked cells + the analytic origin lemma).
`leftUpper_lt_one`: the `f < 1` part of the `leftUpper` field (corpus reduction
`zeroCap_leftUpper_of_outsideWideHalfCollarAndNarrow`).
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK

theorem ATOP_ge : (5 : ℝ) / 11 ≤ (ATOP : ℝ) / 2 ^ 64 := by
  unfold ATOP; norm_num

theorem leftUpperOwner : LeftUpperOutsideWideHalfCollarAndNarrowOwner :=
  owner_of_box ATOP_ge root_good

theorem leftUpper_lt_one : ∀ e f : ℝ, 0 < e → e < f → f < 1 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f :=
  zeroCap_leftUpper_of_outsideWideHalfCollarAndNarrow leftUpperOwner

end CKLaneN4.LU

end


