-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerClosure_q00
-- name    : CK_CKLaneN23_CornerClosure_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-12T19:19:22.166962+00:00
-- url     : https://prove2.me/theorems/751767d6-7c13-41bc-912e-6caa1ba6c6e3
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerClosure (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerClosure (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerClosure (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerClosure (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerClosure (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneN23_CornerOkUC
import Definitions.Def_CK_CKLaneN23_CornerOkUE
import Definitions.Def_CK_CKLaneN23_CornerOkTC
import Definitions.Def_CK_CKLaneN23_CornerOkPosCells



/-!
# CKLaneN23.CornerClosure — the closed RA-stat corner theorem `GammaCorner (1/20)` (Lane N23b)

The Boolean corner checker `cornerCheck = ucCheck && (ueCheck && (tcCheck && posCheckC))` is evaluated by
the kernel (`decide +kernel` in `CornerOk{UC,UE,TC}` and the 128 positivity cells `PosCell.C<j>_<k>` assembled in `CornerOkPosCells`, no `native_decide`); `cornerCheck_sound`
(its only premise is the check) turns it into `GammaCorner (1/20)`.
-/

namespace CKLaneN23.CT

theorem cornerCheck_ok : cornerCheck = true := by
  show (ucCheck && (ueCheck && (tcCheck && posCheckC))) = true
  rw [uc_ok, ue_ok, tc_ok, pos_ok]
  all_goals rfl

end CKLaneN23.CT

namespace CKLaneN23.RS

end CKLaneN23.RS


