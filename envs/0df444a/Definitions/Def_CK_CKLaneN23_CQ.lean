-- Prove2me | Definitions.Def_CK_CKLaneN23_CQ
-- name    : CK_CKLaneN23_CQ
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:57:22.423997+00:00
-- url     : https://prove2.me/theorems/9c11ff6f-309d-48bb-b900-3ee5a5c25bbe
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CQ` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CQ` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CQ` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CQ (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CQ.lean)

import Definitions.Def_CK_CKLaneN23_CStep2

-- ===== source module CKLaneN23.CQ =====
section

/-!
# CKLaneN23.CQ — compact rational literals for large certificate data (Lane N23b)

`qq n d = n / d`.  Certificate literals written with `qq` elaborate much faster than `((n : ℚ) / d)`
(no `binop%` elaboration per coefficient); the kernel evaluates `qq n d` to the normalized rational.
-/

namespace CKLaneN23.CT

/-- `n / d` as a rational -/
def qq (n : ℤ) (d : ℕ) : ℚ := (n : ℚ) / (d : ℚ)

end CKLaneN23.CT

end


