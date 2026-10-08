-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactAll
-- name    : CK_CKLaneC2R_CompactAll
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T06:26:35.806521+00:00
-- url     : https://prove2.me/theorems/76571a6e-7d0e-4f32-90a4-8c8b6d4fe787
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactAll` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactAll` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactAll` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactAll (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactAll.lean)

import Definitions.Def_CK_CKLaneC2R_CompactAll_lo
import Definitions.Def_CK_CKLaneC2R_CompactAll_hi

section
namespace CKLaneC2R

theorem compact_all_certified {a z : ℝ} (ha1 : (3 / 20 : ℝ) ≤ a) (ha2 : a ≤ 999 / 1000)
    (hz1 : (43 / 500 : ℝ) ≤ z) (hz2 : z ≤ 999 / 1000) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  rcases le_or_gt a (1 / 2) with h | h
  · exact compact_lo_certified ha1 h hz1 hz2
  · exact compact_hi_certified h ha2 hz1 hz2

end CKLaneC2R
end


