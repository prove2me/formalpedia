-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactAll_hi
-- name    : CK_CKLaneC2R_CompactAll_hi
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T05:59:43.698159+00:00
-- url     : https://prove2.me/theorems/78c7abd3-d27c-433a-8ec4-3e4e52f457ce
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactAll (strips 3-5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactAll (strips 3-5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactAll (strips 3-5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactAll (strips 3-5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactAll (strips 3-5).lean)

import Definitions.Def_CK_CKLaneC2R_CompactAll_hi_a
import Definitions.Def_CK_CKLaneC2R_CompactCover_S05

section
namespace CKLaneC2R

theorem compact_hi_certified {a z : ℝ} (ha1 : (1 / 2 : ℝ) < a) (ha2 : a ≤ 999 / 1000)
    (hz1 : (43 / 500 : ℝ) ≤ z) (hz2 : z ≤ 999 / 1000) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  have q3 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  have q4 : ((7 / 10 : ℚ) : ℝ) = 7 / 10 := by norm_num
  have q5 : ((9 / 10 : ℚ) : ℝ) = 9 / 10 := by norm_num
  have q6 : ((999 / 1000 : ℚ) : ℝ) = 999 / 1000 := by norm_num
  have qz : ((43 / 500 : ℚ) : ℝ) = 43 / 500 := by norm_num
  have hz1' : ((43 / 500 : ℚ) : ℝ) ≤ z := by rw [qz]; exact hz1
  have hz2' : z ≤ ((999 / 1000 : ℚ) : ℝ) := by rw [q6]; exact hz2
  rcases le_or_gt a (9 / 10) with h5 | h5
  · exact compact_hi_a_certified ha1 h5 hz1 hz2
  · exact CompactCover.strip5 (by rw [q5]; exact h5.le) (by rw [q6]; exact ha2) hz1' hz2'

end CKLaneC2R
end


