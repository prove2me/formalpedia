-- Prove2me | Definitions.Def_CK_CKLaneP_Cells_S3_C040_0009
-- name    : CK_CKLaneP_Cells_S3_C040_0009
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T19:55:48.189399+00:00
-- url     : https://prove2.me/theorems/ec9c521c-3e8b-4924-84b1-197b94c7d02f
-- title:
--   Courtade–Kumar proof module `CKLaneP.Cells.S3.C040_0009` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.Cells.S3.C040_0009` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.Cells.S3.C040_0009` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.Cells.S3.C040_0009 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/Cells/S3/C040_0009.lean)

import Definitions.Def_CK_CKLaneP_Cells_S3_C040_0009_part00
import Definitions.Def_CK_CKLaneP_Cells_S3_C040_0009_k00
import Definitions.Def_CK_CKLaneP_Cells_S3_C040_0009_k01
import Definitions.Def_CK_CKLaneP_Cells_S3_C040_0009_k02
import Definitions.Def_CK_CKLaneP_Cells_S3_C040_0009_k03

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C040_0009

open CKLaneP

theorem sp_ok {qT m p0 p1 t0 t1 : ℚ} {a b : STree} (ha : a.check qT p0 m t0 t1 = true)
    (hb : b.check qT m p1 t0 t1 = true) : (STree.sp m a b).check qT p0 p1 t0 t1 = true := by
  simp [STree.check, ha, hb]

theorem st_ok {qT m p0 p1 t0 t1 : ℚ} {a b : STree} (ha : a.check qT p0 p1 t0 m = true)
    (hb : b.check qT p0 p1 m t1 = true) : (STree.st m a b).check qT p0 p1 t0 t1 = true := by
  simp [STree.check, ha, hb]

theorem tree_eq : tree = (STree.st (3 / 5 : ℚ) (STree.st (2 / 5 : ℚ) sub00 sub01) (STree.st (4 / 5 : ℚ) sub02 sub03)) := rfl

theorem check : STree.check (1 / 200000 : ℚ) tree (233 / 6250000 : ℚ) (479 / 12500000 : ℚ) (3 / 10 : ℚ) (1 : ℚ) = true := by
  rw [tree_eq]; exact (st_ok (st_ok check00 check01) (st_ok check02 check03))

end CKLaneP.Cells.S3.C040_0009


