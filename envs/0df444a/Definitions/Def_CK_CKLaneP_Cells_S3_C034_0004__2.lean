-- Prove2me | Definitions.Def_CK_CKLaneP_Cells_S3_C034_0004__2
-- name    : CK_CKLaneP_Cells_S3_C034_0004__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:20:28.035983+00:00
-- url     : https://prove2.me/theorems/988a1965-bfaf-47c1-a8f7-228ed879e566
-- title:
--   Courtade–Kumar proof module `CKLaneP.Cells.S3.C034_0004 (+1 modules: CKLaneP.Cells.S3.C034_0005)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.Cells.S3.C034_0004 (+1 modules: CKLaneP.Cells.S3.C034_0005)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.Cells.S3.C034_0004 (+1 modules: CKLaneP.Cells.S3.C034_0005)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.Cells.S3.C034_0004 (+1 modules: CKLaneP.Cells.S3.C034_0005) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/Cells/S3/C034_0004 (+1 modules: CKLaneP/Cells/S3/C034_0005).lean)

import Definitions.Def_CK_CKLaneP_SeamTree

-- ===== source module CKLaneP.Cells.S3.C034_0004 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C034_0004

open CKLaneP

def tree : STree :=
  STree.sp (3 / 500000 : ℚ)
    (STree.leaf (SLeaf.v 5706961447803 6917529027642 46289798409964 58856642810180 58862346826857 5706900318437 441447536532107008))
    (STree.st (9 / 10 : ℚ)
      (STree.sp (1 / 156250 : ℚ)
        (STree.leaf (SLeaf.v 6917529027641 7378697629484 47131431108327 53034389211915 53039990896170 6917439107242 448998208190618880))
        (STree.leaf (SLeaf.v 7378697629483 7920570736650 47159101224438 53161210577422 53166766112244 7378595278308 451183691566069184)))
      (STree.leaf (SLeaf.v 6917529027641 7920570736650 51670483071965 58649116939351 58654688265801 6917439107242 457273259008325888)))

theorem check : STree.check (1 / 200000 : ℚ) tree (99 / 20000000 : ℚ) (687 / 100000000 : ℚ) (4 / 5 : ℚ) (1 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C034_0004

end

-- ===== source module CKLaneP.Cells.S3.C034_0005 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C034_0005

open CKLaneP

def tree : STree :=
  STree.leaf (SLeaf.v 5706961447803 7920570736650 55432465941497 111798798301726 111798322659519 5706900318437 458445957944841280)

theorem check : STree.check (1 / 200000 : ℚ) tree (99 / 20000000 : ℚ) (687 / 100000000 : ℚ) (1 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C034_0005

end


