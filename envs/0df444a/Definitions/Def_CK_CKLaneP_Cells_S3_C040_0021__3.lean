-- Prove2me | Definitions.Def_CK_CKLaneP_Cells_S3_C040_0021__3
-- name    : CK_CKLaneP_Cells_S3_C040_0021__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:34:15.345008+00:00
-- url     : https://prove2.me/theorems/5bc7515c-1f71-4adb-9bb9-7318d2a141e1
-- title:
--   Courtade–Kumar proof module `CKLaneP.Cells.S3.C040_0021 (+2 modules: CKLaneP.Cells.S3.C040_0022, CKLaneP.Cells.S3.C040_0023)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.Cells.S3.C040_0021 (+2 modules: CKLaneP.Cells.S3.C040_0022, CKLaneP.Cells.S3.C040_0023)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.Cells.S3.C040_0021 (+2 modules: CKLaneP.Cells.S3.C040_0022, CKLaneP.Cells.S3.C040_0023)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.Cells.S3.C040_0021 (+2 modules: CKLaneP.Cells.S3.C040_0022, CKLaneP.Cells.S3.C040_0023) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/Cells/S3/C040_0021 (+2 modules: CKLaneP/Cells/S3/C040_0022, CKLaneP/Cells/S3/C040_0023).lean)

import Definitions.Def_CK_CKLaneP_Cells_S3_C040_0021__3_q01

-- ===== source module CKLaneP.Cells.S3.C040_0023 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C040_0023

open CKLaneP

def tree : STree :=
  STree.sp (21 / 500000 : ℚ)
    (STree.leaf (SLeaf.nA 47950005376598 48422703193488 51331524149611 51333092209604 47945621874931 (4709809978367939706881 / 1208925819614629174706176 : ℚ) 571969324186187584 571969324177203776))
    (STree.st (1 / 10 : ℚ)
      (STree.leaf (SLeaf.nA 48422703193487 49275865106897 50198202310583 50199798700344 48418232451687 (1463336763140744937473 / 1208925819614629174706176 : ℚ) 575065211517326912 575065211514534848))
      (STree.st (1 / 5 : ℚ)
        (STree.leaf (SLeaf.nA 48422703193487 49275865106897 51120539514268 51122075545537 48418232451687 (2949060131606182232065 / 1208925819614629174706176 : ℚ) 573648357689607360 573648357683981632))
        (STree.st (1 / 4 : ℚ)
          (STree.st (11 / 50 : ℚ)
            (STree.leaf (SLeaf.nA 48422703193487 49275865106897 51305006955005 51306530522241 48418232451687 (3249201605366413000705 / 1208925819614629174706176 : ℚ) 573362136769817152 573362136763619008))
            (STree.st (6 / 25 : ℚ)
              (STree.sp (53 / 1250000 : ℚ)
                (STree.leaf (SLeaf.nA 48422703193487 48883871795331 51097481084176 51099018664253 48418232451687 (3525043092879124201473 / 1208925819614629174706176 : ℚ) 573099091711798784 573099091705074560))
                (STree.leaf (SLeaf.nA 48883871795330 49275865106897 51378793931300 51380267268353 48879315108454 (3308728437373819420673 / 1208925819614629174706176 : ℚ) 573305371173962688 573305371167651008)))
              (STree.sp (53 / 1250000 : ℚ)
                (STree.leaf (SLeaf.nA 48422703193487 48883871795331 51189714804545 51191246177129 48418232451687 (3674936005464888967169 / 1208925819614629174706176 : ℚ) 572956153664369472 572956153657359296))
                (STree.leaf (SLeaf.nA 48883871795330 49275865106897 51466415965650 51467883233834 48879315108454 (3449256282932984676353 / 1208925819614629174706176 : ℚ) 573171362440571072 573171362433991360)))))
          (STree.st (7 / 25 : ℚ)
            (STree.st (13 / 50 : ℚ)
              (STree.sp (53 / 1250000 : ℚ)
                (STree.leaf (SLeaf.nA 48422703193487 48883871795331 51281948524913 51283473657306 48418232451687 (3825080104568610619393 / 1208925819614629174706176 : ℚ) 572812977020175552 572812977012879040))
                (STree.leaf (SLeaf.nA 48883871795330 49275865106897 51554038000000 51555499169800 48879315108454 (3590008911262650466305 / 1208925819614629174706176 : ℚ) 573037140123376128 573037140116528000)))
              (STree.sp (53 / 1250000 : ℚ)
                (STree.leaf (SLeaf.nA 48422703193487 48883871795331 51466415965650 51467928519562 48418232451687 (4126116744989021044737 / 1208925819614629174706176 : ℚ) 572525912993711424 572525912985840832))
                (STree.leaf (SLeaf.nA 48883871795330 49275865106897 51729282068701 51730730953188 48879315108454 (3872172733802157703169 / 1208925819614629174706176 : ℚ) 572768069928890624 572768069921504384))))
            (STree.sp (53 / 1250000 : ℚ)
              (STree.leaf (SLeaf.nA 48422703193487 48883871795331 51650883406387 51652383251015 48418232451687 (4428157985233673650177 / 1208925819614629174706176 : ℚ) 572237895240712576 572237895232265984))
              (STree.leaf (SLeaf.nA 48883871795330 49275865106897 51904526137401 51905962618508 48879315108454 (4155223046165076377601 / 1208925819614629174706176 : ℚ) 572498157880330944 572498157872404800)))))))

theorem check : STree.check (1 / 200000 : ℚ) tree (4159 / 100000000 : ℚ) (2137 / 50000000 : ℚ) (0 : ℚ) (3 / 10 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C040_0023

end


