-- Prove2me | Definitions.Def_CK_CKLaneP_Cells_S3_C000_0000__12
-- name    : CK_CKLaneP_Cells_S3_C000_0000__12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T18:41:58.586017+00:00
-- url     : https://prove2.me/theorems/a936da4d-f3c6-4c5f-a775-f78632f568f4
-- title:
--   Courtade–Kumar proof module `CKLaneP.Cells.S3.C000_0000 (+11 modules: CKLaneP.Cells.S3.C001_0000, CKLaneP.Cells.S3.C002_0000, CKLaneP.Cells.S3.C003_0000, CKLaneP.Cells.S3.C004_0000, CKLan…
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.Cells.S3.C000_0000 (+11 modules: CKLaneP.Cells.S3.C001_0000, CKLaneP.Cells.S3.C002_0000, CKLaneP.Cells.S3.C003_0000, CKLaneP.Cells.S3.C004_0000, CKLaneP.Cells.S3.C005_0000, CKLaneP.Cells.S3.C006_0000, CKLaneP.Cells.S3.C007_0000, CKLaneP.Cells.S3.C008_0000, CKLaneP.Cells.S3.C009_0000, CKLaneP.Cells.S3.C010_0000, CKLaneP.Cells.S3.C011_0000)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.Cells.S3.C000_0000 (+11 modules: CKLaneP.Cells.S3.C001_0000, CKLaneP.Cells.S3.C002_0000, CKLaneP.Cells.S3.C003_0000, CKLaneP.Cells.S3.C004_0000, CKLaneP.Cells.S3.C005_0000, CKLaneP.Cells.S3.C006_0000, CKLaneP.Cells.S3.C007_0000, CKLaneP.Cells.S3.C008_0000, CKLaneP.Cells.S3.C009_0000, CKLaneP.Cells.S3.C010_0000, CKLaneP.Cells.S3.C011_0000)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.Cells.S3.C000_0000 (+11 modules: CKLaneP.Cells.S3.C001_0000, CKLaneP.Cells.S3.C002_0000, CKLaneP.Cells.S3.C003_0000, CKLaneP.Cells.S3.C004_0000, CKLaneP.Cells.S3.C005_0000, CKLaneP.Cells.S3.C006_0000, CKLaneP.Cells.S3.C007_0000, CKLaneP.Cells.S3.C008_0000, CKLaneP.Cells.S3.C009_0000, CKLaneP.Cells.S3.C010_0000, CKLaneP.Cells.S3.C011_0000) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/Cells/S3/C000_0000 (+11 modules: CKLaneP/Cells/S3/C001_0000, CKLaneP/Cells/S3/C002_0000, CKLaneP/Cells/S3/C003_0000, CKLaneP/Cells/S3/C004_0000, CKLaneP/Cells/S3/C005_0000, CKLaneP/Cells/S3/C006_0000, CKLaneP/Cells/S3/C007_0000, CKLaneP/Cells/S3/C008_0000, CKLaneP/Cells/S3/C009_0000, CKLaneP/Cells/S3/C010_0000, CKLaneP/Cells/S3/C011_0000).lean)

import Definitions.Def_CK_CKLaneP_SeamTree

-- ===== source module CKLaneP.Cells.S3.C000_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C000_0000

open CKLaneP

def tree : STree :=
  STree.st (49999 / 500000 : ℚ)
    (STree.leaf SLeaf.tq)
    (STree.leaf (SLeaf.v 0 115292151 5764480701899 115292265752836 115292265843028 0 91696373138268448))

theorem check : STree.check (1 / 200000 : ℚ) tree (0 : ℚ) (1 / 10000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C000_0000

end

-- ===== source module CKLaneP.Cells.S3.C001_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C001_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 25000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (11 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 115292150 126821366 3458872196689 5764722815185 5765908084674 115291688 53126878555977008))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 126821365 138350581 3458883034151 5764733191479 5765918462877 126820903 53127422220830744)))))
          (STree.leaf (SLeaf.v 115292150 138350581 5764708980126 17293926332039 17297131559598 115291688 91704093611731120)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (13 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 138350580 149879796 3458893871613 5764743567772 5765928841080 138350118 53127964502187272))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 149879795 160256090 3458904778250 5764752791144 5765938066135 149879333 53128506675874048)))))
          (STree.leaf (SLeaf.v 138350580 160256090 5764729848005 17293941320018 17297146549131 138350118 91705194403255840))))
      (STree.leaf (SLeaf.v 115292150 160256090 17293889784426 57646120194282 57652467549211 115291688 246803291751113632)))
    (STree.leaf (SLeaf.v 115292150 160256090 57646030266403 115292080132473 115292080238258 115291688 436199380713921792))

theorem check : STree.check (1 / 200000 : ℚ) tree (1 / 10000000000 : ℚ) (139 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C001_0000

end

-- ===== source module CKLaneP.Cells.S3.C002_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C002_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (1 / 6250000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (3 / 20000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 160256089 172938226 3458914393616 5764764435652 5765949712814 160255627 53128990264723416))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 172938225 184467441 3458926383999 5764774696653 5765959975690 172937763 53129584116160760)))))
          (STree.leaf (SLeaf.v 160256089 184467441 5764749332379 17293958959717 17297164190830 160255627 91706229691946544)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (9 / 50000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 184467440 207525871 3458936529709 5764796602161 5765981885368 184466978 53130110257452880))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 207525870 222513851 3458958688860 5764809284298 5765994569741 207525408 53131191070845848)))))
          (STree.leaf (SLeaf.v 184467440 222513851 5764769739089 17293989742721 17297194977782 184466978 91707350622348560))))
      (STree.leaf (SLeaf.v 160256089 222513851 17293916071036 57646137488104 57652484838099 160255627 246804652109565472)))
    (STree.leaf (SLeaf.v 160256089 222513851 57646012972581 115292052462357 115292052564308 160255627 436199656108441088))

theorem check : STree.check (1 / 200000 : ℚ) tree (139 / 1000000000000 : ℚ) (193 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C002_0000

end

-- ===== source module CKLaneP.Cells.S3.C003_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C003_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (23 / 100000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (1 / 5000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 222513850 230584301 3458973192612 5764815855951 5766001142521 222513388 53131893444906296))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 230584300 265171947 3458979187804 5764849636551 5766034929656 230583838 53132240656027360)))))
          (STree.leaf (SLeaf.v 222513850 265171947 5764803519690 17294020986894 17297226225522 222513388 91709131851648688)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (1 / 4000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 265171946 288230377 3459012391944 5764869236216 5766054532790 265171484 53133850603754256))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 288230376 307830042 3459034274394 5764886530039 5766071829754 288229914 53134916290459920)))))
          (STree.leaf (SLeaf.v 265171946 307830042 5764841911976 17294050847561 17297256089393 265171484 91711127077207920))))
      (STree.leaf (SLeaf.v 222513850 307830042 17293952733940 57646160546534 57652507889696 222513388 246806519610037536)))
    (STree.leaf (SLeaf.v 222513850 307830042 57645989914151 115292013263026 115292013359864 222513388 436200035033870272))

theorem check : STree.check (1 / 200000 : ℚ) tree (193 / 1000000000000 : ℚ) (267 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C003_0000

end

-- ===== source module CKLaneP.Cells.S3.C004_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C004_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 10000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (7 / 25000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 307830041 322818022 3459052974780 5764899558052 5766084860109 307829579 53135821886327800))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 322818021 345876452 3459066579254 5764921117684 5766106423805 322817559 53136501615068184)))))
          (STree.leaf (SLeaf.v 307830041 345876452 5764880765430 17294076096542 17297281340867 307829579 91713120595610896)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (33 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 345876451 380464097 3459087562426 5764953399486 5766138711687 345875989 53137546467991928))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 380464096 427733879 3459119313884 5764997210503 5766182530919 380463634 53139114629413096)))))
          (STree.leaf (SLeaf.v 345876451 427733879 5764910626097 17294146540046 17297351793974 345875989 91714812689344096))))
      (STree.leaf (SLeaf.v 307830041 427733879 17294002078980 57646195134179 57652542467981 307829579 246809044091039840)))
    (STree.leaf (SLeaf.v 307830041 427733879 57645955326505 115291962534480 115291962623650 307829579 436200542554340096))

theorem check : STree.check (1 / 200000 : ℚ) tree (267 / 1000000000000 : ℚ) (371 / 1000000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C004_0000

end

-- ===== source module CKLaneP.Cells.S3.C005_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C005_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (1 / 2500000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (39 / 100000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 427733878 449639387 3459165269335 5765014389034 5766199712306 427733415 53141294114940312))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 449639386 461168602 3459186483091 5765023727698 5766209052564 449638923 53142300351591760)))))
          (STree.leaf (SLeaf.v 427733878 461168602 5764989140052 17294155417542 17297360670160 427733415 91718670295206160)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (9 / 20000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 461168601 518814678 3459194553541 5765080220852 5766265556669 461168138 53142777475753728))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.v 518814677 592601654 3459247772398 5765148243220 5766333591750 518814214 53145373386355056)))))
          (STree.leaf (SLeaf.v 461168601 592601654 5765009431470 17294276820176 17297482090396 461168138 91720045161096208))))
      (STree.leaf (SLeaf.v 427733878 592601654 17294072522484 57646240098118 57652587418761 427733415 246812567151341184)))
    (STree.leaf (SLeaf.v 427733878 592601654 57645910362567 115291887594582 115291887673783 427733415 436201255188398592))

theorem check : STree.check (1 / 200000 : ℚ) tree (371 / 1000000000000 : ℚ) (257 / 500000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C005_0000

end

-- ===== source module CKLaneP.Cells.S3.C006_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C006_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 5000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (7 / 12500000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.st (3 / 50 : ℚ)
                (STree.leaf SLeaf.tq)
                (STree.leaf (SLeaf.wK 592601653 645636043 3459318377311 5765193898912 5766379255594 592601190 (2791063847262474028974081 / 1208925819614629174706176 : ℚ) 36546171057283544 36546170984190280 (3686082857339871 / 2251799813685248 : ℚ) 54938572219622952 54938572329501016 20765499816603000))))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 645636042 691752903 1730007140365 5765234712333 5766420076443 645635579 (2691638849406714387628033 / 1208925819614629174706176 : ℚ) 38160934764923896 38160934688601112 (5489487695251847 / 4503599627370496 : ℚ) 77397495438962768 77397495593758672 10068590580988304))))
          (STree.leaf (SLeaf.v 592601653 691752903 5765130949397 17294336541510 17297541816628 592601190 91726109214743344)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (13 / 20000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 691752902 749398978 1730051527843 5765287746722 5766473120730 691752439 (2614342487742087486767105 / 1208925819614629174706176 : ℚ) 39508436510230544 39508436431212752 (2661083838573395 / 2251799813685248 : ℚ) 80186492146481440 80186492306855360 10423410992050868)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 749398977 823185955 1730106960309 5765355769091 5766541155811 749398513 (2527625130837774084079617 / 1208925819614629174706176 : ℚ) 41126466362230944 41126466279977088 (320809338438679 / 281474976710656 : ℚ) 83561412430855040 83561412597978784 10850127415089210))))
          (STree.leaf (SLeaf.v 691752902 823185955 5765216957341 17294438229187 17297643516721 691752439 91730563618739136))))
      (STree.leaf (SLeaf.v 592601653 823185955 17294168214969 57646305814644 57652653117198 592601190 246817349892448800)))
    (STree.leaf (SLeaf.v 592601653 823185955 57645844646041 115291788443333 115291788507964 592601190 436202216135678016))

theorem check : STree.check (1 / 200000 : ℚ) tree (257 / 500000000000 : ℚ) (357 / 500000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C006_0000

end

-- ===== source module CKLaneP.Cells.S3.C007_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C007_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (1 / 1250000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (19 / 25000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 823185954 876220344 1730179156254 5765401424783 5766586819656 823185490 (2429764835285665421721601 / 1208925819614629174706176 : ℚ) 43102440281056208 43102440194850400 (2506221385727699 / 2251799813685248 : ℚ) 85843890930742208 85843891102430912 11372531878630138)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 876220343 922337204 1730230807137 5765442238204 5766627640504 876219879 (2366952238633654390095873 / 1208925819614629174706176 : ℚ) 44463595336166944 44463595247238832 (1228840807855697 / 1125899906842624 : ℚ) 87763771361765296 87763771537293776 11733074301336926))))
          (STree.leaf (SLeaf.v 823185954 922337204 5765338475268 17294497950521 17297703242953 823185490 91736562930478800)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (9 / 10000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 922337203 1037629355 1730273465233 5765552918669 5766738342169 922336739 (2316658599543885214515201 / 1208925819614629174706176 : ℚ) 45610698119418072 45610698028195752 (2348851675268147 / 2251799813685248 : ℚ) 92353841154807792 92353841339516400 12036909814403928)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1037629354 1141392290 1730385644495 5765645152389 5766830592724 1037628889 (2205432533768608789037057 / 1208925819614629174706176 : ℚ) 48347136138573504 48347136041878304 (4531375052895151 / 4503599627370496 : ℚ) 96153389215097664 96153389407405376 12764705660042272))))
          (STree.leaf (SLeaf.v 922337203 1141392290 5765415721008 17294687260232 17297892578574 922336739 91740831507276208))))
      (STree.leaf (SLeaf.v 823185954 1141392290 17294303337370 57646393436678 57652740713928 823185490 246823982756955008)))
    (STree.leaf (SLeaf.v 823185954 1141392290 57645757024007 115291645481066 115291645526270 823185490 436203553349858112))

theorem check : STree.check (1 / 200000 : ℚ) tree (357 / 500000000000 : ℚ) (99 / 100000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C007_0000

end

-- ===== source module CKLaneP.Cells.S3.C008_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C008_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 2500000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (11 / 10000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1141392289 1268213656 1730485602790 5765761597461 5766947059502 1141391824 (2119634143085460874854401 / 1208925819614629174706176 : ℚ) 50668138449856024 50668138348518824 (544276290946761 / 562949953421312 : ℚ) 100510965366030288 100510965567053136 13383965665920488)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1268213655 1383505806 1730608965391 5765864207475 5767049688260 1268213189 (2028945433757339244036097 / 1208925819614629174706176 : ℚ) 53349053083357496 53349052976658472 (2107171910876659 / 2251799813685248 : ℚ) 104200456166457792 104200456374859616 14102171583206272))))
          (STree.leaf (SLeaf.v 1141392289 1383505806 5765610564743 17294863657222 17298068995562 1141391824 91750612126048176)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (13 / 10000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1383505805 1498797956 1730720798777 5765967970410 5767153470290 1383505338 (1957212464663290796048385 / 1208925819614629174706176 : ℚ) 55656514784543632 55656514673229680 (4089857232034837 / 4503599627370496 : ℚ) 107686817083228752 107686817298603312 14722679181588174)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1498797955 1579502462 1730833669792 5766037145700 5767222657894 1498797488 (1893638073420086775906305 / 1208925819614629174706176 : ℚ) 57856075265513344 57856075149800272 (8022097782150051 / 9007199254740992 : ℚ) 109999874757915520 109999874977916192 15316630768973954))))
          (STree.leaf (SLeaf.v 1383505805 1579502462 5765833078593 17294987019823 17298192369240 1383505338 91761474368469568))))
      (STree.leaf (SLeaf.v 1141392289 1579502462 17294490110653 57646513340515 57652860582845 1141391824 246833043341674784)))
    (STree.leaf (SLeaf.v 1141392289 1579502462 57645637120170 115291447178567 115291447197187 1141391824 436205379416072384))

theorem check : STree.check (1 / 200000 : ℚ) tree (99 / 100000000000 : ℚ) (137 / 100000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C008_0000

end

-- ===== source module CKLaneP.Cells.S3.C009_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C009_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (1 / 625000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (3 / 2000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1579502461 1729382257 1730909877903 5766178955046 5767364494168 1579501993 (1853210866110994241814529 / 1208925819614629174706176 : ℚ) 59337476928871088 59337476810195216 (3876909088311373 / 4503599627370496 : ℚ) 114139970869552880 114139971097833744 15717148300704410)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1729382256 1844674408 1731056298934 5766279259216 5767464816380 1729381787 (1785507520116409721946113 / 1208925819614629174706176 : ℚ) 61976126111477344 61976125987524176 (473201733212175 / 562949953421312 : ℚ) 117113988174048288 117113988408277184 16434435804813174))))
          (STree.leaf (SLeaf.v 1579502461 1844674408 5766002558054 17295193392772 17298398767558 1579501993 91770049198963184)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (17 / 10000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1844674407 1959966558 1731168132320 5766383022152 5767568598411 1844673937 (1738952732620878631665665 / 1208925819614629174706176 : ℚ) 63915245805978776 63915245678147368 (3701613334980529 / 4503599627370496 : ℚ) 119970042488146832 119970042728087824 16963538961883508)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 1959966557 2202080074 1731276161065 5766613606453 5767799226669 1959966086 (1696442639187890287935489 / 1208925819614629174706176 : ℚ) 65782736361568512 65782736230002112 (7089527178834949 / 9007199254740992 : ℚ) 125633803347035728 125633803598304272 17473758004005940))))
          (STree.leaf (SLeaf.v 1844674407 2202080074 5766231989434 17295471246855 17298676655754 1844673937 91781600943940416))))
      (STree.leaf (SLeaf.v 1579502461 2202080074 17294741447541 57646697807955 57653045002225 1579501993 246845327483460224)))
    (STree.leaf (SLeaf.v 1579502461 2202080074 57645452652729 115291193535836 115291193513558 1579501993 436207825083914816))

theorem check : STree.check (1 / 200000 : ℚ) tree (137 / 100000000000 : ℚ) (191 / 100000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C009_0000

end

-- ===== source module CKLaneP.Cells.S3.C010_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C010_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (11 / 5000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (1 / 500000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 2202080073 2305843010 1731515161693 5766693158037 5767878791228 2202079600 (1617881887780601790988289 / 1208925819614629174706176 : ℚ) 69501892459786280 69501892320781576 (6973252571905275 / 9007199254740992 : ℚ) 127850233626828672 127850233882530048 18499010755137960)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 2305843009 2536427311 1731612007100 5766913366044 5768099041283 2305842535 (1587951876676420747919361 / 1208925819614629174706176 : ℚ) 71018749696988880 71018749554950464 (841498405937923 / 1125899906842624 : ℚ) 132667544844100000 132667545109436000 18917570590008428))))
          (STree.leaf (SLeaf.v 2202080073 2536427311 5766555960377 17295698372391 17298903804573 2202079600 91797333441348864)))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (3 / 1250000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 2536427310 2767011612 1731835673872 5767120891915 5768306605342 2536426834 (1527887764050778186055681 / 1208925819614629174706176 : ℚ) 74246902559319472 74246902410824752 (815225225953915 / 1125899906842624 : ℚ) 137120965776108448 137120966050351296 19815388065530792)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 2767011611 3055241988 1732057611261 5767386063861 5768571826776 2767011133 (1475237324748210839748609 / 1208925819614629174706176 : ℚ) 77297459440565552 77297459285969712 (6290584797834509 / 9007199254740992 : ℚ) 142319362638427232 142319362923066880 20668896444236876))))
          (STree.leaf (SLeaf.v 2536427310 3055241988 5766838426145 17296116882897 17299322368587 2536426834 91811639336467632))))
      (STree.leaf (SLeaf.v 2202080073 3055241988 17295108076580 57646928392256 57653275518198 2202079600 246862691644009984)))
    (STree.leaf (SLeaf.v 2202080073 3055241988 57645222068428 115290801542525 115290801469124 2202079600 436211322448872832))

theorem check : STree.check (1 / 200000 : ℚ) tree (191 / 100000000000 : ℚ) (53 / 20000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C010_0000

end

-- ===== source module CKLaneP.Cells.S3.C011_0000 =====
section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CKLaneP.Cells.S3.C011_0000

open CKLaneP

def tree : STree :=
  STree.st (1 : ℚ)
    (STree.st (3 / 10 : ℚ)
      (STree.sp (3 / 1000000000 : ℚ)
        (STree.st (1 / 10 : ℚ)
          (STree.sp (7 / 2500000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 3055241987 3228180213 1732340653491 5767530179049 5768715967096 3055241505 (1417687449726856758034433 / 1208925819614629174706176 : ℚ) 80894870934412000 80894870772621344 (6167844802274313 / 9007199254740992 : ℚ) 145215243897888768 145215244188320192 21684867389240388)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 3228180212 3458764514 1732506674187 5767743469527 5768929297515 3228179728 (1386797160079677336846337 / 1208925819614629174706176 : ℚ) 82949969323061424 82949969157160560 (3007739441038193 / 4503599627370496 : ℚ) 148949991854602528 148949992152503456 22267633825065720))))
          (STree.st (1 / 5 : ℚ)
            (STree.st (3 / 20 : ℚ)
              (STree.leaf (SLeaf.wK 3055241987 3458764514 5767316888570 8649911762768 8651647851322 3055241505 (1672973874451186150539265 / 1208925819614629174706176 : ℚ) 66855949270673552 66855949136960736 (1168102320892273 / 1125899906842624 : ℚ) 92914570449149984 92914570634980032 43061436321304384))
              (STree.leaf (SLeaf.v 3055241987 3458764514 8649447711861 11532062762185 11534319142634 3055241505 137656049112525792)))
            (STree.leaf (SLeaf.v 3055241987 3458764514 11531578535152 17296364761021 17299570267908 3055241505 178978564338934784))))
        (STree.st (1 / 10 : ℚ)
          (STree.sp (33 / 10000000000 : ℚ)
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 3458764513 3804640966 1732726882195 5768066287549 5769252176326 3458764026 (1349146447692768850477057 / 1208925819614629174706176 : ℚ) 85582382696266944 85582382525101248 (2905812509256983 / 4503599627370496 : ℚ) 154203861193971328 154203861502379968 23017722320175368)))
            (STree.st (3 / 100 : ℚ)
              (STree.leaf SLeaf.tq)
              (STree.leaf (SLeaf.wK 3804640965 4231221922 1733059961217 5768458280860 5769644242737 3804640473 (1298980986304275236782081 / 1208925819614629174706176 : ℚ) 89325992322701616 89325992144048720 (2796961561669751 / 4503599627370496 : ℚ) 160163547401714496 160163547722042496 24093581958727648))))
          (STree.st (1 / 5 : ℚ)
            (STree.st (3 / 20 : ℚ)
              (STree.leaf (SLeaf.wK 3458764513 4231221922 5767643165355 8650623691797 8652359906021 3458764026 (1590655864027563010555905 / 1208925819614629174706176 : ℚ) 70879299426950648 70879299285191128 (8655405204648165 / 9007199254740992 : ℚ) 101192603309852672 101192603512238816 45715353946148144))
              (STree.leaf (SLeaf.v 3458764513 4231221922 8649735365776 11532754515088 11535011008002 3458764026 137671630451118432)))
            (STree.leaf (SLeaf.v 3458764513 4231221922 11531827566197 17297016161671 17300221755663 3458764026 178992397619258496)))))
      (STree.leaf (SLeaf.v 3055241987 4231221922 17295608444513 57647251210278 57653598242591 3055241505 246886206627362784)))
    (STree.leaf (SLeaf.v 3055241987 4231221922 57644899250407 115290271198633 115290271053661 3055241505 436216043645803328))

theorem check : STree.check (1 / 200000 : ℚ) tree (53 / 20000000000 : ℚ) (367 / 100000000000 : ℚ) (0 : ℚ) (2 : ℚ) = true := by
  decide +kernel

end CKLaneP.Cells.S3.C011_0000

end


