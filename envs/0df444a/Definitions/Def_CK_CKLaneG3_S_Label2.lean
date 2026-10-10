-- Prove2me | Definitions.Def_CK_CKLaneG3_S_Label2
-- name    : CK_CKLaneG3_S_Label2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T19:48:04.99608+00:00
-- url     : https://prove2.me/theorems/8d23a03f-1c58-46c2-bf66-33a81241cd5f
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.Label2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.Label2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.Label2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.Label2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/Label2.lean)

import Definitions.Def_CK_CKLaneG3_S_Label2_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.Label2
open CKLaneD CKLaneG3 CKLaneG3.S
/-- Every archived (S) leaf with owner label 2 satisfies the `SS_Compact` obligation. -/
theorem label2 : ∀ q ∈ sTree.leaves, q.2 = 2 → SLeafOK (sBox q.1) :=
  fam_root (P := PP) sTree
    (fam_node (P := PP) 2 _ _ _
    CKLaneG3.S.C2.B0.c_4
    (fam_node (P := PP) 0 _ _ _
     (fam_node (P := PP) 1 _ _ _
      (fam_node (P := PP) 0 _ _ _
       (fam_node (P := PP) 1 _ _ _
        (fam_node (P := PP) 0 _ _ _
         (fam_node (P := PP) 1 _ _ _
          (fam_node (P := PP) 0 _ _ _
           (fam_node (P := PP) 1 _ _ _
            (fam_node (P := PP) 0 _ _ _
             (fam_node (P := PP) 2 _ _ _
              CKLaneG3.S.C2.B0.c_50202020204
              CKLaneG3.S.C2.B0.c_50202020205)
             CKLaneG3.S.C2.B0.c_5020202021)
            (fam_node (P := PP) 0 _ _ _
             (fam_node (P := PP) 2 _ _ _
              (fam_node (P := PP) 0 _ _ _
               CKLaneG3.S.C2.B0.c_502020203040
               (fam_node (P := PP) 2 _ _ _
                CKLaneG3.S.C2.B0.c_5020202030414
                CKLaneG3.S.C2.B0.c_5020202030415))
              CKLaneG3.S.C2.B1.c_50202020305)
             (fam_node (P := PP) 2 _ _ _
              CKLaneG3.S.C2.B1.c_50202020314
              CKLaneG3.S.C2.B1.c_50202020315)))
           CKLaneG3.S.C2.B1.c_50202021)
          (fam_node (P := PP) 0 _ _ _
           (fam_node (P := PP) 0 _ _ _
            (fam_node (P := PP) 2 _ _ _
             (fam_node (P := PP) 1 _ _ _
              (fam_node (P := PP) 0 _ _ _
               CKLaneG3.S.C2.B1.c_502020300420
               (fam_node (P := PP) 2 _ _ _
                CKLaneG3.S.C2.B1.c_5020203004214
                (fam_node (P := PP) 1 _ _ _
                 CKLaneG3.S.C2.B1.c_50202030042152
                 CKLaneG3.S.C2.B1.c_50202030042153)))
              (fam_node (P := PP) 0 _ _ _
               CKLaneG3.S.C2.B1.c_502020300430
               (fam_node (P := PP) 2 _ _ _
                CKLaneG3.S.C2.B1.c_5020203004314
                (fam_node (P := PP) 0 _ _ _
                 CKLaneG3.S.C2.B1.c_50202030043150
                 (fam_node (P := PP) 1 _ _ _
                  CKLaneG3.S.C2.B2.c_502020300431512
                  CKLaneG3.S.C2.B2.c_502020300431513)))))
             (fam_node (P := PP) 1 _ _ _
              CKLaneG3.S.C2.B2.c_50202030052
              CKLaneG3.S.C2.B2.c_50202030053))
            (fam_node (P := PP) 2 _ _ _
             (fam_node (P := PP) 1 _ _ _
              CKLaneG3.S.C2.B2.c_50202030142
              CKLaneG3.S.C2.B3.c_50202030143)
             CKLaneG3.S.C2.B3.c_5020203015))
           CKLaneG3.S.C2.B3.c_50202031))
         CKLaneG3.S.C2.B3.c_502021)
        (fam_node (P := PP) 0 _ _ _
         (fam_node (P := PP) 0 _ _ _
          (fam_node (P := PP) 0 _ _ _
           CKLaneG3.S.C2.B3.c_50203000
           (fam_node (P := PP) 2 _ _ _
            (fam_node (P := PP) 1 _ _ _
             (fam_node (P := PP) 0 _ _ _
              CKLaneG3.S.C2.B3.c_50203001420
              CKLaneG3.S.C2.B3.c_50203001421)
             (fam_node (P := PP) 0 _ _ _
              CKLaneG3.S.C2.B3.c_50203001430
              CKLaneG3.S.C2.B4.c_50203001431))
            (fam_node (P := PP) 1 _ _ _
             CKLaneG3.S.C2.B4.c_5020300152
             (fam_node (P := PP) 0 _ _ _
              CKLaneG3.S.C2.B4.c_50203001530
              CKLaneG3.S.C2.B4.c_50203001531))))
          CKLaneG3.S.C2.B4.c_5020301)
         CKLaneG3.S.C2.B4.c_502031))
       CKLaneG3.S.C2.B4.c_5021)
      (fam_node (P := PP) 0 _ _ _
       (fam_node (P := PP) 0 _ _ _
        (fam_node (P := PP) 0 _ _ _
         (fam_node (P := PP) 0 _ _ _
          CKLaneG3.S.C2.B4.c_5030000
          (fam_node (P := PP) 2 _ _ _
           CKLaneG3.S.C2.B4.c_50300014
           (fam_node (P := PP) 1 _ _ _
            (fam_node (P := PP) 0 _ _ _
             CKLaneG3.S.C2.B4.c_5030001520
             (fam_node (P := PP) 1 _ _ _
              (fam_node (P := PP) 2 _ _ _
               (fam_node (P := PP) 0 _ _ _
                (fam_node (P := PP) 1 _ _ _
                 CKLaneG3.S.C2.B5.c_50300015212402
                 CKLaneG3.S.C2.B5.c_50300015212403)
                (fam_node (P := PP) 1 _ _ _
                 CKLaneG3.S.C2.B5.c_50300015212412
                 CKLaneG3.S.C2.B5.c_50300015212413))
               CKLaneG3.S.C2.B5.c_503000152125)
              (fam_node (P := PP) 2 _ _ _
               (fam_node (P := PP) 0 _ _ _
                CKLaneG3.S.C2.B5.c_5030001521340
                (fam_node (P := PP) 1 _ _ _
                 (fam_node (P := PP) 2 _ _ _
                  CKLaneG3.S.C2.B6.c_503000152134124
                  CKLaneG3.S.C2.B6.c_503000152134125)
                 CKLaneG3.S.C2.B6.c_50300015213413))
               CKLaneG3.S.C2.B6.c_503000152135)))
            CKLaneG3.S.C2.B6.c_503000153)))
         (fam_node (P := PP) 0 _ _ _
          (fam_node (P := PP) 2 _ _ _
           (fam_node (P := PP) 1 _ _ _
            (fam_node (P := PP) 0 _ _ _
             CKLaneG3.S.C2.B6.c_5030010420
             CKLaneG3.S.C2.B6.c_5030010421)
            CKLaneG3.S.C2.B7.c_503001043)
           (fam_node (P := PP) 1 _ _ _
            (fam_node (P := PP) 0 _ _ _
             (fam_node (P := PP) 1 _ _ _
              CKLaneG3.S.C2.B7.c_50300105202
              (fam_node (P := PP) 2 _ _ _
               (fam_node (P := PP) 0 _ _ _
                (fam_node (P := PP) 1 _ _ _
                 CKLaneG3.S.C2.B7.c_50300105203402
                 CKLaneG3.S.C2.B7.c_50300105203403)
                CKLaneG3.S.C2.B7.c_5030010520341)
               CKLaneG3.S.C2.B7.c_503001052035))
             CKLaneG3.S.C2.B7.c_5030010521)
            (fam_node (P := PP) 0 _ _ _
             (fam_node (P := PP) 2 _ _ _
              (fam_node (P := PP) 1 _ _ _
               (fam_node (P := PP) 0 _ _ _
                (fam_node (P := PP) 2 _ _ _
                 CKLaneG3.S.C2.B7.c_50300105304204
                 (fam_node (P := PP) 1 _ _ _
                  CKLaneG3.S.C2.B7.c_503001053042052
                  CKLaneG3.S.C2.B8.c_503001053042053))
                (fam_node (P := PP) 2 _ _ _
                 CKLaneG3.S.C2.B8.c_50300105304214
                 CKLaneG3.S.C2.B8.c_50300105304215))
               (fam_node (P := PP) 0 _ _ _
                CKLaneG3.S.C2.B8.c_5030010530430
                (fam_node (P := PP) 2 _ _ _
                 CKLaneG3.S.C2.B8.c_50300105304314
                 (fam_node (P := PP) 1 _ _ _
                  CKLaneG3.S.C2.B8.c_503001053043152
                  (fam_node (P := PP) 0 _ _ _
                   CKLaneG3.S.C2.B9.c_5030010530431530
                   CKLaneG3.S.C2.B9.c_5030010530431531)))))
              CKLaneG3.S.C2.B9.c_50300105305)
             (fam_node (P := PP) 2 _ _ _
              (fam_node (P := PP) 1 _ _ _
               CKLaneG3.S.C2.B9.c_503001053142
               (fam_node (P := PP) 0 _ _ _
                (fam_node (P := PP) 2 _ _ _
                 CKLaneG3.S.C2.B9.c_50300105314304
                 CKLaneG3.S.C2.B9.c_50300105314305)
                CKLaneG3.S.C2.B10.c_5030010531431))
              CKLaneG3.S.C2.B10.c_50300105315))))
          (fam_node (P := PP) 2 _ _ _
           (fam_node (P := PP) 1 _ _ _
            CKLaneG3.S.C2.B10.c_503001142
            CKLaneG3.S.C2.B10.c_503001143)
           CKLaneG3.S.C2.B10.c_50300115)))
        CKLaneG3.S.C2.B10.c_50301)
       CKLaneG3.S.C2.B10.c_5031))
     CKLaneG3.S.C2.B10.c_51))

end CKLaneG3.S.Label2


