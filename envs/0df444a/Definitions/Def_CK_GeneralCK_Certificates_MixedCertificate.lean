-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedCertificate
-- name    : CK_GeneralCK_Certificates_MixedCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:34:23.741899+00:00
-- url     : https://prove2.me/theorems/6d0821ac-4489-46cf-abf4-cfa286029b75
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves00
import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves01
import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves02
import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves03
import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves04
import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves05
import Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves06

namespace GeneralCK.Certificates.Mixed

/-- The retained 105 closed rational intervals cover the compact domain. -/
theorem mixed_compact (v : ℝ) (hl : (1/22 : ℝ) ≤ v) (hu : v ≤ (1/3 : ℝ)) :
    profile v ≤ 13/6 := by
  by_cases hm : v ≤ (343 / 2112)
  · have hu := hm
    by_cases hm : v ≤ (439 / 4224)
    · have hu := hm
      by_cases hm : v ≤ (631 / 8448)
      · have hu := hm
        by_cases hm : v ≤ (83 / 1408)
        · have hu := hm
          by_cases hm : v ≤ (147 / 2816)
          · have hu := hm
            by_cases hm : v ≤ (403 / 8448)
            · have hu := hm
              exact leaf_0 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (211 / 4224)
              · have hu := hm
                exact leaf_1 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_2 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (115 / 2112)
            · have hu := hm
              exact leaf_3 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (479 / 8448)
              · have hu := hm
                exact leaf_4 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_5 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (185 / 2816)
          · have hu := hm
            by_cases hm : v ≤ (47 / 768)
            · have hu := hm
              exact leaf_6 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (67 / 1056)
              · have hu := hm
                exact leaf_7 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_8 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (593 / 8448)
            · have hu := hm
              by_cases hm : v ≤ (287 / 4224)
              · have hu := hm
                exact leaf_9 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_10 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (51 / 704)
              · have hu := hm
                exact leaf_11 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_12 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (745 / 8448)
        · have hu := hm
          by_cases hm : v ≤ (43 / 528)
          · have hu := hm
            by_cases hm : v ≤ (325 / 4224)
            · have hu := hm
              exact leaf_13 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (223 / 2816)
              · have hu := hm
                exact leaf_14 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_15 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (707 / 8448)
            · have hu := hm
              exact leaf_16 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (11 / 128)
              · have hu := hm
                exact leaf_17 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_18 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (401 / 4224)
          · have hu := hm
            by_cases hm : v ≤ (191 / 2112)
            · have hu := hm
              exact leaf_19 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (261 / 2816)
              · have hu := hm
                exact leaf_20 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_21 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (35 / 352)
            · have hu := hm
              by_cases hm : v ≤ (821 / 8448)
              · have hu := hm
                exact leaf_22 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_23 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (859 / 8448)
              · have hu := hm
                exact leaf_24 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_25 v hl hu
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : v ≤ (375 / 2816)
      · have hu := hm
        by_cases hm : v ≤ (31 / 264)
        · have hu := hm
          by_cases hm : v ≤ (85 / 768)
          · have hu := hm
            by_cases hm : v ≤ (299 / 2816)
            · have hu := hm
              exact leaf_26 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (229 / 2112)
              · have hu := hm
                exact leaf_27 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_28 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (159 / 1408)
            · have hu := hm
              exact leaf_29 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (973 / 8448)
              · have hu := hm
                exact leaf_30 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_31 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (1049 / 8448)
          · have hu := hm
            by_cases hm : v ≤ (337 / 2816)
            · have hu := hm
              exact leaf_32 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (515 / 4224)
              · have hu := hm
                exact leaf_33 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_34 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (1087 / 8448)
            · have hu := hm
              by_cases hm : v ≤ (89 / 704)
              · have hu := hm
                exact leaf_35 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_36 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (553 / 4224)
              · have hu := hm
                exact leaf_37 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_38 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (413 / 2816)
        · have hu := hm
          by_cases hm : v ≤ (197 / 1408)
          · have hu := hm
            by_cases hm : v ≤ (13 / 96)
            · have hu := hm
              exact leaf_39 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1163 / 8448)
              · have hu := hm
                exact leaf_40 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_41 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (1201 / 8448)
            · have hu := hm
              exact leaf_42 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (305 / 2112)
              · have hu := hm
                exact leaf_43 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_44 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (27 / 176)
          · have hu := hm
            by_cases hm : v ≤ (629 / 4224)
            · have hu := hm
              exact leaf_45 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1277 / 8448)
              · have hu := hm
                exact leaf_46 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_47 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (667 / 4224)
            · have hu := hm
              by_cases hm : v ≤ (1315 / 8448)
              · have hu := hm
                exact leaf_48 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_49 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (41 / 256)
              · have hu := hm
                exact leaf_50 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_51 v hl hu
  · have hl := (lt_of_not_ge hm).le
    by_cases hm : v ≤ (311 / 1408)
    · have hu := hm
      by_cases hm : v ≤ (1619 / 8448)
      · have hu := hm
        by_cases hm : v ≤ (743 / 4224)
        · have hu := hm
          by_cases hm : v ≤ (1429 / 8448)
          · have hu := hm
            by_cases hm : v ≤ (1391 / 8448)
            · have hu := hm
              exact leaf_52 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (235 / 1408)
              · have hu := hm
                exact leaf_53 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_54 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (181 / 1056)
            · have hu := hm
              exact leaf_55 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (489 / 2816)
              · have hu := hm
                exact leaf_56 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_57 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (1543 / 8448)
          · have hu := hm
            by_cases hm : v ≤ (1505 / 8448)
            · have hu := hm
              exact leaf_58 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (127 / 704)
              · have hu := hm
                exact leaf_59 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_60 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (527 / 2816)
            · have hu := hm
              by_cases hm : v ≤ (71 / 384)
              · have hu := hm
                exact leaf_61 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_62 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (25 / 132)
              · have hu := hm
                exact leaf_63 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_64 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (1733 / 8448)
        · have hu := hm
          by_cases hm : v ≤ (419 / 2112)
          · have hu := hm
            by_cases hm : v ≤ (273 / 1408)
            · have hu := hm
              exact leaf_65 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1657 / 8448)
              · have hu := hm
                exact leaf_66 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_67 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (565 / 2816)
            · have hu := hm
              exact leaf_68 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (857 / 4224)
              · have hu := hm
                exact leaf_69 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_70 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (895 / 4224)
          · have hu := hm
            by_cases hm : v ≤ (73 / 352)
            · have hu := hm
              exact leaf_71 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (161 / 768)
              · have hu := hm
                exact leaf_72 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_73 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (457 / 2112)
            · have hu := hm
              by_cases hm : v ≤ (603 / 2816)
              · have hu := hm
                exact leaf_74 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_75 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1847 / 8448)
              · have hu := hm
                exact leaf_76 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_77 v hl hu
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : v ≤ (533 / 2112)
      · have hu := hm
        by_cases hm : v ≤ (15 / 64)
        · have hu := hm
          by_cases hm : v ≤ (641 / 2816)
          · have hu := hm
            by_cases hm : v ≤ (1885 / 8448)
            · have hu := hm
              exact leaf_78 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (119 / 528)
              · have hu := hm
                exact leaf_79 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_80 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (971 / 4224)
            · have hu := hm
              exact leaf_81 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1961 / 8448)
              · have hu := hm
                exact leaf_82 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_83 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (679 / 2816)
          · have hu := hm
            by_cases hm : v ≤ (1999 / 8448)
            · have hu := hm
              exact leaf_84 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1009 / 4224)
              · have hu := hm
                exact leaf_85 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_86 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (2075 / 8448)
            · have hu := hm
              by_cases hm : v ≤ (257 / 1056)
              · have hu := hm
                exact leaf_87 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_88 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (349 / 1408)
              · have hu := hm
                exact leaf_89 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_90 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (109 / 384)
        · have hu := hm
          by_cases hm : v ≤ (1123 / 4224)
          · have hu := hm
            by_cases hm : v ≤ (1085 / 4224)
            · have hu := hm
              exact leaf_91 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (23 / 88)
              · have hu := hm
                exact leaf_92 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_93 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (387 / 1408)
            · have hu := hm
              by_cases hm : v ≤ (571 / 2112)
              · have hu := hm
                exact leaf_94 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_95 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (295 / 1056)
              · have hu := hm
                exact leaf_96 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_97 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (157 / 528)
          · have hu := hm
            by_cases hm : v ≤ (203 / 704)
            · have hu := hm
              exact leaf_98 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1237 / 4224)
              · have hu := hm
                exact leaf_99 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_100 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (111 / 352)
            · have hu := hm
              by_cases hm : v ≤ (647 / 2112)
              · have hu := hm
                exact leaf_101 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_102 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (685 / 2112)
              · have hu := hm
                exact leaf_103 v hl hu
              · have hl := (lt_of_not_ge hm).le
                exact leaf_104 v hl hu

end GeneralCK.Certificates.Mixed


