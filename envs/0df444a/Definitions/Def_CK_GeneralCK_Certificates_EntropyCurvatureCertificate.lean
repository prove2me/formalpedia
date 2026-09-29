-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureCertificate
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:12:25.022859+00:00
-- url     : https://prove2.me/theorems/3bbea014-8ddd-4135-bbdc-bcf94d361d96
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureCertificate.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves00
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves01
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves02
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves03
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves04
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves05
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves06
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves07
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves08
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves09
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves10
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves11
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves12
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves13
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves14

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem entropy_curvature_compact (v : ℝ) (hl : (1/100 : ℝ) ≤ v) (hu : v ≤ (11/24 : ℝ)) :
    0 < P v ∧ 0 < R v := by
  by_cases hm : v ≤ (3727 / 76800)
  · have hu := hm
    by_cases hm : v ≤ (1831 / 102400)
    · have hu := hm
      by_cases hm : v ≤ (8027 / 614400)
      · have hu := hm
        by_cases hm : v ≤ (18267 / 1638400)
        · have hu := hm
          by_cases hm : v ≤ (25921 / 2457600)
          · have hu := hm
            by_cases hm : v ≤ (50497 / 4915200)
            · have hu := hm
              by_cases hm : v ≤ (4969 / 491520)
              · have hu := hm
                by_cases hm : v ≤ (49421 / 4915200)
                · have hu := hm
                  exact leaf_0 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_1 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (16653 / 1638400)
                · have hu := hm
                  exact leaf_2 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (12557 / 1228800)
                  · have hu := hm
                    exact leaf_3 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_4 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (10207 / 983040)
              · have hu := hm
                by_cases hm : v ≤ (8461 / 819200)
                · have hu := hm
                  exact leaf_5 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_6 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (6413 / 614400)
                · have hu := hm
                  exact leaf_7 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (17191 / 1638400)
                  · have hu := hm
                    exact leaf_8 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_9 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (17729 / 1638400)
            · have hu := hm
              by_cases hm : v ≤ (873 / 81920)
              · have hu := hm
                by_cases hm : v ≤ (52111 / 4915200)
                · have hu := hm
                  exact leaf_10 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_11 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (52649 / 4915200)
                · have hu := hm
                  exact leaf_12 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (26459 / 2457600)
                  · have hu := hm
                    exact leaf_13 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_14 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (8999 / 819200)
              · have hu := hm
                by_cases hm : v ≤ (3341 / 307200)
                · have hu := hm
                  exact leaf_15 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (2149 / 196608)
                  · have hu := hm
                    exact leaf_16 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_17 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (54263 / 4915200)
                · have hu := hm
                  exact leaf_18 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (13633 / 1228800)
                  · have hu := hm
                    exact leaf_19 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_20 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (29149 / 2457600)
          · have hu := hm
            by_cases hm : v ≤ (28073 / 2457600)
            · have hu := hm
              by_cases hm : v ≤ (55339 / 4915200)
              · have hu := hm
                by_cases hm : v ≤ (5507 / 491520)
                · have hu := hm
                  exact leaf_21 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_22 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (2317 / 204800)
                · have hu := hm
                  exact leaf_23 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (55877 / 4915200)
                  · have hu := hm
                    exact leaf_24 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_25 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (56953 / 4915200)
              · have hu := hm
                by_cases hm : v ≤ (3761 / 327680)
                · have hu := hm
                  exact leaf_26 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (14171 / 1228800)
                  · have hu := hm
                    exact leaf_27 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_28 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (9537 / 819200)
                · have hu := hm
                  exact leaf_29 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (361 / 30720)
                  · have hu := hm
                    exact leaf_30 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_31 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (15247 / 1228800)
            · have hu := hm
              by_cases hm : v ≤ (29687 / 2457600)
              · have hu := hm
                by_cases hm : v ≤ (4903 / 409600)
                · have hu := hm
                  exact leaf_32 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_33 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (7489 / 614400)
                · have hu := hm
                  exact leaf_34 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (403 / 32768)
                  · have hu := hm
                    exact leaf_35 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_36 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (31301 / 2457600)
              · have hu := hm
                by_cases hm : v ≤ (30763 / 2457600)
                · have hu := hm
                  exact leaf_37 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1293 / 102400)
                  · have hu := hm
                    exact leaf_38 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_39 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (3157 / 245760)
                · have hu := hm
                  exact leaf_40 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (10613 / 819200)
                  · have hu := hm
                    exact leaf_41 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_42 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (19013 / 1228800)
        · have hu := hm
          by_cases hm : v ≤ (11689 / 819200)
          · have hu := hm
            by_cases hm : v ≤ (11151 / 819200)
            · have hu := hm
              by_cases hm : v ≤ (5441 / 409600)
              · have hu := hm
                by_cases hm : v ≤ (32377 / 2457600)
                · have hu := hm
                  exact leaf_43 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_44 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (6583 / 491520)
                · have hu := hm
                  exact leaf_45 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1037 / 76800)
                  · have hu := hm
                    exact leaf_46 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_47 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (571 / 40960)
              · have hu := hm
                by_cases hm : v ≤ (16861 / 1228800)
                · have hu := hm
                  exact leaf_48 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (33991 / 2457600)
                  · have hu := hm
                    exact leaf_49 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_50 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (34529 / 2457600)
                · have hu := hm
                  exact leaf_51 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (17399 / 1228800)
                  · have hu := hm
                    exact leaf_52 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_53 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (9103 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (7121 / 491520)
              · have hu := hm
                by_cases hm : v ≤ (4417 / 307200)
                · have hu := hm
                  exact leaf_54 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_55 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (5979 / 409600)
                · have hu := hm
                  exact leaf_56 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (36143 / 2457600)
                  · have hu := hm
                    exact leaf_57 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_58 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (37219 / 2457600)
              · have hu := hm
                by_cases hm : v ≤ (12227 / 819200)
                · have hu := hm
                  exact leaf_59 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (739 / 49152)
                  · have hu := hm
                    exact leaf_60 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_61 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (781 / 51200)
                · have hu := hm
                  exact leaf_62 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (37757 / 2457600)
                  · have hu := hm
                    exact leaf_63 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_64 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (8197 / 491520)
          · have hu := hm
            by_cases hm : v ≤ (39371 / 2457600)
            · have hu := hm
              by_cases hm : v ≤ (9641 / 614400)
              · have hu := hm
                by_cases hm : v ≤ (2553 / 163840)
                · have hu := hm
                  exact leaf_65 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_66 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (38833 / 2457600)
                · have hu := hm
                  exact leaf_67 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (6517 / 409600)
                  · have hu := hm
                    exact leaf_68 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_69 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (20089 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (991 / 61440)
                · have hu := hm
                  exact leaf_70 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (13303 / 819200)
                  · have hu := hm
                    exact leaf_71 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_72 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (40447 / 2457600)
                · have hu := hm
                  exact leaf_73 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (3393 / 204800)
                  · have hu := hm
                    exact leaf_74 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_75 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (1411 / 81920)
            · have hu := hm
              by_cases hm : v ≤ (13841 / 819200)
              · have hu := hm
                by_cases hm : v ≤ (20627 / 1228800)
                · have hu := hm
                  exact leaf_76 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_77 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (653 / 38400)
                · have hu := hm
                  exact leaf_78 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (42061 / 2457600)
                  · have hu := hm
                    exact leaf_79 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_80 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (14379 / 819200)
              · have hu := hm
                by_cases hm : v ≤ (42599 / 2457600)
                · have hu := hm
                  exact leaf_81 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (10717 / 614400)
                  · have hu := hm
                    exact leaf_82 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_83 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (21703 / 1228800)
                · have hu := hm
                  exact leaf_84 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1747 / 98304)
                  · have hu := hm
                    exact leaf_85 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_86 v hl hu
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : v ≤ (2113 / 76800)
      · have hu := hm
        by_cases hm : v ≤ (2789 / 122880)
        · have hu := hm
          by_cases hm : v ≤ (24931 / 1228800)
          · have hu := hm
            by_cases hm : v ≤ (23317 / 1228800)
            · have hu := hm
              by_cases hm : v ≤ (2251 / 122880)
              · have hu := hm
                by_cases hm : v ≤ (22241 / 1228800)
                · have hu := hm
                  exact leaf_87 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_88 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (7593 / 409600)
                · have hu := hm
                  exact leaf_89 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (2881 / 153600)
                  · have hu := hm
                    exact leaf_90 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_91 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (6031 / 307200)
              · have hu := hm
                by_cases hm : v ≤ (3931 / 204800)
                · have hu := hm
                  exact leaf_92 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (4771 / 245760)
                  · have hu := hm
                    exact leaf_93 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_94 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (8131 / 409600)
                · have hu := hm
                  exact leaf_95 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (12331 / 614400)
                  · have hu := hm
                    exact leaf_96 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_97 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (6569 / 307200)
            · have hu := hm
              by_cases hm : v ≤ (25469 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (21 / 1024)
                · have hu := hm
                  exact leaf_98 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_99 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (12869 / 614400)
                · have hu := hm
                  exact leaf_100 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (8669 / 409600)
                  · have hu := hm
                    exact leaf_101 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_102 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (27083 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (5309 / 245760)
                · have hu := hm
                  exact leaf_103 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (4469 / 204800)
                  · have hu := hm
                    exact leaf_104 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_105 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (3419 / 153600)
                · have hu := hm
                  exact leaf_106 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (9207 / 409600)
                  · have hu := hm
                    exact leaf_107 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_108 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (10283 / 409600)
          · have hu := hm
            by_cases hm : v ≤ (1949 / 81920)
            · have hu := hm
              by_cases hm : v ≤ (2369 / 102400)
              · have hu := hm
                by_cases hm : v ≤ (28159 / 1228800)
                · have hu := hm
                  exact leaf_109 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_110 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (28697 / 1228800)
                · have hu := hm
                  exact leaf_111 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (14483 / 614400)
                  · have hu := hm
                    exact leaf_112 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_113 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (5007 / 204800)
              · have hu := hm
                by_cases hm : v ≤ (461 / 19200)
                · have hu := hm
                  exact leaf_114 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (29773 / 1228800)
                  · have hu := hm
                    exact leaf_115 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_116 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (30311 / 1228800)
                · have hu := hm
                  exact leaf_117 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1529 / 61440)
                  · have hu := hm
                    exact leaf_118 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_119 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (16097 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (31387 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (15559 / 614400)
                · have hu := hm
                  exact leaf_120 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_121 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (1319 / 51200)
                · have hu := hm
                  exact leaf_122 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1277 / 49152)
                  · have hu := hm
                    exact leaf_123 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_124 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (33001 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (10821 / 409600)
                · have hu := hm
                  exact leaf_125 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (8183 / 307200)
                  · have hu := hm
                    exact leaf_126 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_127 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (1109 / 40960)
                · have hu := hm
                  exact leaf_128 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (33539 / 1228800)
                  · have hu := hm
                    exact leaf_129 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_130 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (22553 / 614400)
        · have hu := hm
          by_cases hm : v ≤ (9797 / 307200)
          · have hu := hm
            by_cases hm : v ≤ (899 / 30720)
            · have hu := hm
              by_cases hm : v ≤ (17173 / 614400)
              · have hu := hm
                by_cases hm : v ≤ (11359 / 409600)
                · have hu := hm
                  exact leaf_131 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_132 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (2907 / 102400)
                · have hu := hm
                  exact leaf_133 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (17711 / 614400)
                  · have hu := hm
                    exact leaf_134 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_135 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (18787 / 614400)
              · have hu := hm
                by_cases hm : v ≤ (6083 / 204800)
                · have hu := hm
                  exact leaf_136 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (9259 / 307200)
                  · have hu := hm
                    exact leaf_137 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_138 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (397 / 12800)
                · have hu := hm
                  exact leaf_139 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (773 / 24576)
                  · have hu := hm
                    exact leaf_140 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_141 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (20939 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (5033 / 153600)
              · have hu := hm
                by_cases hm : v ≤ (6621 / 204800)
                · have hu := hm
                  exact leaf_142 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_143 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (20401 / 614400)
                · have hu := hm
                  exact leaf_144 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (689 / 20480)
                  · have hu := hm
                    exact leaf_145 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_146 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (10873 / 307200)
              · have hu := hm
                by_cases hm : v ≤ (2651 / 76800)
                · have hu := hm
                  exact leaf_147 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (7159 / 204800)
                  · have hu := hm
                    exact leaf_148 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_149 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (4403 / 122880)
                · have hu := hm
                  exact leaf_150 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1857 / 51200)
                  · have hu := hm
                    exact leaf_151 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_152 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (1063 / 25600)
          · have hu := hm
            by_cases hm : v ≤ (3983 / 102400)
            · have hu := hm
              by_cases hm : v ≤ (7697 / 204800)
              · have hu := hm
                by_cases hm : v ≤ (11411 / 307200)
                · have hu := hm
                  exact leaf_153 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_154 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (73 / 1920)
                · have hu := hm
                  exact leaf_155 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (23629 / 614400)
                  · have hu := hm
                    exact leaf_156 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_157 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (1647 / 40960)
              · have hu := hm
                by_cases hm : v ≤ (24167 / 614400)
                · have hu := hm
                  exact leaf_158 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (6109 / 153600)
                  · have hu := hm
                    exact leaf_159 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_160 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (12487 / 307200)
                · have hu := hm
                  exact leaf_161 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (25243 / 614400)
                  · have hu := hm
                    exact leaf_162 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_163 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (26857 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (521 / 12288)
              · have hu := hm
                by_cases hm : v ≤ (25781 / 614400)
                · have hu := hm
                  exact leaf_164 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_165 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (8773 / 204800)
                · have hu := hm
                  exact leaf_166 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (6647 / 153600)
                  · have hu := hm
                    exact leaf_167 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_168 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (14101 / 307200)
              · have hu := hm
                by_cases hm : v ≤ (4521 / 102400)
                · have hu := hm
                  exact leaf_169 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1729 / 38400)
                  · have hu := hm
                    exact leaf_170 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_171 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (479 / 10240)
                · have hu := hm
                  exact leaf_172 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (14639 / 307200)
                  · have hu := hm
                    exact leaf_173 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_174 v hl hu
  · have hl := (lt_of_not_ge hm).le
    by_cases hm : v ≤ (6379 / 19200)
    · have hu := hm
      by_cases hm : v ≤ (3881 / 38400)
      · have hu := hm
        by_cases hm : v ≤ (20557 / 307200)
        · have hu := hm
          by_cases hm : v ≤ (2933 / 51200)
          · have hu := hm
            by_cases hm : v ≤ (16253 / 307200)
            · have hu := hm
              by_cases hm : v ≤ (7723 / 153600)
              · have hu := hm
                by_cases hm : v ≤ (5059 / 102400)
                · have hu := hm
                  exact leaf_175 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_176 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (3143 / 61440)
                · have hu := hm
                  exact leaf_177 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (333 / 6400)
                  · have hu := hm
                    exact leaf_178 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_179 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (5597 / 102400)
              · have hu := hm
                by_cases hm : v ≤ (8261 / 153600)
                · have hu := hm
                  exact leaf_180 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_181 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (853 / 15360)
                · have hu := hm
                  exact leaf_182 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (17329 / 307200)
                  · have hu := hm
                    exact leaf_183 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_184 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (18943 / 307200)
            · have hu := hm
              by_cases hm : v ≤ (2267 / 38400)
              · have hu := hm
                by_cases hm : v ≤ (17867 / 307200)
                · have hu := hm
                  exact leaf_185 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_186 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (1227 / 20480)
                · have hu := hm
                  exact leaf_187 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (9337 / 153600)
                  · have hu := hm
                    exact leaf_188 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_189 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (395 / 6144)
              · have hu := hm
                by_cases hm : v ≤ (1601 / 25600)
                · have hu := hm
                  exact leaf_190 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (19481 / 307200)
                  · have hu := hm
                    exact leaf_191 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_192 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (6673 / 102400)
                · have hu := hm
                  exact leaf_193 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (317 / 4800)
                  · have hu := hm
                    exact leaf_194 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_195 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (2513 / 30720)
          · have hu := hm
            by_cases hm : v ≤ (10951 / 153600)
            · have hu := hm
              by_cases hm : v ≤ (4219 / 61440)
              · have hu := hm
                by_cases hm : v ≤ (3471 / 51200)
                · have hu := hm
                  exact leaf_196 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_197 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (5341 / 76800)
                · have hu := hm
                  exact leaf_198 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (7211 / 102400)
                  · have hu := hm
                    exact leaf_199 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_200 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (5879 / 76800)
              · have hu := hm
                by_cases hm : v ≤ (187 / 2560)
                · have hu := hm
                  exact leaf_201 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (11489 / 153600)
                  · have hu := hm
                    exact leaf_202 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_203 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (4009 / 51200)
                · have hu := hm
                  exact leaf_204 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1537 / 19200)
                  · have hu := hm
                    exact leaf_205 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_206 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (1391 / 15360)
            · have hu := hm
              by_cases hm : v ≤ (13103 / 153600)
              · have hu := hm
                by_cases hm : v ≤ (2139 / 25600)
                · have hu := hm
                  exact leaf_207 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_208 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (3343 / 38400)
                · have hu := hm
                  exact leaf_209 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (4547 / 51200)
                  · have hu := hm
                    exact leaf_210 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_211 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (14717 / 153600)
              · have hu := hm
                by_cases hm : v ≤ (14179 / 153600)
                · have hu := hm
                  exact leaf_212 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (301 / 3200)
                  · have hu := hm
                    exact leaf_213 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_214 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (7493 / 76800)
                · have hu := hm
                  exact leaf_215 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1017 / 10240)
                  · have hu := hm
                    exact leaf_216 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_217 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (57 / 320)
        · have hu := hm
          by_cases hm : v ≤ (10183 / 76800)
          · have hu := hm
            by_cases hm : v ≤ (8569 / 76800)
            · have hu := hm
              by_cases hm : v ≤ (2677 / 25600)
              · have hu := hm
                by_cases hm : v ≤ (15793 / 153600)
                · have hu := hm
                  exact leaf_218 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_219 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (16331 / 153600)
                · have hu := hm
                  exact leaf_220 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (83 / 768)
                  · have hu := hm
                    exact leaf_221 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_222 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (293 / 2400)
              · have hu := hm
                by_cases hm : v ≤ (1473 / 12800)
                · have hu := hm
                  exact leaf_223 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (9107 / 76800)
                  · have hu := hm
                    exact leaf_224 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_225 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (643 / 5120)
                · have hu := hm
                  exact leaf_226 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (4957 / 38400)
                  · have hu := hm
                    exact leaf_227 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_228 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (1441 / 9600)
            · have hu := hm
              by_cases hm : v ≤ (10721 / 76800)
              · have hu := hm
                by_cases hm : v ≤ (871 / 6400)
                · have hu := hm
                  exact leaf_229 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_230 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (1099 / 7680)
                · have hu := hm
                  exact leaf_231 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (3753 / 25600)
                  · have hu := hm
                    exact leaf_232 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_233 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (2467 / 15360)
              · have hu := hm
                by_cases hm : v ≤ (11797 / 76800)
                · have hu := hm
                  exact leaf_234 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (2011 / 12800)
                  · have hu := hm
                    exact leaf_235 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_236 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (3151 / 19200)
                · have hu := hm
                  exact leaf_237 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (6571 / 38400)
                  · have hu := hm
                    exact leaf_238 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_239 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (9799 / 38400)
          · have hu := hm
            by_cases hm : v ≤ (1637 / 7680)
            · have hu := hm
              by_cases hm : v ≤ (3689 / 19200)
              · have hu := hm
                by_cases hm : v ≤ (7109 / 38400)
                · have hu := hm
                  exact leaf_240 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_241 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (2549 / 12800)
                · have hu := hm
                  exact leaf_242 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1979 / 9600)
                  · have hu := hm
                    exact leaf_243 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_244 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (281 / 1200)
              · have hu := hm
                by_cases hm : v ≤ (1409 / 6400)
                · have hu := hm
                  exact leaf_245 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (8723 / 38400)
                  · have hu := hm
                    exact leaf_246 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_247 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (3087 / 12800)
                · have hu := hm
                  exact leaf_248 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (953 / 3840)
                  · have hu := hm
                    exact leaf_249 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_250 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (1393 / 4800)
            · have hu := hm
              by_cases hm : v ≤ (10337 / 38400)
              · have hu := hm
                by_cases hm : v ≤ (839 / 3200)
                · have hu := hm
                  exact leaf_251 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_252 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (5303 / 19200)
                · have hu := hm
                  exact leaf_253 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (145 / 512)
                  · have hu := hm
                    exact leaf_254 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_255 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (11951 / 38400)
              · have hu := hm
                by_cases hm : v ≤ (11413 / 38400)
                · have hu := hm
                  exact leaf_256 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1947 / 6400)
                  · have hu := hm
                    exact leaf_257 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_258 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (611 / 1920)
                · have hu := hm
                  exact leaf_259 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (4163 / 12800)
                  · have hu := hm
                    exact leaf_260 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_261 v hl hu
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : v ≤ (135151 / 307200)
      · have hu := hm
        by_cases hm : v ≤ (849 / 2048)
        · have hu := hm
          by_cases hm : v ≤ (497 / 1280)
          · have hu := hm
            by_cases hm : v ≤ (4701 / 12800)
            · have hu := hm
              by_cases hm : v ≤ (277 / 800)
              · have hu := hm
                by_cases hm : v ≤ (13027 / 38400)
                · have hu := hm
                  exact leaf_262 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_263 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (2713 / 7680)
                · have hu := hm
                  exact leaf_264 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (6917 / 19200)
                  · have hu := hm
                    exact leaf_265 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_266 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (9671 / 25600)
              · have hu := hm
                by_cases hm : v ≤ (1139 / 3072)
                · have hu := hm
                  exact leaf_267 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (3593 / 9600)
                  · have hu := hm
                    exact leaf_268 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_269 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (14641 / 38400)
                · have hu := hm
                  exact leaf_270 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (29551 / 76800)
                  · have hu := hm
                    exact leaf_271 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_272 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (20687 / 51200)
            · have hu := hm
              by_cases hm : v ≤ (15179 / 38400)
              · have hu := hm
                by_cases hm : v ≤ (30089 / 76800)
                · have hu := hm
                  exact leaf_273 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_274 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (10209 / 25600)
                · have hu := hm
                  exact leaf_275 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (1931 / 4800)
                  · have hu := hm
                    exact leaf_276 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_277 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (5239 / 12800)
              · have hu := hm
                by_cases hm : v ≤ (6233 / 15360)
                · have hu := hm
                  exact leaf_278 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (62599 / 153600)
                  · have hu := hm
                    exact leaf_279 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_280 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (63137 / 153600)
                · have hu := hm
                  exact leaf_281 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (31703 / 76800)
                  · have hu := hm
                    exact leaf_282 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_283 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (1377 / 3200)
          · have hu := hm
            by_cases hm : v ≤ (3251 / 7680)
            · have hu := hm
              by_cases hm : v ≤ (64213 / 153600)
              · have hu := hm
                by_cases hm : v ≤ (7993 / 19200)
                · have hu := hm
                  exact leaf_284 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_285 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (10747 / 25600)
                · have hu := hm
                  exact leaf_286 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (64751 / 153600)
                  · have hu := hm
                    exact leaf_287 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_288 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (8759 / 20480)
              · have hu := hm
                by_cases hm : v ≤ (21763 / 51200)
                · have hu := hm
                  exact leaf_289 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (32779 / 76800)
                  · have hu := hm
                    exact leaf_290 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_291 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (65827 / 153600)
                · have hu := hm
                  exact leaf_292 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (131923 / 307200)
                  · have hu := hm
                    exact leaf_293 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_294 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (133537 / 307200)
            · have hu := hm
              by_cases hm : v ≤ (13273 / 30720)
              · have hu := hm
                by_cases hm : v ≤ (132461 / 307200)
                · have hu := hm
                  exact leaf_295 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_296 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (44333 / 102400)
                · have hu := hm
                  exact leaf_297 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (33317 / 76800)
                  · have hu := hm
                    exact leaf_298 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_299 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (16793 / 38400)
              · have hu := hm
                by_cases hm : v ≤ (22301 / 51200)
                · have hu := hm
                  exact leaf_300 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (5363 / 12288)
                  · have hu := hm
                    exact leaf_301 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_302 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (44871 / 102400)
                · have hu := hm
                  exact leaf_303 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (67441 / 153600)
                  · have hu := hm
                    exact leaf_304 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_305 v hl hu
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : v ≤ (5777 / 12800)
        · have hu := hm
          by_cases hm : v ≤ (274337 / 614400)
          · have hu := hm
            by_cases hm : v ≤ (272723 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (135689 / 307200)
              · have hu := hm
                by_cases hm : v ≤ (2257 / 5120)
                · have hu := hm
                  exact leaf_306 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_307 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (67979 / 153600)
                · have hu := hm
                  exact leaf_308 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (45409 / 102400)
                  · have hu := hm
                    exact leaf_309 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_310 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (27353 / 61440)
              · have hu := hm
                by_cases hm : v ≤ (8531 / 19200)
                · have hu := hm
                  exact leaf_311 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (91087 / 204800)
                  · have hu := hm
                    exact leaf_312 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_313 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (273799 / 614400)
                · have hu := hm
                  exact leaf_314 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (22839 / 51200)
                  · have hu := hm
                    exact leaf_315 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_316 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (45947 / 102400)
            · have hu := hm
              by_cases hm : v ≤ (3665 / 8192)
              · have hu := hm
                by_cases hm : v ≤ (137303 / 307200)
                · have hu := hm
                  exact leaf_317 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_318 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (34393 / 76800)
                · have hu := hm
                  exact leaf_319 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (275413 / 614400)
                  · have hu := hm
                    exact leaf_320 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_321 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (92163 / 204800)
              · have hu := hm
                by_cases hm : v ≤ (275951 / 614400)
                · have hu := hm
                  exact leaf_322 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (13811 / 30720)
                  · have hu := hm
                    exact leaf_323 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_324 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (138379 / 307200)
                · have hu := hm
                  exact leaf_325 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (277027 / 614400)
                  · have hu := hm
                    exact leaf_326 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_327 v hl hu
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : v ≤ (186747 / 409600)
          · have hu := hm
            by_cases hm : v ≤ (278641 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (138917 / 307200)
              · have hu := hm
                by_cases hm : v ≤ (55513 / 122880)
                · have hu := hm
                  exact leaf_328 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_329 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (92701 / 204800)
                · have hu := hm
                  exact leaf_330 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (69593 / 153600)
                  · have hu := hm
                    exact leaf_331 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_332 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (34931 / 76800)
              · have hu := hm
                by_cases hm : v ≤ (9297 / 20480)
                · have hu := hm
                  exact leaf_333 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (279179 / 614400)
                  · have hu := hm
                    exact leaf_334 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_335 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (93239 / 204800)
                · have hu := hm
                  exact leaf_336 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (139993 / 307200)
                  · have hu := hm
                    exact leaf_337 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_338 v hl hu
          · have hl := (lt_of_not_ge hm).le
            by_cases hm : v ≤ (280793 / 614400)
            · have hu := hm
              by_cases hm : v ≤ (560779 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (56051 / 122880)
                · have hu := hm
                  exact leaf_339 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  exact leaf_340 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (23377 / 51200)
                · have hu := hm
                  exact leaf_341 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (561317 / 1228800)
                  · have hu := hm
                    exact leaf_342 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_343 v hl hu
            · have hl := (lt_of_not_ge hm).le
              by_cases hm : v ≤ (562393 / 1228800)
              · have hu := hm
                by_cases hm : v ≤ (37457 / 81920)
                · have hu := hm
                  exact leaf_344 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (140531 / 307200)
                  · have hu := hm
                    exact leaf_345 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_346 v hl hu
              · have hl := (lt_of_not_ge hm).le
                by_cases hm : v ≤ (93777 / 204800)
                · have hu := hm
                  exact leaf_347 v hl hu
                · have hl := (lt_of_not_ge hm).le
                  by_cases hm : v ≤ (562931 / 1228800)
                  · have hu := hm
                    exact leaf_348 v hl hu
                  · have hl := (lt_of_not_ge hm).le
                    exact leaf_349 v hl hu

end GeneralCK.Certificates.EntropyCurvature


