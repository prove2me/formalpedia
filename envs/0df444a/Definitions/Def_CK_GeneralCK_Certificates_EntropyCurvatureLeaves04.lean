-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves04
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:58:26.954311+00:00
-- url     : https://prove2.me/theorems/03fd39e7-f9d6-43f6-a532-10ef1ca8bc2d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves04.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_96 (v : ℝ) (hl : (8131 / 409600) ≤ v) (hu : v ≤ (12331 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8131 / 409600)) (u := (12331 / 614400)) (xl := (972063909 / 500000000)) (xu := (1949723203 / 1000000000))
    (Bl := (3928803887 / 2000000000)) (Bu := (3939547913 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_96.2.1 endpoint_97.1 endpoint_96.2.2.2 endpoint_97.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_97 (v : ℝ) (hl : (12331 / 614400) ≤ v) (hu : v ≤ (24931 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (12331 / 614400)) (u := (24931 / 1228800)) (xl := (3877183803 / 2000000000)) (xu := (3888255643 / 2000000000))
    (Bl := (244886181 / 125000000)) (Bu := (1964401947 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_97.2.1 endpoint_98.1 endpoint_97.2.2.2 endpoint_98.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_98 (v : ℝ) (hl : (24931 / 1228800) ≤ v) (hu : v ≤ (21 / 1024)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (24931 / 1228800)) (u := (21 / 1024)) (xl := (3866228347 / 2000000000)) (xu := (387718381 / 200000000))
    (Bl := (1953835191 / 1000000000)) (Bu := (3918178903 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_98.2.1 endpoint_99.1 endpoint_98.2.2.2 endpoint_99.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_99 (v : ℝ) (hl : (21 / 1024) ≤ v) (hu : v ≤ (25469 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (21 / 1024)) (u := (25469 / 1228800)) (xl := (1927693397 / 1000000000)) (xu := (1933114177 / 1000000000))
    (Bl := (3897275871 / 2000000000)) (Bu := (3907670389 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_99.2.1 endpoint_100.1 endpoint_99.2.2.2 endpoint_100.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_100 (v : ℝ) (hl : (25469 / 1228800) ≤ v) (hu : v ≤ (12869 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (25469 / 1228800)) (u := (12869 / 614400)) (xl := (15378627 / 8000000)) (xu := (3855386801 / 2000000000))
    (Bl := (3886992969 / 2000000000)) (Bu := (1948637939 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_100.2.1 endpoint_101.1 endpoint_100.2.2.2 endpoint_101.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_101 (v : ℝ) (hl : (12869 / 614400) ≤ v) (hu : v ≤ (8669 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (12869 / 614400)) (u := (8669 / 409600)) (xl := (766807179 / 400000000)) (xu := (3844656757 / 2000000000))
    (Bl := (1938409679 / 1000000000)) (Bu := (242937061 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_101.2.1 endpoint_102.1 endpoint_101.2.2.2 endpoint_102.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_102 (v : ℝ) (hl : (8669 / 409600) ≤ v) (hu : v ≤ (6569 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8669 / 409600)) (u := (6569 / 307200)) (xl := (3823521981 / 2000000000)) (xu := (1917017951 / 1000000000))
    (Bl := (1933376393 / 1000000000)) (Bu := (775363873 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_102.2.1 endpoint_103.1 endpoint_102.2.2.2 endpoint_103.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_103 (v : ℝ) (hl : (6569 / 307200) ≤ v) (hu : v ≤ (5309 / 245760)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6569 / 307200)) (u := (5309 / 245760)) (xl := (3813112829 / 2000000000)) (xu := (955880497 / 500000000))
    (Bl := (964197769 / 500000000)) (Bu := (3866752793 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_103.2.1 endpoint_104.1 endpoint_103.2.2.2 endpoint_104.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_104 (v : ℝ) (hl : (5309 / 245760) ≤ v) (hu : v ≤ (4469 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5309 / 245760)) (u := (4469 / 204800)) (xl := (152112253 / 80000000)) (xu := (953278209 / 500000000))
    (Bl := (1923466057 / 1000000000)) (Bu := (3856791083 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_104.2.1 endpoint_105.1 endpoint_104.2.2.2 endpoint_105.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_105 (v : ℝ) (hl : (4469 / 204800) ≤ v) (hu : v ≤ (27083 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4469 / 204800)) (u := (27083 / 1228800)) (xl := (1896300209 / 1000000000)) (xu := (950701583 / 500000000))
    (Bl := (3837173849 / 2000000000)) (Bu := (3846932121 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_105.2.1 endpoint_106.1 endpoint_105.2.2.2 endpoint_106.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_106 (v : ℝ) (hl : (27083 / 1228800) ≤ v) (hu : v ≤ (3419 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (27083 / 1228800)) (u := (3419 / 153600)) (xl := (3782493119 / 2000000000)) (xu := (151704017 / 80000000))
    (Bl := (1913757147 / 1000000000)) (Bu := (119911683 / 62500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_106.2.1 endpoint_107.1 endpoint_106.2.2.2 endpoint_107.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_107 (v : ℝ) (hl : (3419 / 153600) ≤ v) (hu : v ≤ (9207 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3419 / 153600)) (u := (9207 / 409600)) (xl := (3772482497 / 2000000000)) (xu := (1891246563 / 1000000000))
    (Bl := (1908975757 / 1000000000)) (Bu := (3827514301 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_107.2.1 endpoint_108.1 endpoint_107.2.2.2 endpoint_108.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_108 (v : ℝ) (hl : (9207 / 409600) ≤ v) (hu : v ≤ (2789 / 122880)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9207 / 409600)) (u := (2789 / 122880)) (xl := (940641669 / 500000000)) (xu := (471560313 / 250000000))
    (Bl := (3808483637 / 2000000000)) (Bu := (3817951521 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_108.2.1 endpoint_109.1 endpoint_108.2.2.2 endpoint_109.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_109 (v : ℝ) (hl : (2789 / 122880) ≤ v) (hu : v ≤ (28159 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2789 / 122880)) (u := (28159 / 1228800)) (xl := (3752743837 / 2000000000)) (xu := (3762566683 / 2000000000))
    (Bl := (1899554421 / 1000000000)) (Bu := (952120911 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_109.2.1 endpoint_110.1 endpoint_109.2.2.2 endpoint_110.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_110 (v : ℝ) (hl : (28159 / 1228800) ≤ v) (hu : v ≤ (2369 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (28159 / 1228800)) (u := (2369 / 102400)) (xl := (3743012209 / 2000000000)) (xu := (938185961 / 500000000))
    (Bl := (1894912679 / 1000000000)) (Bu := (3799108849 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_110.2.1 endpoint_111.1 endpoint_110.2.2.2 endpoint_111.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_111 (v : ℝ) (hl : (2369 / 102400) ≤ v) (hu : v ≤ (28697 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2369 / 102400)) (u := (28697 / 1228800)) (xl := (1866685037 / 1000000000)) (xu := (467876527 / 250000000))
    (Bl := (3780631467 / 2000000000)) (Bu := (757965073 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_111.2.1 endpoint_112.1 endpoint_111.2.2.2 endpoint_112.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_112 (v : ℝ) (hl : (28697 / 1228800) ≤ v) (hu : v ≤ (14483 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (28697 / 1228800)) (u := (14483 / 614400)) (xl := (3723815761 / 2000000000)) (xu := (3733370081 / 2000000000))
    (Bl := (7543051 / 4000000)) (Bu := (1890315737 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_112.2.1 endpoint_113.1 endpoint_112.2.2.2 endpoint_113.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_113 (v : ℝ) (hl : (14483 / 614400) ≤ v) (hu : v ≤ (1949 / 81920)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14483 / 614400)) (u := (1949 / 81920)) (xl := (928586911 / 500000000)) (xu := (465476971 / 250000000))
    (Bl := (3762505829 / 2000000000)) (Bu := (3771525507 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_113.2.1 endpoint_114.1 endpoint_113.2.2.2 endpoint_114.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_114 (v : ℝ) (hl : (1949 / 81920) ≤ v) (hu : v ≤ (461 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1949 / 81920)) (u := (461 / 19200)) (xl := (1852482073 / 1000000000)) (xu := (3714347651 / 2000000000))
    (Bl := (3753570877 / 2000000000)) (Bu := (940626459 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_114.2.1 endpoint_115.1 endpoint_114.2.2.2 endpoint_115.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_115 (v : ℝ) (hl : (461 / 19200) ≤ v) (hu : v ≤ (29773 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (461 / 19200)) (u := (29773 / 1228800)) (xl := (230978983 / 125000000)) (xu := (3704964153 / 2000000000))
    (Bl := (748943821 / 400000000)) (Bu := (938392721 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_115.2.1 endpoint_116.1 endpoint_115.2.2.2 endpoint_116.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_116 (v : ℝ) (hl : (29773 / 1228800) ≤ v) (hu : v ≤ (5007 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (29773 / 1228800)) (u := (5007 / 204800)) (xl := (1843222447 / 1000000000)) (xu := (739132747 / 400000000))
    (Bl := (3735949019 / 2000000000)) (Bu := (468089889 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_116.2.1 endpoint_117.1 endpoint_116.2.2.2 endpoint_117.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_117 (v : ℝ) (hl : (5007 / 204800) ≤ v) (hu : v ≤ (30311 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5007 / 204800)) (u := (30311 / 1228800)) (xl := (3677306189 / 2000000000)) (xu := (3686444901 / 2000000000))
    (Bl := (1863629581 / 1000000000)) (Bu := (1867974513 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_117.2.1 endpoint_118.1 endpoint_117.2.2.2 endpoint_118.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_118 (v : ℝ) (hl : (30311 / 1228800) ≤ v) (hu : v ≤ (1529 / 61440)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (30311 / 1228800)) (u := (1529 / 61440)) (xl := (3668246197 / 2000000000)) (xu := (919326549 / 500000000))
    (Bl := (92966203 / 50000000)) (Bu := (3727259169 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_118.2.1 endpoint_119.1 endpoint_118.2.2.2 endpoint_119.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_119 (v : ℝ) (hl : (1529 / 61440) ≤ v) (hu : v ≤ (10283 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1529 / 61440)) (u := (10283 / 409600)) (xl := (3659263537 / 2000000000)) (xu := (917061551 / 500000000))
    (Bl := (371011451 / 200000000)) (Bu := (3718648127 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_119.2.1 endpoint_120.1 endpoint_119.2.2.2 endpoint_120.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


