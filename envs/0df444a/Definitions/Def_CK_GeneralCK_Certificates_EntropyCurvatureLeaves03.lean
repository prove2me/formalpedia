-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves03
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:13.822644+00:00
-- url     : https://prove2.me/theorems/0b0530c2-e1d4-48f2-93f0-b32f193ff65c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves03` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves03` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves03` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves03 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves03.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_72 (v : ℝ) (hl : (13303 / 819200) ≤ v) (hu : v ≤ (20089 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13303 / 819200)) (u := (20089 / 1228800)) (xl := (4097137377 / 2000000000)) (xu := (1025991593 / 500000000))
    (Bl := (2065052269 / 1000000000)) (Bu := (827342199 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_72.2.1 endpoint_73.1 endpoint_72.2.2.2 endpoint_73.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_73 (v : ℝ) (hl : (20089 / 1228800) ≤ v) (hu : v ≤ (40447 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (20089 / 1228800)) (u := (40447 / 2457600)) (xl := (2045176601 / 1000000000)) (xu := (512142173 / 250000000))
    (Bl := (4123542927 / 2000000000)) (Bu := (826020909 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_73.2.1 endpoint_74.1 endpoint_73.2.2.2 endpoint_74.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_74 (v : ℝ) (hl : (40447 / 2457600) ≤ v) (hu : v ≤ (3393 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (40447 / 2457600)) (u := (3393 / 204800)) (xl := (4083613247 / 2000000000)) (xu := (4090353209 / 2000000000))
    (Bl := (102925639 / 50000000)) (Bu := (2061771467 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_74.2.1 endpoint_75.1 endpoint_74.2.2.2 endpoint_75.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_75 (v : ℝ) (hl : (3393 / 204800) ≤ v) (hu : v ≤ (8197 / 491520)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3393 / 204800)) (u := (8197 / 491520)) (xl := (407691693 / 200000000)) (xu := (2041806627 / 1000000000))
    (Bl := (4110551857 / 2000000000)) (Bu := (4117025567 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_75.2.1 endpoint_76.1 endpoint_75.2.2.2 endpoint_76.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_76 (v : ℝ) (hl : (8197 / 491520) ≤ v) (hu : v ≤ (20627 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8197 / 491520)) (u := (20627 / 1228800)) (xl := (4070263679 / 2000000000)) (xu := (4076916937 / 2000000000))
    (Bl := (1026030311 / 500000000)) (Bu := (513818983 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_76.2.1 endpoint_77.1 endpoint_76.2.2.2 endpoint_77.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_77 (v : ℝ) (hl : (20627 / 1228800) ≤ v) (hu : v ≤ (13841 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (20627 / 1228800)) (u := (13841 / 819200)) (xl := (812730587 / 400000000)) (xu := (2035131843 / 1000000000))
    (Bl := (2048866581 / 1000000000)) (Bu := (4104121251 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_77.2.1 endpoint_78.1 endpoint_77.2.2.2 endpoint_78.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_78 (v : ℝ) (hl : (13841 / 819200) ≤ v) (hu : v ≤ (653 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13841 / 819200)) (u := (653 / 38400)) (xl := (1014271037 / 500000000)) (xu := (2031826471 / 1000000000))
    (Bl := (4091387063 / 2000000000)) (Bu := (4097733169 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_78.2.1 endpoint_79.1 endpoint_78.2.2.2 endpoint_79.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_79 (v : ℝ) (hl : (653 / 38400) ≤ v) (hu : v ≤ (42061 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (653 / 38400)) (u := (42061 / 2457600)) (xl := (202527839 / 100000000)) (xu := (811416831 / 400000000))
    (Bl := (4085082407 / 2000000000)) (Bu := (409138707 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_79.2.1 endpoint_80.1 endpoint_79.2.2.2 endpoint_80.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_80 (v : ℝ) (hl : (42061 / 2457600) ≤ v) (hu : v ≤ (1411 / 81920)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (42061 / 2457600)) (u := (1411 / 81920)) (xl := (4044070303 / 2000000000)) (xu := (4050556787 / 2000000000))
    (Bl := (2039409333 / 1000000000)) (Bu := (2042541207 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_80.2.1 endpoint_81.1 endpoint_80.2.2.2 endpoint_81.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_81 (v : ℝ) (hl : (1411 / 81920) ≤ v) (hu : v ≤ (42599 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1411 / 81920)) (u := (42599 / 2457600)) (xl := (2018812099 / 1000000000)) (xu := (404407031 / 200000000))
    (Bl := (4072595323 / 2000000000)) (Bu := (4078818673 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_81.2.1 endpoint_82.1 endpoint_81.2.2.2 endpoint_82.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_82 (v : ℝ) (hl : (42599 / 2457600) ≤ v) (hu : v ≤ (10717 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (42599 / 2457600)) (u := (10717 / 614400)) (xl := (1007804489 / 500000000)) (xu := (807524841 / 400000000))
    (Bl := (4066411869 / 2000000000)) (Bu := (407259533 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_82.2.1 endpoint_83.1 endpoint_82.2.2.2 endpoint_83.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_83 (v : ℝ) (hl : (10717 / 614400) ≤ v) (hu : v ≤ (14379 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10717 / 614400)) (u := (14379 / 819200)) (xl := (100621277 / 50000000)) (xu := (4031217963 / 2000000000))
    (Bl := (4060267803 / 2000000000)) (Bu := (1016602969 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_83.2.1 endpoint_84.1 endpoint_83.2.2.2 endpoint_84.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_84 (v : ℝ) (hl : (14379 / 819200) ≤ v) (hu : v ≤ (21703 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14379 / 819200)) (u := (21703 / 1228800)) (xl := (4018523079 / 2000000000)) (xu := (4024851087 / 2000000000))
    (Bl := (2027081319 / 1000000000)) (Bu := (406026781 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_84.2.1 endpoint_85.1 endpoint_84.2.2.2 endpoint_85.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_85 (v : ℝ) (hl : (21703 / 1228800) ≤ v) (hu : v ≤ (1747 / 98304)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (21703 / 1228800)) (u := (1747 / 98304)) (xl := (4012233473 / 2000000000)) (xu := (2009261543 / 1000000000))
    (Bl := (2024047947 / 1000000000)) (Bu := (810832529 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_85.2.1 endpoint_86.1 endpoint_85.2.2.2 endpoint_86.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_86 (v : ℝ) (hl : (1747 / 98304) ≤ v) (hu : v ≤ (1831 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1747 / 98304)) (u := (1831 / 102400)) (xl := (400598179 / 200000000)) (xu := (100305837 / 50000000))
    (Bl := (4042067097 / 2000000000)) (Bu := (4048095901 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_86.2.1 endpoint_87.1 endpoint_86.2.2.2 endpoint_87.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_87 (v : ℝ) (hl : (1831 / 102400) ≤ v) (hu : v ≤ (22241 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1831 / 102400)) (u := (22241 / 1228800)) (xl := (79871807 / 40000000)) (xu := (4005981797 / 2000000000))
    (Bl := (4030121503 / 2000000000)) (Bu := (126314597 / 62500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_87.2.1 endpoint_88.1 endpoint_87.2.2.2 endpoint_88.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_88 (v : ℝ) (hl : (22241 / 1228800) ≤ v) (hu : v ≤ (2251 / 122880)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (22241 / 1228800)) (u := (2251 / 122880)) (xl := (1990672577 / 1000000000)) (xu := (3993590357 / 2000000000))
    (Bl := (4018322253 / 2000000000)) (Bu := (403012151 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_88.2.1 endpoint_89.1 endpoint_88.2.2.2 endpoint_89.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_89 (v : ℝ) (hl : (2251 / 122880) ≤ v) (hu : v ≤ (7593 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2251 / 122880)) (u := (7593 / 409600)) (xl := (3969242727 / 2000000000)) (xu := (3981345161 / 2000000000))
    (Bl := (250416617 / 125000000)) (Bu := (200916113 / 100000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_89.2.1 endpoint_90.1 endpoint_89.2.2.2 endpoint_90.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_90 (v : ℝ) (hl : (7593 / 409600) ≤ v) (hu : v ≤ (2881 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7593 / 409600)) (u := (2881 / 153600)) (xl := (989319929 / 500000000)) (xu := (1984621367 / 1000000000))
    (Bl := (799029801 / 400000000)) (Bu := (4006665879 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_90.2.1 endpoint_91.1 endpoint_90.2.2.2 endpoint_91.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_91 (v : ℝ) (hl : (2881 / 153600) ≤ v) (hu : v ≤ (23317 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2881 / 153600)) (u := (23317 / 1228800)) (xl := (986363221 / 500000000)) (xu := (3957279723 / 2000000000))
    (Bl := (3983768417 / 2000000000)) (Bu := (998787253 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_91.2.1 endpoint_92.1 endpoint_91.2.2.2 endpoint_92.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_92 (v : ℝ) (hl : (23317 / 1228800) ≤ v) (hu : v ≤ (3931 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (23317 / 1228800)) (u := (3931 / 204800)) (xl := (30732493 / 15625000)) (xu := (3945452891 / 2000000000))
    (Bl := (3972520981 / 2000000000)) (Bu := (497971053 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_92.2.1 endpoint_93.1 endpoint_92.2.2.2 endpoint_93.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_93 (v : ℝ) (hl : (3931 / 204800) ≤ v) (hu : v ≤ (4771 / 245760)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3931 / 204800)) (u := (4771 / 245760)) (xl := (3922195359 / 2000000000)) (xu := (3933759111 / 2000000000))
    (Bl := (24758773 / 12500000)) (Bu := (993130247 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_93.2.1 endpoint_94.1 endpoint_93.2.2.2 endpoint_94.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_94 (v : ℝ) (hl : (4771 / 245760) ≤ v) (hu : v ≤ (6031 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4771 / 245760)) (u := (6031 / 307200)) (xl := (3910758731 / 2000000000)) (xu := (1961097683 / 1000000000))
    (Bl := (987603399 / 500000000)) (Bu := (3961403687 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_94.2.1 endpoint_95.1 endpoint_94.2.2.2 endpoint_95.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_95 (v : ℝ) (hl : (6031 / 307200) ≤ v) (hu : v ≤ (8131 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6031 / 307200)) (u := (8131 / 409600)) (xl := (3899446399 / 2000000000)) (xu := (1955379369 / 1000000000))
    (Bl := (1969773953 / 1000000000)) (Bu := (3950413603 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_95.2.1 endpoint_96.1 endpoint_95.2.2.2 endpoint_96.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


