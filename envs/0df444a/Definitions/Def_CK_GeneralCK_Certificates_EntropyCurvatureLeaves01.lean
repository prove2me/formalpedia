-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves01
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:32.132685+00:00
-- url     : https://prove2.me/theorems/422c489c-cbe2-4729-9708-d1e423a309ce
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves01` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves01` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves01` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves01 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves01.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_24 (v : ℝ) (hl : (2317 / 204800) ≤ v) (hu : v ≤ (55877 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2317 / 204800)) (u := (55877 / 4915200)) (xl := (1116375389 / 500000000)) (xu := (4470382691 / 2000000000))
    (Bl := (4488368189 / 2000000000)) (Bu := (1123284653 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_24.2.1 endpoint_25.1 endpoint_24.2.2.2 endpoint_25.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_25 (v : ℝ) (hl : (55877 / 4915200) ≤ v) (hu : v ≤ (28073 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (55877 / 4915200)) (u := (28073 / 2457600)) (xl := (4460643603 / 2000000000)) (xu := (1116375391 / 500000000))
    (Bl := (2241810477 / 1000000000)) (Bu := (4488368197 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_25.2.1 endpoint_26.1 endpoint_25.2.2.2 endpoint_26.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_26 (v : ℝ) (hl : (28073 / 2457600) ≤ v) (hu : v ≤ (3761 / 327680)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (28073 / 2457600)) (u := (3761 / 327680)) (xl := (4455808601 / 2000000000)) (xu := (4460643611 / 2000000000))
    (Bl := (1119724169 / 500000000)) (Bu := (2241810481 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_26.2.1 endpoint_27.1 endpoint_26.2.2.2 endpoint_27.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_27 (v : ℝ) (hl : (3761 / 327680) ≤ v) (hu : v ≤ (14171 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3761 / 327680)) (u := (14171 / 1228800)) (xl := (1112749083 / 500000000)) (xu := (4455808609 / 2000000000))
    (Bl := (4474195139 / 2000000000)) (Bu := (1119724171 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_27.2.1 endpoint_28.1 endpoint_27.2.2.2 endpoint_28.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_28 (v : ℝ) (hl : (14171 / 1228800) ≤ v) (hu : v ≤ (56953 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14171 / 1228800)) (u := (56953 / 4915200)) (xl := (4446206581 / 2000000000)) (xu := (222549817 / 100000000))
    (Bl := (1117379031 / 500000000)) (Bu := (4474195147 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_28.2.1 endpoint_29.1 endpoint_28.2.2.2 endpoint_29.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_29 (v : ℝ) (hl : (56953 / 4915200) ≤ v) (hu : v ≤ (9537 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (56953 / 4915200)) (u := (9537 / 819200)) (xl := (4441439137 / 2000000000)) (xu := (4446206589 / 2000000000))
    (Bl := (2232429711 / 1000000000)) (Bu := (1117379033 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_29.2.1 endpoint_30.1 endpoint_29.2.2.2 endpoint_30.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_30 (v : ℝ) (hl : (9537 / 819200) ≤ v) (hu : v ≤ (361 / 30720)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9537 / 819200)) (u := (361 / 30720)) (xl := (443197033 / 200000000)) (xu := (888287829 / 400000000))
    (Bl := (4455612119 / 2000000000)) (Bu := (446485943 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_30.2.1 endpoint_31.1 endpoint_30.2.2.2 endpoint_31.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_31 (v : ℝ) (hl : (361 / 30720) ≤ v) (hu : v ≤ (29149 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (361 / 30720)) (u := (29149 / 2457600)) (xl := (4422588273 / 2000000000)) (xu := (2215985169 / 1000000000))
    (Bl := (444645159 / 200000000)) (Bu := (4455612127 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_31.2.1 endpoint_32.1 endpoint_31.2.2.2 endpoint_32.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_32 (v : ℝ) (hl : (29149 / 2457600) ≤ v) (hu : v ≤ (4903 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (29149 / 2457600)) (u := (4903 / 409600)) (xl := (1103322843 / 500000000)) (xu := (4422588281 / 2000000000))
    (Bl := (4437376241 / 2000000000)) (Bu := (2223225799 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_32.2.1 endpoint_33.1 endpoint_32.2.2.2 endpoint_33.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_33 (v : ℝ) (hl : (4903 / 409600) ≤ v) (hu : v ≤ (29687 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4903 / 409600)) (u := (29687 / 2457600)) (xl := (1101019519 / 500000000)) (xu := (220664569 / 100000000))
    (Bl := (4428384523 / 2000000000)) (Bu := (4437376249 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_33.2.1 endpoint_34.1 endpoint_33.2.2.2 endpoint_34.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_34 (v : ℝ) (hl : (29687 / 2457600) ≤ v) (hu : v ≤ (7489 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (29687 / 2457600)) (u := (7489 / 614400)) (xl := (1098736719 / 500000000)) (xu := (1101019521 / 500000000))
    (Bl := (176778997 / 80000000)) (Bu := (4428384531 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_34.2.1 endpoint_35.1 endpoint_34.2.2.2 endpoint_35.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_35 (v : ℝ) (hl : (7489 / 614400) ≤ v) (hu : v ≤ (403 / 32768)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7489 / 614400)) (u := (403 / 32768)) (xl := (877179261 / 400000000)) (xu := (1098736721 / 500000000))
    (Bl := (220532299 / 100000000)) (Bu := (4419474933 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_35.2.1 endpoint_36.1 endpoint_35.2.2.2 endpoint_36.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_36 (v : ℝ) (hl : (403 / 32768) ≤ v) (hu : v ≤ (15247 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (403 / 32768)) (u := (15247 / 1228800)) (xl := (4376924933 / 2000000000)) (xu := (4385896313 / 2000000000))
    (Bl := (2200948129 / 1000000000)) (Bu := (1102661497 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_36.2.1 endpoint_37.1 endpoint_36.2.2.2 endpoint_37.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_37 (v : ℝ) (hl : (15247 / 1228800) ≤ v) (hu : v ≤ (30763 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (15247 / 1228800)) (u := (30763 / 2457600)) (xl := (4368031369 / 2000000000)) (xu := (4376924941 / 2000000000))
    (Bl := (439322437 / 200000000)) (Bu := (2200948133 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_37.2.1 endpoint_38.1 endpoint_37.2.2.2 endpoint_38.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_38 (v : ℝ) (hl : (30763 / 2457600) ≤ v) (hu : v ≤ (1293 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (30763 / 2457600)) (u := (1293 / 102400)) (xl := (2179607129 / 1000000000)) (xu := (4368031377 / 2000000000))
    (Bl := (4384628959 / 2000000000)) (Bu := (2196612189 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_38.2.1 endpoint_39.1 endpoint_38.2.2.2 endpoint_39.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_39 (v : ℝ) (hl : (1293 / 102400) ≤ v) (hu : v ≤ (31301 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1293 / 102400)) (u := (31301 / 2457600)) (xl := (108761807 / 50000000)) (xu := (2179607133 / 1000000000))
    (Bl := (875221741 / 400000000)) (Bu := (4384628967 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_39.2.1 endpoint_40.1 endpoint_39.2.2.2 endpoint_40.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_40 (v : ℝ) (hl : (31301 / 2457600) ≤ v) (hu : v ≤ (3157 / 245760)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (31301 / 2457600)) (u := (3157 / 245760)) (xl := (4341804149 / 2000000000)) (xu := (135952259 / 62500000))
    (Bl := (1091915581 / 500000000)) (Bu := (4376108713 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_40.2.1 endpoint_41.1 endpoint_40.2.2.2 endpoint_41.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_41 (v : ℝ) (hl : (3157 / 245760) ≤ v) (hu : v ≤ (10613 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3157 / 245760)) (u := (10613 / 819200)) (xl := (4333208611 / 2000000000)) (xu := (4341804157 / 2000000000))
    (Bl := (54491107 / 25000000)) (Bu := (1091915583 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_41.2.1 endpoint_42.1 endpoint_41.2.2.2 endpoint_42.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_42 (v : ℝ) (hl : (10613 / 819200) ≤ v) (hu : v ≤ (8027 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10613 / 819200)) (u := (8027 / 614400)) (xl := (864936889 / 400000000)) (xu := (4333208619 / 2000000000))
    (Bl := (271936637 / 125000000)) (Bu := (544911071 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_42.2.1 endpoint_43.1 endpoint_42.2.2.2 endpoint_43.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_43 (v : ℝ) (hl : (8027 / 614400) ≤ v) (hu : v ≤ (32377 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8027 / 614400)) (u := (32377 / 2457600)) (xl := (4316230459 / 2000000000)) (xu := (4324684453 / 2000000000))
    (Bl := (434275403 / 200000000)) (Bu := (21754931 / 10000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_43.2.1 endpoint_44.1 endpoint_43.2.2.2 endpoint_44.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_44 (v : ℝ) (hl : (32377 / 2457600) ≤ v) (hu : v ≤ (5441 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (32377 / 2457600)) (u := (5441 / 409600)) (xl := (4307845493 / 2000000000)) (xu := (4316230467 / 2000000000))
    (Bl := (433459091 / 200000000)) (Bu := (2171377019 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_44.2.1 endpoint_45.1 endpoint_44.2.2.2 endpoint_45.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_45 (v : ℝ) (hl : (5441 / 409600) ≤ v) (hu : v ≤ (6583 / 491520)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5441 / 409600)) (u := (6583 / 491520)) (xl := (4299528413 / 2000000000)) (xu := (4307845501 / 2000000000))
    (Bl := (2163247851 / 1000000000)) (Bu := (2167295459 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_45.2.1 endpoint_46.1 endpoint_45.2.2.2 endpoint_46.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_46 (v : ℝ) (hl : (6583 / 491520) ≤ v) (hu : v ≤ (1037 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6583 / 491520)) (u := (1037 / 76800)) (xl := (4291278113 / 2000000000)) (xu := (4299528421 / 2000000000))
    (Bl := (43184673 / 20000000)) (Bu := (432649571 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_46.2.1 endpoint_47.1 endpoint_46.2.2.2 endpoint_47.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_47 (v : ℝ) (hl : (1037 / 76800) ≤ v) (hu : v ≤ (11151 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1037 / 76800)) (u := (11151 / 819200)) (xl := (856618703 / 400000000)) (xu := (4291278121 / 2000000000))
    (Bl := (269406539 / 125000000)) (Bu := (1079616827 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_47.2.1 endpoint_48.1 endpoint_47.2.2.2 endpoint_48.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


