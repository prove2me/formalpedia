-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves13
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:38.281134+00:00
-- url     : https://prove2.me/theorems/b4ad371f-c45b-496a-81db-5d94c4249449
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves13.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_312 (v : ℝ) (hl : (8531 / 19200) ≤ v) (hu : v ≤ (91087 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8531 / 19200)) (u := (91087 / 204800)) (xl := (44372527 / 400000000)) (xu := (111817877 / 1000000000))
    (Bl := (17482187 / 25000000)) (Bu := (1398771631 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_312.2.1 endpoint_313.1 endpoint_312.2.2.2 endpoint_313.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_313 (v : ℝ) (hl : (91087 / 204800) ≤ v) (hu : v ≤ (27353 / 61440)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (91087 / 204800)) (u := (27353 / 61440)) (xl := (220089867 / 2000000000)) (xu := (110931319 / 1000000000))
    (Bl := (349594971 / 500000000)) (Bu := (1398574963 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_313.2.1 endpoint_314.1 endpoint_313.2.2.2 endpoint_314.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_314 (v : ℝ) (hl : (27353 / 61440) ≤ v) (hu : v ≤ (273799 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (27353 / 61440)) (u := (273799 / 614400)) (xl := (109158721 / 1000000000)) (xu := (22008987 / 200000000))
    (Bl := (1398186397 / 2000000000)) (Bu := (1398379887 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_314.2.1 endpoint_315.1 endpoint_314.2.2.2 endpoint_315.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_315 (v : ℝ) (hl : (273799 / 614400) ≤ v) (hu : v ≤ (22839 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (273799 / 614400)) (u := (22839 / 51200)) (xl := (216545359 / 2000000000)) (xu := (43663489 / 400000000))
    (Bl := (2795989 / 4000000)) (Bu := (1747733 / 2500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_315.2.1 endpoint_316.1 endpoint_315.2.2.2 endpoint_316.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_316 (v : ℝ) (hl : (22839 / 51200) ≤ v) (hu : v ≤ (274337 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (22839 / 51200)) (u := (274337 / 614400)) (xl := (42954723 / 400000000)) (xu := (108272681 / 1000000000))
    (Bl := (139780419 / 200000000)) (Bu := (1397994503 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_316.2.1 endpoint_317.1 endpoint_316.2.2.2 endpoint_317.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_317 (v : ℝ) (hl : (274337 / 614400) ≤ v) (hu : v ≤ (137303 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (274337 / 614400)) (u := (137303 / 307200)) (xl := (213002207 / 2000000000)) (xu := (107386809 / 1000000000))
    (Bl := (349403867 / 500000000)) (Bu := (1397804193 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_317.2.1 endpoint_318.1 endpoint_317.2.2.2 endpoint_318.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_318 (v : ℝ) (hl : (137303 / 307200) ≤ v) (hu : v ≤ (3665 / 8192)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (137303 / 307200)) (u := (3665 / 8192)) (xl := (52807783 / 500000000)) (xu := (21300221 / 200000000))
    (Bl := (1397428331 / 2000000000)) (Bu := (1397615471 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_318.2.1 endpoint_319.1 endpoint_318.2.2.2 endpoint_319.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_319 (v : ℝ) (hl : (3665 / 8192) ≤ v) (hu : v ≤ (34393 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3665 / 8192)) (u := (34393 / 76800)) (xl := (104730193 / 1000000000)) (xu := (42246227 / 400000000))
    (Bl := (1397242781 / 2000000000)) (Bu := (698714167 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_319.2.1 endpoint_320.1 endpoint_319.2.2.2 endpoint_320.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_320 (v : ℝ) (hl : (34393 / 76800) ≤ v) (hu : v ≤ (275413 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (34393 / 76800)) (u := (275413 / 614400)) (xl := (12980623 / 125000000)) (xu := (209460389 / 2000000000))
    (Bl := (279411763 / 400000000)) (Bu := (43663837 / 62500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_320.2.1 endpoint_321.1 endpoint_320.2.2.2 endpoint_321.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_321 (v : ℝ) (hl : (275413 / 614400) ≤ v) (hu : v ≤ (45947 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (275413 / 614400)) (u := (45947 / 102400)) (xl := (205919873 / 2000000000)) (xu := (207689971 / 2000000000))
    (Bl := (87304777 / 125000000)) (Bu := (698529409 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_321.2.1 endpoint_322.1 endpoint_321.2.2.2 endpoint_322.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_322 (v : ℝ) (hl : (45947 / 102400) ≤ v) (hu : v ≤ (275951 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (45947 / 102400)) (u := (275951 / 614400)) (xl := (204150101 / 2000000000)) (xu := (51479969 / 500000000))
    (Bl := (87293477 / 125000000)) (Bu := (279375287 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_322.2.1 endpoint_323.1 endpoint_322.2.2.2 endpoint_323.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_323 (v : ℝ) (hl : (275951 / 614400) ≤ v) (hu : v ≤ (13811 / 30720)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (275951 / 614400)) (u := (13811 / 30720)) (xl := (202380647 / 2000000000)) (xu := (25518763 / 250000000))
    (Bl := (698258207 / 1000000000)) (Bu := (279339127 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_323.2.1 endpoint_324.1 endpoint_323.2.2.2 endpoint_324.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_324 (v : ℝ) (hl : (13811 / 30720) ≤ v) (hu : v ≤ (92163 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13811 / 30720)) (u := (92163 / 204800)) (xl := (200611509 / 2000000000)) (xu := (4047613 / 40000000))
    (Bl := (698169389 / 1000000000)) (Bu := (1396516417 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_324.2.1 endpoint_325.1 endpoint_324.2.2.2 endpoint_325.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_325 (v : ℝ) (hl : (92163 / 204800) ≤ v) (hu : v ≤ (138379 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (92163 / 204800)) (u := (138379 / 307200)) (xl := (198842683 / 2000000000)) (xu := (25076439 / 250000000))
    (Bl := (698081361 / 1000000000)) (Bu := (1396338781 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_325.2.1 endpoint_326.1 endpoint_325.2.2.2 endpoint_326.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_326 (v : ℝ) (hl : (138379 / 307200) ≤ v) (hu : v ≤ (277027 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (138379 / 307200)) (u := (277027 / 614400)) (xl := (197074167 / 2000000000)) (xu := (99421343 / 1000000000))
    (Bl := (348997061 / 500000000)) (Bu := (55846509 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_326.2.1 endpoint_327.1 endpoint_326.2.2.2 endpoint_327.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_327 (v : ℝ) (hl : (277027 / 614400) ≤ v) (hu : v ≤ (5777 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (277027 / 614400)) (u := (5777 / 12800)) (xl := (195305959 / 2000000000)) (xu := (19707417 / 200000000))
    (Bl := (697907673 / 1000000000)) (Bu := (1395988247 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_327.2.1 endpoint_328.1 endpoint_327.2.2.2 endpoint_328.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_328 (v : ℝ) (hl : (5777 / 12800) ≤ v) (hu : v ≤ (55513 / 122880)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5777 / 12800)) (u := (55513 / 122880)) (xl := (38707611 / 400000000)) (xu := (97652981 / 1000000000))
    (Bl := (697822013 / 1000000000)) (Bu := (1395815349 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_328.2.1 endpoint_329.1 endpoint_328.2.2.2 endpoint_329.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_329 (v : ℝ) (hl : (55513 / 122880) ≤ v) (hu : v ≤ (138917 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (55513 / 122880)) (u := (138917 / 307200)) (xl := (47942613 / 500000000)) (xu := (96769029 / 1000000000))
    (Bl := (1395474283 / 2000000000)) (Bu := (1395644029 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_329.2.1 endpoint_330.1 endpoint_329.2.2.2 endpoint_330.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_330 (v : ℝ) (hl : (138917 / 307200) ≤ v) (hu : v ≤ (92701 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (138917 / 307200)) (u := (92701 / 204800)) (xl := (47500787 / 500000000)) (xu := (38354091 / 400000000))
    (Bl := (279061223 / 400000000)) (Bu := (697737143 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_330.2.1 endpoint_331.1 endpoint_330.2.2.2 endpoint_331.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_331 (v : ℝ) (hl : (92701 / 204800) ≤ v) (hu : v ≤ (69593 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (92701 / 204800)) (u := (69593 / 153600)) (xl := (188236139 / 2000000000)) (xu := (190003151 / 2000000000))
    (Bl := (348784881 / 500000000)) (Bu := (697653059 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_331.2.1 endpoint_332.1 endpoint_331.2.2.2 endpoint_332.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_332 (v : ℝ) (hl : (69593 / 153600) ≤ v) (hu : v ≤ (278641 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (69593 / 153600)) (u := (278641 / 614400)) (xl := (11654339 / 125000000)) (xu := (94118071 / 1000000000))
    (Bl := (1394974507 / 2000000000)) (Bu := (1395139527 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_332.2.1 endpoint_333.1 endpoint_332.2.2.2 endpoint_333.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_333 (v : ℝ) (hl : (278641 / 614400) ≤ v) (hu : v ≤ (9297 / 20480)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (278641 / 614400)) (u := (9297 / 20480)) (xl := (184702999 / 2000000000)) (xu := (186469427 / 2000000000))
    (Bl := (174351383 / 250000000)) (Bu := (139497451 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_333.2.1 endpoint_334.1 endpoint_333.2.2.2 endpoint_334.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_334 (v : ℝ) (hl : (9297 / 20480) ≤ v) (hu : v ≤ (279179 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9297 / 20480)) (u := (279179 / 614400)) (xl := (182936861 / 2000000000)) (xu := (92351501 / 1000000000))
    (Bl := (697324597 / 1000000000)) (Bu := (1394811067 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_334.2.1 endpoint_335.1 endpoint_334.2.2.2 endpoint_335.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_335 (v : ℝ) (hl : (279179 / 614400) ≤ v) (hu : v ≤ (34931 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (279179 / 614400)) (u := (34931 / 76800)) (xl := (2830797 / 31250000)) (xu := (5716777 / 62500000))
    (Bl := (278897779 / 400000000)) (Bu := (1394649197 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_335.2.1 endpoint_336.1 endpoint_335.2.2.2 endpoint_336.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


