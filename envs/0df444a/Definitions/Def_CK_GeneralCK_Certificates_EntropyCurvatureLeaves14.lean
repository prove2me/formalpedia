-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves14
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:58:21.109992+00:00
-- url     : https://prove2.me/theorems/d4d07f0f-e7f6-40f7-8f09-ae36eeb89b27
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves14` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves14` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves14` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves14 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves14.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_336 (v : ℝ) (hl : (34931 / 76800) ≤ v) (hu : v ≤ (93239 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (34931 / 76800)) (u := (93239 / 204800)) (xl := (44851359 / 500000000)) (xu := (181171011 / 2000000000))
    (Bl := (1394330169 / 2000000000)) (Bu := (697244449 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_336.2.1 endpoint_337.1 endpoint_336.2.2.2 endpoint_337.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_337 (v : ℝ) (hl : (93239 / 204800) ≤ v) (hu : v ≤ (139993 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (93239 / 204800)) (u := (139993 / 307200)) (xl := (177640143 / 2000000000)) (xu := (179405439 / 2000000000))
    (Bl := (697086507 / 1000000000)) (Bu := (348582543 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_337.2.1 endpoint_338.1 endpoint_337.2.2.2 endpoint_338.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_338 (v : ℝ) (hl : (139993 / 307200) ≤ v) (hu : v ≤ (186747 / 409600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (139993 / 307200)) (u := (186747 / 409600)) (xl := (220947 / 2500000)) (xu := (88820073 / 1000000000))
    (Bl := (55763801 / 80000000)) (Bu := (1394173017 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_338.2.1 endpoint_339.1 endpoint_338.2.2.2 endpoint_339.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_339 (v : ℝ) (hl : (186747 / 409600) ≤ v) (hu : v ≤ (56051 / 122880)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (186747 / 409600)) (u := (56051 / 122880)) (xl := (87937563 / 1000000000)) (xu := (176757603 / 2000000000))
    (Bl := (1394017429 / 2000000000)) (Bu := (348523757 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_339.2.1 endpoint_340.1 endpoint_339.2.2.2 endpoint_340.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_340 (v : ℝ) (hl : (56051 / 122880) ≤ v) (hu : v ≤ (560779 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (56051 / 122880)) (u := (560779 / 1228800)) (xl := (2187409 / 25000000)) (xu := (175875129 / 2000000000))
    (Bl := (55757609 / 80000000)) (Bu := (174252179 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_340.2.1 endpoint_341.1 endpoint_340.2.2.2 endpoint_341.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_341 (v : ℝ) (hl : (560779 / 1228800) ≤ v) (hu : v ≤ (23377 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (560779 / 1228800)) (u := (23377 / 51200)) (xl := (87055191 / 1000000000)) (xu := (174992723 / 2000000000))
    (Bl := (1393863413 / 2000000000)) (Bu := (348485057 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_341.2.1 endpoint_342.1 endpoint_341.2.2.2 endpoint_342.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_342 (v : ℝ) (hl : (23377 / 51200) ≤ v) (hu : v ≤ (561317 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (23377 / 51200)) (u := (561317 / 1228800)) (xl := (10826757 / 125000000)) (xu := (34822077 / 400000000))
    (Bl := (1393786993 / 2000000000)) (Bu := (174232927 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_342.2.1 endpoint_343.1 endpoint_342.2.2.2 endpoint_343.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_343 (v : ℝ) (hl : (561317 / 1228800) ≤ v) (hu : v ≤ (280793 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (561317 / 1228800)) (u := (280793 / 614400)) (xl := (172345909 / 2000000000)) (xu := (34645623 / 400000000))
    (Bl := (696855483 / 1000000000)) (Bu := (348446749 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_343.2.1 endpoint_344.1 endpoint_343.2.2.2 endpoint_344.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_344 (v : ℝ) (hl : (280793 / 614400) ≤ v) (hu : v ≤ (37457 / 81920)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (280793 / 614400)) (u := (37457 / 81920)) (xl := (171463773 / 2000000000)) (xu := (21543239 / 250000000))
    (Bl := (139363533 / 200000000)) (Bu := (1393710969 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_344.2.1 endpoint_345.1 endpoint_344.2.2.2 endpoint_345.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_345 (v : ℝ) (hl : (37457 / 81920) ≤ v) (hu : v ≤ (140531 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (37457 / 81920)) (u := (140531 / 307200)) (xl := (170581703 / 2000000000)) (xu := (5358243 / 62500000))
    (Bl := (696780043 / 1000000000)) (Bu := (1393635333 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_345.2.1 endpoint_346.1 endpoint_345.2.2.2 endpoint_346.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_346 (v : ℝ) (hl : (140531 / 307200) ≤ v) (hu : v ≤ (562393 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (140531 / 307200)) (u := (562393 / 1228800)) (xl := (1696997 / 20000000)) (xu := (85290853 / 1000000000))
    (Bl := (278697047 / 400000000)) (Bu := (1393560089 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_346.2.1 endpoint_347.1 endpoint_346.2.2.2 endpoint_347.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_347 (v : ℝ) (hl : (562393 / 1228800) ≤ v) (hu : v ≤ (93777 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (562393 / 1228800)) (u := (93777 / 204800)) (xl := (84408881 / 1000000000)) (xu := (169699703 / 2000000000))
    (Bl := (55736431 / 80000000)) (Bu := (696742619 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_347.2.1 endpoint_348.1 endpoint_347.2.2.2 endpoint_348.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_348 (v : ℝ) (hl : (93777 / 204800) ≤ v) (hu : v ≤ (562931 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (93777 / 204800)) (u := (562931 / 1228800)) (xl := (16793589 / 200000000)) (xu := (33763553 / 400000000))
    (Bl := (278667341 / 400000000)) (Bu := (696705389 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_348.2.1 endpoint_349.1 endpoint_348.2.2.2 endpoint_349.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_349 (v : ℝ) (hl : (562931 / 1228800) ≤ v) (hu : v ≤ (11 / 24)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (562931 / 1228800)) (u := (11 / 24)) (xl := (167054083 / 2000000000)) (xu := (167935893 / 2000000000))
    (Bl := (348315757 / 500000000)) (Bu := (348334177 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_349.2.1 endpoint_350.1 endpoint_349.2.2.2 endpoint_350.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


