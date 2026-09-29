-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves12
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:35.42167+00:00
-- url     : https://prove2.me/theorems/38743c10-7680-45d8-954f-b7276b37bfb6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves12` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves12` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves12` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves12 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves12.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_288 (v : ℝ) (hl : (64751 / 153600) ≤ v) (hu : v ≤ (3251 / 7680)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (64751 / 153600)) (u := (3251 / 7680)) (xl := (154605591 / 1000000000)) (xu := (79097289 / 500000000))
    (Bl := (1410102627 / 2000000000)) (Bu := (1411216199 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_288.2.1 endpoint_289.1 endpoint_288.2.2.2 endpoint_289.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_289 (v : ℝ) (hl : (3251 / 7680) ≤ v) (hu : v ≤ (21763 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3251 / 7680)) (u := (21763 / 51200)) (xl := (60408221 / 400000000)) (xu := (61842237 / 400000000))
    (Bl := (352253849 / 500000000)) (Bu := (141010263 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_289.2.1 endpoint_290.1 endpoint_289.2.2.2 endpoint_290.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_290 (v : ℝ) (hl : (21763 / 51200) ≤ v) (hu : v ≤ (32779 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (21763 / 51200)) (u := (32779 / 76800)) (xl := (11795149 / 80000000)) (xu := (75510277 / 500000000))
    (Bl := (70397721 / 100000000)) (Bu := (1409015399 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_290.2.1 endpoint_291.1 endpoint_290.2.2.2 endpoint_291.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_291 (v : ℝ) (hl : (32779 / 76800) ≤ v) (hu : v ≤ (8759 / 20480)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (32779 / 76800)) (u := (8759 / 20480)) (xl := (7282509 / 50000000)) (xu := (36859841 / 250000000))
    (Bl := (1407433751 / 2000000000)) (Bu := (1407954423 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_291.2.1 endpoint_292.1 endpoint_291.2.2.2 endpoint_292.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_292 (v : ℝ) (hl : (8759 / 20480) ≤ v) (hu : v ≤ (65827 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8759 / 20480)) (u := (65827 / 153600)) (xl := (143861923 / 1000000000)) (xu := (291300363 / 2000000000))
    (Bl := (281383923 / 400000000)) (Bu := (703716877 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_292.2.1 endpoint_293.1 endpoint_292.2.2.2 endpoint_293.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_293 (v : ℝ) (hl : (65827 / 153600) ≤ v) (hu : v ≤ (131923 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (65827 / 153600)) (u := (131923 / 307200)) (xl := (284149159 / 2000000000)) (xu := (287723849 / 2000000000))
    (Bl := (703206001 / 1000000000)) (Bu := (703459809 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_293.2.1 endpoint_294.1 endpoint_293.2.2.2 endpoint_294.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_294 (v : ℝ) (hl : (131923 / 307200) ≤ v) (hu : v ≤ (1377 / 3200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (131923 / 307200)) (u := (1377 / 3200)) (xl := (140288137 / 1000000000)) (xu := (142074581 / 1000000000))
    (Bl := (1405910903 / 2000000000)) (Bu := (281282401 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_294.2.1 endpoint_295.1 endpoint_294.2.2.2 endpoint_295.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_295 (v : ℝ) (hl : (1377 / 3200) ≤ v) (hu : v ≤ (132461 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1377 / 3200)) (u := (132461 / 307200)) (xl := (17312823 / 125000000)) (xu := (280576277 / 2000000000))
    (Bl := (1405416307 / 2000000000)) (Bu := (702955453 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_295.2.1 endpoint_296.1 endpoint_295.2.2.2 endpoint_296.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_296 (v : ℝ) (hl : (132461 / 307200) ≤ v) (hu : v ≤ (13273 / 30720)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (132461 / 307200)) (u := (13273 / 30720)) (xl := (34179477 / 250000000)) (xu := (277005171 / 2000000000))
    (Bl := (280985641 / 400000000)) (Bu := (140541631 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_296.2.1 endpoint_297.1 endpoint_296.2.2.2 endpoint_297.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_297 (v : ℝ) (hl : (13273 / 30720) ≤ v) (hu : v ≤ (44333 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13273 / 30720)) (u := (44333 / 102400)) (xl := (134934097 / 1000000000)) (xu := (273435819 / 2000000000))
    (Bl := (1404446587 / 2000000000)) (Bu := (87808013 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_297.2.1 endpoint_298.1 endpoint_297.2.2.2 endpoint_298.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_298 (v : ℝ) (hl : (44333 / 102400) ≤ v) (hu : v ≤ (33317 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (44333 / 102400)) (u := (33317 / 76800)) (xl := (133151139 / 1000000000)) (xu := (269868197 / 2000000000))
    (Bl := (280794289 / 400000000)) (Bu := (140444659 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_298.2.1 endpoint_299.1 endpoint_298.2.2.2 endpoint_299.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_299 (v : ℝ) (hl : (33317 / 76800) ≤ v) (hu : v ≤ (133537 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (33317 / 76800)) (u := (133537 / 307200)) (xl := (52547609 / 400000000)) (xu := (266302281 / 2000000000))
    (Bl := (87718923 / 125000000)) (Bu := (175496431 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_299.2.1 endpoint_300.1 endpoint_299.2.2.2 endpoint_300.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_300 (v : ℝ) (hl : (133537 / 307200) ≤ v) (hu : v ≤ (22301 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (133537 / 307200)) (u := (22301 / 51200)) (xl := (25917547 / 200000000)) (xu := (2052641 / 15625000))
    (Bl := (1403040549 / 2000000000)) (Bu := (1403502771 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_300.2.1 endpoint_301.1 endpoint_300.2.2.2 endpoint_301.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_301 (v : ℝ) (hl : (22301 / 51200) ≤ v) (hu : v ≤ (5363 / 12288)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (22301 / 51200)) (u := (5363 / 12288)) (xl := (25561453 / 200000000)) (xu := (259175473 / 2000000000))
    (Bl := (1402584779 / 2000000000)) (Bu := (175380069 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_301.2.1 endpoint_302.1 endpoint_301.2.2.2 endpoint_302.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_302 (v : ℝ) (hl : (5363 / 12288) ≤ v) (hu : v ≤ (16793 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5363 / 12288)) (u := (16793 / 38400)) (xl := (126027601 / 1000000000)) (xu := (255614533 / 2000000000))
    (Bl := (1402135449 / 2000000000)) (Bu := (701292391 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_302.2.1 endpoint_303.1 endpoint_302.2.2.2 endpoint_303.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_303 (v : ℝ) (hl : (16793 / 38400) ≤ v) (hu : v ≤ (44871 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (16793 / 38400)) (u := (44871 / 102400)) (xl := (12424873 / 100000000)) (xu := (50411041 / 400000000))
    (Bl := (1401692549 / 2000000000)) (Bu := (350533863 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_303.2.1 endpoint_304.1 endpoint_303.2.2.2 endpoint_304.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_304 (v : ℝ) (hl : (44871 / 102400) ≤ v) (hu : v ≤ (67441 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (44871 / 102400)) (u := (67441 / 153600)) (xl := (244941283 / 2000000000)) (xu := (248497463 / 2000000000))
    (Bl := (175157009 / 250000000)) (Bu := (175211569 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_304.2.1 endpoint_305.1 endpoint_304.2.2.2 endpoint_305.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_305 (v : ℝ) (hl : (67441 / 153600) ≤ v) (hu : v ≤ (135151 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (67441 / 153600)) (u := (135151 / 307200)) (xl := (120693323 / 1000000000)) (xu := (122470643 / 1000000000))
    (Bl := (1400826009 / 2000000000)) (Bu := (56050243 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_305.2.1 endpoint_306.1 endpoint_305.2.2.2 endpoint_306.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_306 (v : ℝ) (hl : (135151 / 307200) ≤ v) (hu : v ≤ (2257 / 5120)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (135151 / 307200)) (u := (2257 / 5120)) (xl := (237833527 / 2000000000)) (xu := (241386649 / 2000000000))
    (Bl := (87525147 / 125000000)) (Bu := (350206503 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_306.2.1 endpoint_307.1 endpoint_306.2.2.2 endpoint_307.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_307 (v : ℝ) (hl : (2257 / 5120) ≤ v) (hu : v ≤ (135689 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2257 / 5120)) (u := (135689 / 307200)) (xl := (234281901 / 2000000000)) (xu := (23783353 / 200000000))
    (Bl := (699992547 / 1000000000)) (Bu := (280080471 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_307.2.1 endpoint_308.1 endpoint_307.2.2.2 endpoint_308.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_308 (v : ℝ) (hl : (135689 / 307200) ≤ v) (hu : v ≤ (67979 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (135689 / 307200)) (u := (67979 / 153600)) (xl := (46146349 / 400000000)) (xu := (14642619 / 125000000))
    (Bl := (699787113 / 1000000000)) (Bu := (1399985097 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_308.2.1 endpoint_309.1 endpoint_308.2.2.2 endpoint_309.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_309 (v : ℝ) (hl : (67979 / 153600) ≤ v) (hu : v ≤ (45409 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (67979 / 153600)) (u := (45409 / 102400)) (xl := (56795759 / 500000000)) (xu := (57682937 / 500000000))
    (Bl := (1399169739 / 2000000000)) (Bu := (1399574229 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_309.2.1 endpoint_310.1 endpoint_309.2.2.2 endpoint_310.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_310 (v : ℝ) (hl : (45409 / 102400) ≤ v) (hu : v ≤ (272723 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (45409 / 102400)) (u := (272723 / 614400)) (xl := (225409217 / 2000000000)) (xu := (227183039 / 2000000000))
    (Bl := (43717809 / 62500000)) (Bu := (699584871 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_310.2.1 endpoint_311.1 endpoint_310.2.2.2 endpoint_311.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_311 (v : ℝ) (hl : (272723 / 614400) ≤ v) (hu : v ≤ (8531 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (272723 / 614400)) (u := (8531 / 19200)) (xl := (223635751 / 2000000000)) (xu := (11270461 / 100000000))
    (Bl := (349692907 / 500000000)) (Bu := (1398969891 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_311.2.1 endpoint_312.1 endpoint_311.2.2.2 endpoint_312.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


