-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves11
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:55:00.031839+00:00
-- url     : https://prove2.me/theorems/97cfaf2b-d520-4869-bfcc-74ce745b3f89
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves11` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves11` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves11` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves11 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves11.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_264 (v : ℝ) (hl : (277 / 800) ≤ v) (hu : v ≤ (2713 / 7680)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (277 / 800)) (u := (2713 / 7680)) (xl := (604761 / 2000000)) (xu := (635563959 / 2000000000))
    (Bl := (1476368023 / 2000000000)) (Bu := (742812243 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_264.2.1 endpoint_265.1 endpoint_264.2.2.2 endpoint_265.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_265 (v : ℝ) (hl : (2713 / 7680) ≤ v) (hu : v ≤ (6917 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2713 / 7680)) (u := (6917 / 19200)) (xl := (574234041 / 2000000000)) (xu := (604761003 / 2000000000))
    (Bl := (733811107 / 1000000000)) (Bu := (738184013 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_265.2.1 endpoint_266.1 endpoint_265.2.2.2 endpoint_266.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_266 (v : ℝ) (hl : (6917 / 19200) ≤ v) (hu : v ≤ (4701 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6917 / 19200)) (u := (4701 / 12800)) (xl := (16998917 / 62500000)) (xu := (143558511 / 500000000))
    (Bl := (1459374491 / 2000000000)) (Bu := (1467622217 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_266.2.1 endpoint_267.1 endpoint_266.2.2.2 endpoint_267.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_267 (v : ℝ) (hl : (4701 / 12800) ≤ v) (hu : v ≤ (1139 / 3072)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4701 / 12800)) (u := (1139 / 3072)) (xl := (264461257 / 1000000000)) (xu := (543965347 / 2000000000))
    (Bl := (291086749 / 400000000)) (Bu := (729687247 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_267.2.1 endpoint_268.1 endpoint_267.2.2.2 endpoint_268.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_268 (v : ℝ) (hl : (1139 / 3072) ≤ v) (hu : v ≤ (3593 / 9600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1139 / 3072)) (u := (3593 / 9600)) (xl := (256968973 / 1000000000)) (xu := (528922517 / 2000000000))
    (Bl := (1451613231 / 2000000000)) (Bu := (363858437 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_268.2.1 endpoint_269.1 endpoint_268.2.2.2 endpoint_269.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_269 (v : ℝ) (hl : (3593 / 9600) ≤ v) (hu : v ≤ (9671 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3593 / 9600)) (u := (9671 / 25600)) (xl := (499009629 / 2000000000)) (xu := (513937949 / 2000000000))
    (Bl := (723955819 / 1000000000)) (Bu := (725806617 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_269.2.1 endpoint_270.1 endpoint_269.2.2.2 endpoint_270.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_270 (v : ℝ) (hl : (9671 / 25600) ≤ v) (hu : v ≤ (14641 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9671 / 25600)) (u := (14641 / 38400)) (xl := (60516949 / 250000000)) (xu := (15594051 / 62500000))
    (Bl := (1444327699 / 2000000000)) (Bu := (1447911641 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_270.2.1 endpoint_271.1 endpoint_270.2.2.2 endpoint_271.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_271 (v : ℝ) (hl : (14641 / 38400) ≤ v) (hu : v ≤ (29551 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14641 / 38400)) (u := (29551 / 76800)) (xl := (29332119 / 125000000)) (xu := (96827119 / 400000000))
    (Bl := (288172041 / 400000000)) (Bu := (722163851 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_271.2.1 endpoint_272.1 endpoint_271.2.2.2 endpoint_272.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_272 (v : ℝ) (hl : (29551 / 76800) ≤ v) (hu : v ≤ (497 / 1280)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (29551 / 76800)) (u := (497 / 1280)) (xl := (454542669 / 2000000000)) (xu := (469313907 / 2000000000))
    (Bl := (143750799 / 200000000)) (Bu := (90053763 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_272.2.1 endpoint_273.1 endpoint_272.2.2.2 endpoint_273.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_273 (v : ℝ) (hl : (497 / 1280) ≤ v) (hu : v ≤ (30089 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (497 / 1280)) (u := (30089 / 76800)) (xl := (17592801 / 80000000)) (xu := (28408917 / 125000000))
    (Bl := (71713497 / 100000000)) (Bu := (1437507993 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_273.2.1 endpoint_274.1 endpoint_273.2.2.2 endpoint_274.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_274 (v : ℝ) (hl : (30089 / 76800) ≤ v) (hu : v ≤ (15179 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (30089 / 76800)) (u := (15179 / 38400)) (xl := (425144147 / 2000000000)) (xu := (109955007 / 500000000))
    (Bl := (715572491 / 1000000000)) (Bu := (1434269943 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_274.2.1 endpoint_275.1 endpoint_274.2.2.2 endpoint_275.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_275 (v : ℝ) (hl : (15179 / 38400) ≤ v) (hu : v ≤ (10209 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (15179 / 38400)) (u := (10209 / 25600)) (xl := (410513237 / 2000000000)) (xu := (8502883 / 40000000))
    (Bl := (714066047 / 1000000000)) (Bu := (286228997 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_275.2.1 endpoint_276.1 endpoint_275.2.2.2 endpoint_276.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_276 (v : ℝ) (hl : (10209 / 25600) ≤ v) (hu : v ≤ (1931 / 4800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10209 / 25600)) (u := (1931 / 4800)) (xl := (98981383 / 500000000)) (xu := (10262831 / 50000000))
    (Bl := (1425230293 / 2000000000)) (Bu := (1428132097 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_276.2.1 endpoint_277.1 endpoint_276.2.2.2 endpoint_277.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_277 (v : ℝ) (hl : (1931 / 4800) ≤ v) (hu : v ≤ (20687 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1931 / 4800)) (u := (20687 / 51200)) (xl := (388647337 / 2000000000)) (xu := (79185107 / 400000000))
    (Bl := (355955189 / 500000000)) (Bu := (178153787 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_277.2.1 endpoint_278.1 endpoint_277.2.2.2 endpoint_278.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_278 (v : ℝ) (hl : (20687 / 51200) ≤ v) (hu : v ≤ (6233 / 15360)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (20687 / 51200)) (u := (6233 / 15360)) (xl := (190689647 / 1000000000)) (xu := (19432367 / 100000000))
    (Bl := (1422438643 / 2000000000)) (Bu := (1423820759 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_278.2.1 endpoint_279.1 endpoint_278.2.2.2 endpoint_279.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_279 (v : ℝ) (hl : (6233 / 15360) ≤ v) (hu : v ≤ (62599 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6233 / 15360)) (u := (62599 / 153600)) (xl := (37412119 / 200000000)) (xu := (381379297 / 2000000000))
    (Bl := (1421083841 / 2000000000)) (Bu := (711219323 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_279.2.1 endpoint_280.1 endpoint_279.2.2.2 endpoint_280.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_280 (v : ℝ) (hl : (62599 / 153600) ≤ v) (hu : v ≤ (5239 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (62599 / 153600)) (u := (5239 / 12800)) (xl := (183436407 / 1000000000)) (xu := (374121193 / 2000000000))
    (Bl := (1419756243 / 2000000000)) (Bu := (355270961 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_280.2.1 endpoint_281.1 endpoint_280.2.2.2 endpoint_281.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_281 (v : ℝ) (hl : (5239 / 12800) ≤ v) (hu : v ≤ (63137 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5239 / 12800)) (u := (63137 / 153600)) (xl := (359633957 / 2000000000)) (xu := (366872817 / 2000000000))
    (Bl := (22163371 / 31250000)) (Bu := (709878123 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_281.2.1 endpoint_282.1 endpoint_281.2.2.2 endpoint_282.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_282 (v : ℝ) (hl : (63137 / 153600) ≤ v) (hu : v ≤ (31703 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (63137 / 153600)) (u := (31703 / 76800)) (xl := (35240441 / 200000000)) (xu := (8990849 / 50000000))
    (Bl := (1417182239 / 2000000000)) (Bu := (1418455747 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_282.2.1 endpoint_283.1 endpoint_282.2.2.2 endpoint_283.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_283 (v : ℝ) (hl : (31703 / 76800) ≤ v) (hu : v ≤ (849 / 2048)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (31703 / 76800)) (u := (849 / 2048)) (xl := (345183967 / 2000000000)) (xu := (352404413 / 2000000000))
    (Bl := (141593563 / 200000000)) (Bu := (708591121 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_283.2.1 endpoint_284.1 endpoint_283.2.2.2 endpoint_284.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_284 (v : ℝ) (hl : (849 / 2048) ≤ v) (hu : v ≤ (7993 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (849 / 2048)) (u := (7993 / 19200)) (xl := (337972423 / 2000000000)) (xu := (34518397 / 200000000))
    (Bl := (707357907 / 1000000000)) (Bu := (1415935633 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_284.2.1 endpoint_285.1 endpoint_284.2.2.2 endpoint_285.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_285 (v : ℝ) (hl : (7993 / 19200) ≤ v) (hu : v ≤ (64213 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7993 / 19200)) (u := (64213 / 153600)) (xl := (165384787 / 1000000000)) (xu := (168986213 / 1000000000))
    (Bl := (1413522699 / 2000000000)) (Bu := (1414715817 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_285.2.1 endpoint_286.1 endpoint_285.2.2.2 endpoint_286.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_286 (v : ℝ) (hl : (64213 / 153600) ≤ v) (hu : v ≤ (10747 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (64213 / 153600)) (u := (10747 / 25600)) (xl := (161787609 / 1000000000)) (xu := (330769577 / 2000000000))
    (Bl := (1412356191 / 2000000000)) (Bu := (706761351 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_286.2.1 endpoint_287.1 endpoint_286.2.2.2 endpoint_287.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_287 (v : ℝ) (hl : (10747 / 25600) ≤ v) (hu : v ≤ (64751 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10747 / 25600)) (u := (64751 / 153600)) (xl := (316389153 / 2000000000)) (xu := (323575221 / 2000000000))
    (Bl := (352804049 / 500000000)) (Bu := (706178097 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_287.2.1 endpoint_288.1 endpoint_287.2.2.2 endpoint_288.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


