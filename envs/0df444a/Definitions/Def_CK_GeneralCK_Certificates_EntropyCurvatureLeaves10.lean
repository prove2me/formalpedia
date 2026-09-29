-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves10
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:54:56.048286+00:00
-- url     : https://prove2.me/theorems/5b35e862-0388-4c94-8a64-8d0630054621
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves10` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves10` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves10` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves10 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves10.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_240 (v : ℝ) (hl : (57 / 320) ≤ v) (hu : v ≤ (7109 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (57 / 320)) (u := (7109 / 38400)) (xl := (1481968927 / 2000000000)) (xu := (764551383 / 1000000000))
    (Bl := (945711407 / 1000000000)) (Bu := (1921436693 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_240.2.1 endpoint_241.1 endpoint_240.2.2.2 endpoint_241.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_241 (v : ℝ) (hl : (7109 / 38400) ≤ v) (hu : v ≤ (3689 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7109 / 38400)) (u := (3689 / 19200)) (xl := (1436194029 / 2000000000)) (xu := (1481968931 / 2000000000))
    (Bl := (232864461 / 250000000)) (Bu := (945711409 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_241.2.1 endpoint_242.1 endpoint_241.2.2.2 endpoint_242.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_242 (v : ℝ) (hl : (3689 / 19200) ≤ v) (hu : v ≤ (2549 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3689 / 19200)) (u := (2549 / 12800)) (xl := (695837067 / 1000000000)) (xu := (1436194033 / 2000000000))
    (Bl := (1835813953 / 2000000000)) (Bu := (465728923 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_242.2.1 endpoint_243.1 endpoint_242.2.2.2 endpoint_243.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_243 (v : ℝ) (hl : (2549 / 12800) ≤ v) (hu : v ≤ (1979 / 9600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2549 / 12800)) (u := (1979 / 9600)) (xl := (674157963 / 1000000000)) (xu := (695837069 / 1000000000))
    (Bl := (1810026933 / 2000000000)) (Bu := (1835813957 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_243.2.1 endpoint_244.1 endpoint_243.2.2.2 endpoint_244.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_244 (v : ℝ) (hl : (1979 / 9600) ≤ v) (hu : v ≤ (1637 / 7680)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1979 / 9600)) (u := (1637 / 7680)) (xl := (1306035277 / 2000000000)) (xu := (134831593 / 200000000))
    (Bl := (27898019 / 31250000)) (Bu := (1810026937 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_244.2.1 endpoint_245.1 endpoint_244.2.2.2 endpoint_245.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_245 (v : ℝ) (hl : (1637 / 7680) ≤ v) (hu : v ≤ (1409 / 6400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1637 / 7680)) (u := (1409 / 6400)) (xl := (158094507 / 250000000)) (xu := (1306035281 / 2000000000))
    (Bl := (352415891 / 400000000)) (Bu := (89273661 / 100000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_245.2.1 endpoint_246.1 endpoint_245.2.2.2 endpoint_246.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_246 (v : ℝ) (hl : (1409 / 6400) ≤ v) (hu : v ≤ (8723 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1409 / 6400)) (u := (8723 / 38400)) (xl := (612204559 / 1000000000)) (xu := (63237803 / 100000000))
    (Bl := (1739779367 / 2000000000)) (Bu := (1762079459 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_246.2.1 endpoint_247.1 endpoint_246.2.2.2 endpoint_247.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_247 (v : ℝ) (hl : (8723 / 38400) ≤ v) (hu : v ≤ (281 / 1200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8723 / 38400)) (u := (281 / 1200)) (xl := (1184931451 / 2000000000)) (xu := (612204561 / 1000000000))
    (Bl := (859256439 / 1000000000)) (Bu := (1739779371 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_247.2.1 endpoint_248.1 endpoint_247.2.2.2 endpoint_248.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_248 (v : ℝ) (hl : (281 / 1200) ≤ v) (hu : v ≤ (3087 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (281 / 1200)) (u := (3087 / 12800)) (xl := (1146265447 / 2000000000)) (xu := (236986291 / 400000000))
    (Bl := (8491127 / 10000000)) (Bu := (859256441 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_248.2.1 endpoint_249.1 endpoint_248.2.2.2 endpoint_249.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_249 (v : ℝ) (hl : (3087 / 12800) ≤ v) (hu : v ≤ (953 / 3840)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3087 / 12800)) (u := (953 / 3840)) (xl := (554179137 / 1000000000)) (xu := (1146265451 / 2000000000))
    (Bl := (335773441 / 400000000)) (Bu := (424556351 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_249.2.1 endpoint_250.1 endpoint_249.2.2.2 endpoint_250.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_250 (v : ℝ) (hl : (953 / 3840) ≤ v) (hu : v ≤ (9799 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (953 / 3840)) (u := (9799 / 38400)) (xl := (1071161341 / 2000000000)) (xu := (554179139 / 1000000000))
    (Bl := (25943639 / 31250000)) (Bu := (1678867209 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_250.2.1 endpoint_251.1 endpoint_250.2.2.2 endpoint_251.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_251 (v : ℝ) (hl : (9799 / 38400) ≤ v) (hu : v ≤ (839 / 3200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9799 / 38400)) (u := (839 / 3200)) (xl := (1034629829 / 2000000000)) (xu := (1046056 / 1953125))
    (Bl := (410690233 / 500000000)) (Bu := (1660392899 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_251.2.1 endpoint_252.1 endpoint_251.2.2.2 endpoint_252.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_252 (v : ℝ) (hl : (839 / 3200) ≤ v) (hu : v ≤ (10337 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (839 / 3200)) (u := (10337 / 38400)) (xl := (99872229 / 200000000)) (xu := (129328729 / 250000000))
    (Bl := (1625933243 / 2000000000)) (Bu := (328552187 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_252.2.1 endpoint_253.1 endpoint_252.2.2.2 endpoint_253.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_253 (v : ℝ) (hl : (10337 / 38400) ≤ v) (hu : v ≤ (5303 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10337 / 38400)) (u := (5303 / 19200)) (xl := (96340029 / 200000000)) (xu := (998722293 / 2000000000))
    (Bl := (1609874869 / 2000000000)) (Bu := (812966623 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_253.2.1 endpoint_254.1 endpoint_253.2.2.2 endpoint_254.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_254 (v : ℝ) (hl : (5303 / 19200) ≤ v) (hu : v ≤ (145 / 512)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5303 / 19200)) (u := (145 / 512)) (xl := (185725621 / 400000000)) (xu := (963400293 / 2000000000))
    (Bl := (797276829 / 1000000000)) (Bu := (201234359 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_254.2.1 endpoint_255.1 endpoint_254.2.2.2 endpoint_255.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_255 (v : ℝ) (hl : (145 / 512) ≤ v) (hu : v ≤ (1393 / 4800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (145 / 512)) (u := (1393 / 4800)) (xl := (447186221 / 1000000000)) (xu := (232157027 / 500000000))
    (Bl := (1579940001 / 2000000000)) (Bu := (1594553661 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_255.2.1 endpoint_256.1 endpoint_255.2.2.2 endpoint_256.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_256 (v : ℝ) (hl : (1393 / 4800) ≤ v) (hu : v ≤ (11413 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1393 / 4800)) (u := (11413 / 38400)) (xl := (86060221 / 200000000)) (xu := (178874489 / 400000000))
    (Bl := (1566006593 / 2000000000)) (Bu := (394985001 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_256.2.1 endpoint_257.1 endpoint_256.2.2.2 endpoint_257.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_257 (v : ℝ) (hl : (11413 / 38400) ≤ v) (hu : v ≤ (1947 / 6400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11413 / 38400)) (u := (1947 / 6400)) (xl := (413644149 / 1000000000)) (xu := (860602213 / 2000000000))
    (Bl := (1552728227 / 2000000000)) (Bu := (391501649 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_257.2.1 endpoint_258.1 endpoint_257.2.2.2 endpoint_258.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_258 (v : ℝ) (hl : (1947 / 6400) ≤ v) (hu : v ≤ (11951 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1947 / 6400)) (u := (11951 / 38400)) (xl := (12412553 / 31250000)) (xu := (827288301 / 2000000000))
    (Bl := (1540081611 / 2000000000)) (Bu := (155272823 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_258.2.1 endpoint_259.1 endpoint_258.2.2.2 endpoint_259.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_259 (v : ℝ) (hl : (11951 / 38400) ≤ v) (hu : v ≤ (611 / 1920)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11951 / 38400)) (u := (611 / 1920)) (xl := (152384361 / 400000000)) (xu := (158880679 / 400000000))
    (Bl := (382011301 / 500000000)) (Bu := (770040807 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_259.2.1 endpoint_260.1 endpoint_259.2.2.2 endpoint_260.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_260 (v : ℝ) (hl : (611 / 1920) ≤ v) (hu : v ≤ (4163 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (611 / 1920)) (u := (4163 / 12800)) (xl := (729819331 / 2000000000)) (xu := (47620113 / 125000000))
    (Bl := (47393721 / 62500000)) (Bu := (1528045207 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_260.2.1 endpoint_261.1 endpoint_260.2.2.2 endpoint_261.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_261 (v : ℝ) (hl : (4163 / 12800) ≤ v) (hu : v ≤ (6379 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4163 / 12800)) (u := (6379 / 19200)) (xl := (139614621 / 400000000)) (xu := (364909667 / 1000000000))
    (Bl := (37643119 / 50000000)) (Bu := (60663963 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_261.2.1 endpoint_262.1 endpoint_261.2.2.2 endpoint_262.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_262 (v : ℝ) (hl : (6379 / 19200) ≤ v) (hu : v ≤ (13027 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6379 / 19200)) (u := (13027 / 38400)) (xl := (41666343 / 125000000)) (xu := (174518277 / 500000000))
    (Bl := (59816207 / 80000000)) (Bu := (1505724763 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_262.2.1 endpoint_263.1 endpoint_262.2.2.2 endpoint_263.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_263 (v : ℝ) (hl : (13027 / 38400) ≤ v) (hu : v ≤ (277 / 800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13027 / 38400)) (u := (277 / 800)) (xl := (158890989 / 500000000)) (xu := (666661491 / 2000000000))
    (Bl := (1485624483 / 2000000000)) (Bu := (747702589 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_263.2.1 endpoint_264.1 endpoint_263.2.2.2 endpoint_264.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


