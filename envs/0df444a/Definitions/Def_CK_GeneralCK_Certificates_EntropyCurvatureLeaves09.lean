-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves09
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:58:59.71741+00:00
-- url     : https://prove2.me/theorems/26efd412-e5b1-4528-9d10-4a3db741f3b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves09` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves09` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves09` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves09 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves09.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_216 (v : ℝ) (hl : (7493 / 76800) ≤ v) (hu : v ≤ (1017 / 10240)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7493 / 76800)) (u := (1017 / 10240)) (xl := (551210811 / 500000000)) (xu := (2224576663 / 2000000000))
    (Bl := (482809151 / 400000000)) (Bu := (60747353 / 50000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_216.2.1 endpoint_217.1 endpoint_216.2.2.2 endpoint_217.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_217 (v : ℝ) (hl : (1017 / 10240) ≤ v) (hu : v ≤ (3881 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1017 / 10240)) (u := (3881 / 38400)) (xl := (1092708521 / 1000000000)) (xu := (2204843249 / 2000000000))
    (Bl := (2398512167 / 2000000000)) (Bu := (7543893 / 6250000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_217.2.1 endpoint_218.1 endpoint_217.2.2.2 endpoint_218.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_218 (v : ℝ) (hl : (3881 / 38400) ≤ v) (hu : v ≤ (15793 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3881 / 38400)) (u := (15793 / 153600)) (xl := (2166287349 / 2000000000)) (xu := (2185417047 / 2000000000))
    (Bl := (59582067 / 50000000)) (Bu := (599628043 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_218.2.1 endpoint_219.1 endpoint_218.2.2.2 endpoint_219.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_219 (v : ℝ) (hl : (15793 / 153600) ≤ v) (hu : v ≤ (2677 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (15793 / 153600)) (u := (2677 / 25600)) (xl := (1073722003 / 1000000000)) (xu := (1083143677 / 1000000000))
    (Bl := (2368347163 / 2000000000)) (Bu := (476656537 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_219.2.1 endpoint_220.1 endpoint_219.2.2.2 endpoint_220.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_220 (v : ℝ) (hl : (2677 / 25600) ≤ v) (hu : v ≤ (16331 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2677 / 25600)) (u := (16331 / 153600)) (xl := (2128877359 / 2000000000)) (xu := (2147444011 / 2000000000))
    (Bl := (294211999 / 250000000)) (Bu := (74010849 / 62500000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_220.2.1 endpoint_221.1 endpoint_220.2.2.2 endpoint_221.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_221 (v : ℝ) (hl : (16331 / 153600) ≤ v) (hu : v ≤ (83 / 768)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (16331 / 153600)) (u := (83 / 768)) (xl := (527644557 / 500000000)) (xu := (532219341 / 500000000))
    (Bl := (2339320017 / 2000000000)) (Bu := (2353695997 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_221.2.1 endpoint_222.1 endpoint_221.2.2.2 endpoint_222.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_222 (v : ℝ) (hl : (83 / 768) ≤ v) (hu : v ≤ (8569 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (83 / 768)) (u := (8569 / 76800)) (xl := (518686991 / 500000000)) (xu := (2110578233 / 2000000000))
    (Bl := (2311359231 / 2000000000)) (Bu := (1169660011 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_222.2.1 endpoint_223.1 endpoint_222.2.2.2 endpoint_223.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_223 (v : ℝ) (hl : (8569 / 76800) ≤ v) (hu : v ≤ (1473 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8569 / 76800)) (u := (1473 / 12800)) (xl := (509972029 / 500000000)) (xu := (2074747969 / 2000000000))
    (Bl := (456879989 / 400000000)) (Bu := (577839809 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_223.2.1 endpoint_224.1 endpoint_223.2.2.2 endpoint_224.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_224 (v : ℝ) (hl : (1473 / 12800) ≤ v) (hu : v ≤ (9107 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1473 / 12800)) (u := (9107 / 76800)) (xl := (1002969713 / 1000000000)) (xu := (2039888121 / 2000000000))
    (Bl := (2258383151 / 2000000000)) (Bu := (45687999 / 40000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_224.2.1 endpoint_225.1 endpoint_224.2.2.2 endpoint_225.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_225 (v : ℝ) (hl : (9107 / 76800) ≤ v) (hu : v ≤ (293 / 2400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (9107 / 76800)) (u := (293 / 2400)) (xl := (986423901 / 1000000000)) (xu := (2005939431 / 2000000000))
    (Bl := (2233255007 / 2000000000)) (Bu := (564595789 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_225.2.1 endpoint_226.1 endpoint_225.2.2.2 endpoint_226.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_226 (v : ℝ) (hl : (293 / 2400) ≤ v) (hu : v ≤ (643 / 5120)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (293 / 2400)) (u := (643 / 5120)) (xl := (485140933 / 500000000)) (xu := (1972847807 / 2000000000))
    (Bl := (2208966251 / 2000000000)) (Bu := (558313753 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_226.2.1 endpoint_227.1 endpoint_226.2.2.2 endpoint_227.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_227 (v : ℝ) (hl : (643 / 5120) ≤ v) (hu : v ≤ (4957 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (643 / 5120)) (u := (4957 / 38400)) (xl := (119315111 / 125000000)) (xu := (242570467 / 250000000))
    (Bl := (2185471701 / 2000000000)) (Bu := (441793251 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_227.2.1 endpoint_228.1 endpoint_227.2.2.2 endpoint_228.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_228 (v : ℝ) (hl : (4957 / 38400) ≤ v) (hu : v ≤ (10183 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4957 / 38400)) (u := (10183 / 76800)) (xl := (375648027 / 400000000)) (xu := (95452089 / 100000000))
    (Bl := (1081364907 / 1000000000)) (Bu := (437094341 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_228.2.1 endpoint_229.1 endpoint_228.2.2.2 endpoint_229.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_229 (v : ℝ) (hl : (10183 / 76800) ≤ v) (hu : v ≤ (871 / 6400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10183 / 76800)) (u := (871 / 6400)) (xl := (1848120267 / 2000000000)) (xu := (1878240139 / 2000000000))
    (Bl := (1070351157 / 1000000000)) (Bu := (1081364909 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_229.2.1 endpoint_230.1 endpoint_229.2.2.2 endpoint_230.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_230 (v : ℝ) (hl : (871 / 6400) ≤ v) (hu : v ≤ (10721 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (871 / 6400)) (u := (10721 / 76800)) (xl := (1818646559 / 2000000000)) (xu := (1848120271 / 2000000000))
    (Bl := (264919231 / 250000000)) (Bu := (1070351159 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_230.2.1 endpoint_231.1 endpoint_230.2.2.2 endpoint_231.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_231 (v : ℝ) (hl : (10721 / 76800) ≤ v) (hu : v ≤ (1099 / 7680)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10721 / 76800)) (u := (1099 / 7680)) (xl := (111861627 / 125000000)) (xu := (1818646563 / 2000000000))
    (Bl := (2098651707 / 2000000000)) (Bu := (529838463 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_231.2.1 endpoint_232.1 endpoint_231.2.2.2 endpoint_232.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_232 (v : ℝ) (hl : (1099 / 7680) ≤ v) (hu : v ≤ (3753 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1099 / 7680)) (u := (3753 / 25600)) (xl := (176150809 / 200000000)) (xu := (447446509 / 500000000))
    (Bl := (2078565569 / 2000000000)) (Bu := (2098651711 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_232.2.1 endpoint_233.1 endpoint_232.2.2.2 endpoint_233.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_233 (v : ℝ) (hl : (3753 / 25600) ≤ v) (hu : v ≤ (1441 / 9600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3753 / 25600)) (u := (1441 / 9600)) (xl := (1733784293 / 2000000000)) (xu := (880754047 / 1000000000))
    (Bl := (1029533633 / 1000000000)) (Bu := (2078565573 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_233.2.1 endpoint_234.1 endpoint_233.2.2.2 endpoint_234.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_234 (v : ℝ) (hl : (1441 / 9600) ≤ v) (hu : v ≤ (11797 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1441 / 9600)) (u := (11797 / 76800)) (xl := (1706588159 / 2000000000)) (xu := (1733784297 / 2000000000))
    (Bl := (1020065297 / 1000000000)) (Bu := (205906727 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_234.2.1 endpoint_235.1 endpoint_234.2.2.2 endpoint_235.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_235 (v : ℝ) (hl : (11797 / 76800) ≤ v) (hu : v ≤ (2011 / 12800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11797 / 76800)) (u := (2011 / 12800)) (xl := (209986873 / 250000000)) (xu := (1706588163 / 2000000000))
    (Bl := (2021731133 / 2000000000)) (Bu := (1020065299 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_235.2.1 endpoint_236.1 endpoint_235.2.2.2 endpoint_236.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_236 (v : ℝ) (hl : (2011 / 12800) ≤ v) (hu : v ≤ (2467 / 15360)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2011 / 12800)) (u := (2467 / 15360)) (xl := (1653681689 / 2000000000)) (xu := (419973747 / 500000000))
    (Bl := (250480761 / 250000000)) (Bu := (2021731137 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_236.2.1 endpoint_237.1 endpoint_236.2.2.2 endpoint_237.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_237 (v : ℝ) (hl : (2467 / 15360) ≤ v) (hu : v ≤ (3151 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2467 / 15360)) (u := (3151 / 19200)) (xl := (813963339 / 1000000000)) (xu := (1653681693 / 2000000000))
    (Bl := (1986454151 / 2000000000)) (Bu := (500961523 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_237.2.1 endpoint_238.1 endpoint_237.2.2.2 endpoint_238.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_238 (v : ℝ) (hl : (3151 / 19200) ≤ v) (hu : v ≤ (6571 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3151 / 19200)) (u := (6571 / 38400)) (xl := (788855897 / 1000000000)) (xu := (813963341 / 1000000000))
    (Bl := (390614213 / 400000000)) (Bu := (397290831 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_238.2.1 endpoint_239.1 endpoint_238.2.2.2 endpoint_239.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_239 (v : ℝ) (hl : (6571 / 38400) ≤ v) (hu : v ≤ (57 / 320)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6571 / 38400)) (u := (57 / 320)) (xl := (764551381 / 1000000000)) (xu := (788855899 / 1000000000))
    (Bl := (1921436689 / 2000000000)) (Bu := (1953071069 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_239.2.1 endpoint_240.1 endpoint_239.2.2.2 endpoint_240.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


