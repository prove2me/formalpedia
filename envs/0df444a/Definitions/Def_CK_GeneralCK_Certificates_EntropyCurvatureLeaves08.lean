-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves08
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:56:45.428889+00:00
-- url     : https://prove2.me/theorems/91230a29-702a-4bee-bff8-a9e9d9b406e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves08` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves08` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves08` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves08 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves08.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_192 (v : ℝ) (hl : (19481 / 307200) ≤ v) (hu : v ≤ (395 / 6144)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (19481 / 307200)) (u := (395 / 6144)) (xl := (1338947719 / 1000000000)) (xu := (67313617 / 50000000))
    (Bl := (2810795577 / 2000000000)) (Bu := (2823574063 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_192.2.1 endpoint_193.1 endpoint_192.2.2.2 endpoint_193.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_193 (v : ℝ) (hl : (395 / 6144) ≤ v) (hu : v ≤ (6673 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (395 / 6144)) (u := (6673 / 102400)) (xl := (1331715427 / 1000000000)) (xu := (2677895443 / 2000000000))
    (Bl := (2798203499 / 2000000000)) (Bu := (1405397791 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_193.2.1 endpoint_194.1 endpoint_193.2.2.2 endpoint_194.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_194 (v : ℝ) (hl : (6673 / 102400) ≤ v) (hu : v ≤ (317 / 4800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6673 / 102400)) (u := (317 / 4800)) (xl := (165571623 / 125000000)) (xu := (2663430859 / 2000000000))
    (Bl := (2785792873 / 2000000000)) (Bu := (174887719 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_194.2.1 endpoint_195.1 endpoint_194.2.2.2 endpoint_195.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_195 (v : ℝ) (hl : (317 / 4800) ≤ v) (hu : v ≤ (20557 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (317 / 4800)) (u := (20557 / 307200)) (xl := (2635036021 / 2000000000)) (xu := (2649145973 / 2000000000))
    (Bl := (1386779473 / 1000000000)) (Bu := (1392896439 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_195.2.1 endpoint_196.1 endpoint_195.2.2.2 endpoint_196.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_196 (v : ℝ) (hl : (20557 / 307200) ≤ v) (hu : v ≤ (3471 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (20557 / 307200)) (u := (3471 / 51200)) (xl := (65527411 / 50000000)) (xu := (1317518013 / 1000000000))
    (Bl := (552299429 / 400000000)) (Bu := (2773558951 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_196.2.1 endpoint_197.1 endpoint_196.2.2.2 endpoint_197.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_197 (v : ℝ) (hl : (3471 / 51200) ≤ v) (hu : v ≤ (4219 / 61440)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3471 / 51200)) (u := (4219 / 61440)) (xl := (2607322829 / 2000000000)) (xu := (524219289 / 400000000))
    (Bl := (1374801539 / 1000000000)) (Bu := (55229943 / 40000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_197.2.1 endpoint_198.1 endpoint_197.2.2.2 endpoint_198.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_198 (v : ℝ) (hl : (4219 / 61440) ≤ v) (hu : v ≤ (5341 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4219 / 61440)) (u := (5341 / 76800)) (xl := (518742191 / 400000000)) (xu := (1303661417 / 1000000000))
    (Bl := (1368936259 / 1000000000)) (Bu := (2749603083 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_198.2.1 endpoint_199.1 endpoint_198.2.2.2 endpoint_199.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_199 (v : ℝ) (hl : (5341 / 76800) ≤ v) (hu : v ≤ (7211 / 102400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5341 / 76800)) (u := (7211 / 102400)) (xl := (645064187 / 500000000)) (xu := (32421387 / 25000000))
    (Bl := (545260279 / 400000000)) (Bu := (2737872523 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_199.2.1 endpoint_200.1 endpoint_199.2.2.2 endpoint_200.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_200 (v : ℝ) (hl : (7211 / 102400) ≤ v) (hu : v ≤ (10951 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (7211 / 102400)) (u := (10951 / 153600)) (xl := (10027173 / 7812500)) (xu := (2580256753 / 2000000000))
    (Bl := (542977159 / 400000000)) (Bu := (13631507 / 10000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_200.2.1 endpoint_201.1 endpoint_200.2.2.2 endpoint_201.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_201 (v : ℝ) (hl : (10951 / 153600) ≤ v) (hu : v ≤ (187 / 2560)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10951 / 153600)) (u := (187 / 2560)) (xl := (635200409 / 500000000)) (xu := (2566956293 / 2000000000))
    (Bl := (2692506199 / 2000000000)) (Bu := (13574429 / 10000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_201.2.1 endpoint_202.1 endpoint_201.2.2.2 endpoint_202.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_202 (v : ℝ) (hl : (187 / 2560) ≤ v) (hu : v ≤ (11489 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (187 / 2560)) (u := (11489 / 153600)) (xl := (157201149 / 125000000)) (xu := (2540801641 / 2000000000))
    (Bl := (2670705141 / 2000000000)) (Bu := (673126551 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_202.2.1 endpoint_203.1 endpoint_202.2.2.2 endpoint_203.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_203 (v : ℝ) (hl : (11489 / 153600) ≤ v) (hu : v ≤ (5879 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (11489 / 153600)) (u := (5879 / 76800)) (xl := (24901799 / 20000000)) (xu := (2515218389 / 2000000000))
    (Bl := (2649456017 / 2000000000)) (Bu := (1335352573 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_203.2.1 endpoint_204.1 endpoint_203.2.2.2 endpoint_204.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_204 (v : ℝ) (hl : (5879 / 76800) ≤ v) (hu : v ≤ (4009 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5879 / 76800)) (u := (4009 / 51200)) (xl := (30820767 / 25000000)) (xu := (498035981 / 400000000))
    (Bl := (2628734031 / 2000000000)) (Bu := (1324728011 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_204.2.1 endpoint_205.1 endpoint_204.2.2.2 endpoint_205.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_205 (v : ℝ) (hl : (4009 / 51200) ≤ v) (hu : v ≤ (1537 / 19200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4009 / 51200)) (u := (1537 / 19200)) (xl := (2441639589 / 2000000000)) (xu := (493132273 / 400000000))
    (Bl := (1304258017 / 1000000000)) (Bu := (657183509 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_205.2.1 endpoint_206.1 endpoint_205.2.2.2 endpoint_206.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_206 (v : ℝ) (hl : (1537 / 19200) ≤ v) (hu : v ≤ (2513 / 30720)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1537 / 19200)) (u := (2513 / 30720)) (xl := (2418092913 / 2000000000)) (xu := (1220819797 / 1000000000))
    (Bl := (1294390191 / 1000000000)) (Bu := (2608516039 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_206.2.1 endpoint_207.1 endpoint_206.2.2.2 endpoint_207.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_207 (v : ℝ) (hl : (2513 / 30720) ≤ v) (hu : v ≤ (2139 / 25600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2513 / 30720)) (u := (2139 / 25600)) (xl := (479000207 / 400000000)) (xu := (1209046459 / 1000000000))
    (Bl := (1284753401 / 1000000000)) (Bu := (2588780387 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_207.2.1 endpoint_208.1 endpoint_207.2.2.2 endpoint_208.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_208 (v : ℝ) (hl : (2139 / 25600) ≤ v) (hu : v ≤ (13103 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2139 / 25600)) (u := (13103 / 153600)) (xl := (1186172461 / 1000000000)) (xu := (29937513 / 25000000))
    (Bl := (2550676291 / 2000000000)) (Bu := (2569506807 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_208.2.1 endpoint_209.1 endpoint_208.2.2.2 endpoint_209.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_209 (v : ℝ) (hl : (13103 / 153600) ≤ v) (hu : v ≤ (3343 / 38400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13103 / 153600)) (u := (3343 / 38400)) (xl := (1175053349 / 1000000000)) (xu := (2372344927 / 2000000000))
    (Bl := (2532271001 / 2000000000)) (Bu := (318834537 / 250000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_209.2.1 endpoint_210.1 endpoint_209.2.2.2 endpoint_210.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_210 (v : ℝ) (hl : (3343 / 38400) ≤ v) (hu : v ≤ (4547 / 51200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3343 / 38400)) (u := (4547 / 51200)) (xl := (582067389 / 500000000)) (xu := (2350106703 / 2000000000))
    (Bl := (2514274153 / 2000000000)) (Bu := (1266135503 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_210.2.1 endpoint_211.1 endpoint_210.2.2.2 endpoint_211.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_211 (v : ℝ) (hl : (4547 / 51200) ≤ v) (hu : v ≤ (1391 / 15360)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4547 / 51200)) (u := (1391 / 15360)) (xl := (1153408837 / 1000000000)) (xu := (2328269561 / 2000000000))
    (Bl := (2496669951 / 2000000000)) (Bu := (1257137079 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_211.2.1 endpoint_212.1 endpoint_211.2.2.2 endpoint_212.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_212 (v : ℝ) (hl : (1391 / 15360) ≤ v) (hu : v ≤ (14179 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1391 / 15360)) (u := (14179 / 153600)) (xl := (2285736133 / 2000000000)) (xu := (2306817679 / 2000000000))
    (Bl := (247944351 / 200000000)) (Bu := (624167489 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_212.2.1 endpoint_213.1 endpoint_212.2.2.2 endpoint_213.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_213 (v : ℝ) (hl : (14179 / 153600) ≤ v) (hu : v ≤ (301 / 3200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14179 / 153600)) (u := (301 / 3200)) (xl := (1132505431 / 1000000000)) (xu := (1142868069 / 1000000000))
    (Bl := (2462580781 / 2000000000)) (Bu := (495888703 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_213.2.1 endpoint_214.1 endpoint_213.2.2.2 endpoint_214.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_214 (v : ℝ) (hl : (301 / 3200) ≤ v) (hu : v ≤ (14717 / 153600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (301 / 3200)) (u := (14717 / 153600)) (xl := (2244628561 / 2000000000)) (xu := (2265010867 / 2000000000))
    (Bl := (1223034249 / 1000000000)) (Bu := (1231290393 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_214.2.1 endpoint_215.1 endpoint_214.2.2.2 endpoint_215.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_215 (v : ℝ) (hl : (14717 / 153600) ≤ v) (hu : v ≤ (7493 / 76800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (14717 / 153600)) (u := (7493 / 76800)) (xl := (1112288329 / 1000000000)) (xu := (1122314283 / 1000000000))
    (Bl := (485978823 / 400000000)) (Bu := (2446068503 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_215.2.1 endpoint_216.1 endpoint_215.2.2.2 endpoint_216.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


