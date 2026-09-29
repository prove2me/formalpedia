-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLeaves00
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLeaves00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:55:55.50598+00:00
-- url     : https://prove2.me/theorems/23fe4394-57a2-482e-b6dd-04a230f0b9b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLeaves00` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLeaves00` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLeaves00` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLeaves00 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLeaves00.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs

namespace GeneralCK.Certificates.EntropyCurvature
open GeneralCK.EntropyCurvature

theorem leaf_0 (v : ℝ) (hl : (1 / 100) ≤ v) (hu : v ≤ (49421 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (1 / 100)) (u := (49421 / 4915200)) (xl := (2294803333 / 1000000000)) (xu := (2297559927 / 1000000000))
    (Bl := (4609817903 / 2000000000)) (Bu := (184608821 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_0.2.1 endpoint_1.1 endpoint_0.2.2.2 endpoint_1.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_1 (v : ℝ) (hl : (49421 / 4915200) ≤ v) (hu : v ≤ (4969 / 491520)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (49421 / 4915200)) (u := (4969 / 491520)) (xl := (458412311 / 200000000)) (xu := (2294803337 / 1000000000))
    (Bl := (4604444917 / 2000000000)) (Bu := (4609817911 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_1.2.1 endpoint_2.1 endpoint_1.2.2.2 endpoint_2.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_2 (v : ℝ) (hl : (4969 / 491520) ≤ v) (hu : v ≤ (16653 / 1638400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (4969 / 491520)) (u := (16653 / 1638400)) (xl := (2289334429 / 1000000000)) (xu := (2292061559 / 1000000000))
    (Bl := (4599101243 / 2000000000)) (Bu := (184177797 / 80000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_2.2.1 endpoint_3.1 endpoint_2.2.2.2 endpoint_3.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_3 (v : ℝ) (hl : (16653 / 1638400) ≤ v) (hu : v ≤ (12557 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (16653 / 1638400)) (u := (12557 / 1228800)) (xl := (914648719 / 400000000)) (xu := (2289334433 / 1000000000))
    (Bl := (1148446641 / 500000000)) (Bu := (4599101251 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_3.2.1 endpoint_4.1 endpoint_3.2.2.2 endpoint_4.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_4 (v : ℝ) (hl : (12557 / 1228800) ≤ v) (hu : v ≤ (50497 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (12557 / 1228800)) (u := (50497 / 4915200)) (xl := (4567847011 / 2000000000)) (xu := (4573243603 / 2000000000))
    (Bl := (458850057 / 200000000)) (Bu := (1148446643 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_4.2.1 endpoint_5.1 endpoint_4.2.2.2 endpoint_5.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_5 (v : ℝ) (hl : (50497 / 4915200) ≤ v) (hu : v ≤ (8461 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (50497 / 4915200)) (u := (8461 / 819200)) (xl := (4562478803 / 2000000000)) (xu := (4567847019 / 2000000000))
    (Bl := (1145810739 / 500000000)) (Bu := (2294250289 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_5.2.1 endpoint_6.1 endpoint_5.2.2.2 endpoint_6.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_6 (v : ℝ) (hl : (8461 / 819200) ≤ v) (hu : v ≤ (10207 / 983040)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8461 / 819200)) (u := (10207 / 983040)) (xl := (455713867 / 200000000)) (xu := (4562478811 / 2000000000))
    (Bl := (183120537 / 80000000)) (Bu := (1145810741 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_6.2.1 endpoint_7.1 endpoint_6.2.2.2 endpoint_7.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_7 (v : ℝ) (hl : (10207 / 983040) ≤ v) (hu : v ≤ (6413 / 614400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (10207 / 983040)) (u := (6413 / 614400)) (xl := (1137956579 / 500000000)) (xu := (2278569339 / 1000000000))
    (Bl := (4572811679 / 2000000000)) (Bu := (4578013433 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_7.2.1 endpoint_8.1 endpoint_7.2.2.2 endpoint_8.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_8 (v : ℝ) (hl : (6413 / 614400) ≤ v) (hu : v ≤ (17191 / 1638400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (6413 / 614400)) (u := (17191 / 1638400)) (xl := (4546541451 / 2000000000)) (xu := (1137956581 / 500000000))
    (Bl := (1141909357 / 500000000)) (Bu := (4572811687 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_8.2.1 endpoint_9.1 endpoint_8.2.2.2 endpoint_9.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_9 (v : ℝ) (hl : (17191 / 1638400) ≤ v) (hu : v ≤ (25921 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17191 / 1638400)) (u := (25921 / 2457600)) (xl := (4541283789 / 2000000000)) (xu := (4546541459 / 2000000000))
    (Bl := (2281245193 / 1000000000)) (Bu := (1141909359 / 500000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_9.2.1 endpoint_10.1 endpoint_9.2.2.2 endpoint_10.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_10 (v : ℝ) (hl : (25921 / 2457600) ≤ v) (hu : v ≤ (52111 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (25921 / 2457600)) (u := (52111 / 4915200)) (xl := (4536053049 / 2000000000)) (xu := (4541283797 / 2000000000))
    (Bl := (142417821 / 62500000)) (Bu := (2281245197 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_10.2.1 endpoint_11.1 endpoint_10.2.2.2 endpoint_11.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_11 (v : ℝ) (hl : (52111 / 4915200) ≤ v) (hu : v ≤ (873 / 81920)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (52111 / 4915200)) (u := (873 / 81920)) (xl := (4530848953 / 2000000000)) (xu := (4536053057 / 2000000000))
    (Bl := (569034601 / 250000000)) (Bu := (113934257 / 50000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_11.2.1 endpoint_12.1 endpoint_11.2.2.2 endpoint_12.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_12 (v : ℝ) (hl : (873 / 81920) ≤ v) (hu : v ≤ (52649 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (873 / 81920)) (u := (52649 / 4915200)) (xl := (4525671227 / 2000000000)) (xu := (4530848961 / 2000000000))
    (Bl := (2273604861 / 1000000000)) (Bu := (284517301 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_12.2.1 endpoint_13.1 endpoint_12.2.2.2 endpoint_13.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_13 (v : ℝ) (hl : (52649 / 4915200) ≤ v) (hu : v ≤ (26459 / 2457600)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (52649 / 4915200)) (u := (26459 / 2457600)) (xl := (1130129901 / 500000000)) (xu := (905134247 / 400000000))
    (Bl := (4542168743 / 2000000000)) (Bu := (454720973 / 200000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_13.2.1 endpoint_14.1 endpoint_13.2.2.2 endpoint_14.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_14 (v : ℝ) (hl : (26459 / 2457600) ≤ v) (hu : v ≤ (17729 / 1638400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (26459 / 2457600)) (u := (17729 / 1638400)) (xl := (4515393819 / 2000000000)) (xu := (1130129903 / 500000000))
    (Bl := (567144201 / 250000000)) (Bu := (4542168751 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_14.2.1 endpoint_15.1 endpoint_14.2.2.2 endpoint_15.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_15 (v : ℝ) (hl : (17729 / 1638400) ≤ v) (hu : v ≤ (3341 / 307200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (17729 / 1638400)) (u := (3341 / 307200)) (xl := (451029361 / 200000000)) (xu := (4515393827 / 2000000000))
    (Bl := (4532164057 / 2000000000)) (Bu := (283572101 / 125000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_15.2.1 endpoint_16.1 endpoint_15.2.2.2 endpoint_16.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_16 (v : ℝ) (hl : (3341 / 307200) ≤ v) (hu : v ≤ (2149 / 196608)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (3341 / 307200)) (u := (2149 / 196608)) (xl := (2252609361 / 1000000000)) (xu := (2255146809 / 1000000000))
    (Bl := (4527199831 / 2000000000)) (Bu := (906432813 / 400000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_16.2.1 endpoint_17.1 endpoint_16.2.2.2 endpoint_17.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_17 (v : ℝ) (hl : (2149 / 196608) ≤ v) (hu : v ≤ (8999 / 819200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (2149 / 196608)) (u := (8999 / 819200)) (xl := (45001689 / 20000000)) (xu := (450521873 / 200000000))
    (Bl := (4522260679 / 2000000000)) (Bu := (4527199839 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_17.2.1 endpoint_18.1 endpoint_17.2.2.2 endpoint_18.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_18 (v : ℝ) (hl : (8999 / 819200) ≤ v) (hu : v ≤ (54263 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (8999 / 819200)) (u := (54263 / 4915200)) (xl := (2247571949 / 1000000000)) (xu := (1125042227 / 500000000))
    (Bl := (4517346351 / 2000000000)) (Bu := (4522260687 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_18.2.1 endpoint_19.1 endpoint_18.2.2.2 endpoint_19.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_19 (v : ℝ) (hl : (54263 / 4915200) ≤ v) (hu : v ≤ (13633 / 1228800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (54263 / 4915200)) (u := (13633 / 1228800)) (xl := (2245071733 / 1000000000)) (xu := (2247571953 / 1000000000))
    (Bl := (4512456601 / 2000000000)) (Bu := (4517346359 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_19.2.1 endpoint_20.1 endpoint_19.2.2.2 endpoint_20.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_20 (v : ℝ) (hl : (13633 / 1228800) ≤ v) (hu : v ≤ (18267 / 1638400)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (13633 / 1228800)) (u := (18267 / 1638400)) (xl := (2242583683 / 1000000000)) (xu := (2245071737 / 1000000000))
    (Bl := (4507591189 / 2000000000)) (Bu := (4512456609 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_20.2.1 endpoint_21.1 endpoint_20.2.2.2 endpoint_21.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_21 (v : ℝ) (hl : (18267 / 1638400) ≤ v) (hu : v ≤ (5507 / 491520)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (18267 / 1638400)) (u := (5507 / 491520)) (xl := (4480215357 / 2000000000)) (xu := (2242583687 / 1000000000))
    (Bl := (2251374937 / 1000000000)) (Bu := (4507591197 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_21.2.1 endpoint_22.1 endpoint_21.2.2.2 endpoint_22.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_22 (v : ℝ) (hl : (5507 / 491520) ≤ v) (hu : v ≤ (55339 / 4915200)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (5507 / 491520)) (u := (55339 / 4915200)) (xl := (559410901 / 250000000)) (xu := (896043073 / 400000000))
    (Bl := (4497932423 / 2000000000)) (Bu := (2251374941 / 1000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_22.2.1 endpoint_23.1 endpoint_22.2.2.2 endpoint_23.2.2.1
    (by norm_num) (by norm_num)

theorem leaf_23 (v : ℝ) (hl : (55339 / 4915200) ≤ v) (hu : v ≤ (2317 / 204800)) :
    0 < P v ∧ 0 < R v := by
  exact leaf_sound (l := (55339 / 4915200)) (u := (2317 / 204800)) (xl := (4470382683 / 2000000000)) (xu := (279705451 / 125000000))
    (Bl := (1123284651 / 500000000)) (Bu := (4497932431 / 2000000000)) (by norm_num) (by norm_num) hl hu (by norm_num) (by norm_num)
    endpoint_23.2.1 endpoint_24.1 endpoint_23.2.2.2 endpoint_24.2.2.1
    (by norm_num) (by norm_num)

end GeneralCK.Certificates.EntropyCurvature


