-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves00
-- name    : CK_GeneralCK_Certificates_MixedLeaves00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:17.158669+00:00
-- url     : https://prove2.me/theorems/93b530cb-d1ed-4421-ab0b-cc58e95d20ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves00` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves00` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves00` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves00 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves00.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_0 (v : ℝ) (hl : (1 / 22) ≤ v) (hu : v ≤ (403 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1 / 22)) (u := (403 / 8448))
    (a := (386380307 / 125000000)) (b := (48878947 / 1000000000)) (c := (3042748441 / 1000000000)) (d := (9304003 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_0.2 (by convert! log_c_1.2 using 1; norm_num)
    log_v_1.1 (by convert! log_c_0.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_1 (v : ℝ) (hl : (403 / 8448) ≤ v) (hu : v ≤ (211 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (403 / 8448)) (u := (211 / 4224))
    (a := (1521374223 / 500000000)) (b := (800679 / 15625000)) (c := (2996679689 / 1000000000)) (d := (24439473 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_1.2 (by convert! log_c_2.2 using 1; norm_num)
    log_v_2.1 (by convert! log_c_1.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_2 (v : ℝ) (hl : (211 / 4224) ≤ v) (hu : v ≤ (147 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (211 / 4224)) (u := (147 / 2816))
    (a := (1498339847 / 500000000)) (b := (104714 / 1953125)) (c := (23067501 / 7812500)) (d := (10248691 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_2.2 (by convert! log_c_3.2 using 1; norm_num)
    log_v_3.1 (by convert! log_c_2.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_3 (v : ℝ) (hl : (147 / 2816) ≤ v) (hu : v ≤ (115 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (147 / 2816)) (u := (115 / 2112))
    (a := (2952640133 / 1000000000)) (b := (874833 / 15625000)) (c := (1455229257 / 500000000)) (d := (53613567 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_3.2 (by convert! log_c_4.2 using 1; norm_num)
    log_v_4.1 (by convert! log_c_3.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_4 (v : ℝ) (hl : (115 / 2112) ≤ v) (hu : v ≤ (479 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (115 / 2112)) (u := (479 / 8448))
    (a := (2910458519 / 1000000000)) (b := (58370713 / 1000000000)) (c := (1434992203 / 500000000)) (d := (55989311 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_4.2 (by convert! log_c_5.2 using 1; norm_num)
    log_v_5.1 (by convert! log_c_4.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_5 (v : ℝ) (hl : (479 / 8448) ≤ v) (hu : v ≤ (83 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (479 / 8448)) (u := (83 / 1408))
    (a := (2869984411 / 1000000000)) (b := (60757799 / 1000000000)) (c := (1415542463 / 500000000)) (d := (7296339 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_5.2 (by convert! log_c_6.2 using 1; norm_num)
    log_v_6.1 (by convert! log_c_5.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_6 (v : ℝ) (hl : (83 / 1408) ≤ v) (hu : v ≤ (47 / 768)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (83 / 1408)) (u := (47 / 768))
    (a := (2831084931 / 1000000000)) (b := (15787649 / 250000000)) (c := (2793642129 / 1000000000)) (d := (30378899 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_6.2 (by convert! log_c_7.2 using 1; norm_num)
    log_v_7.1 (by convert! log_c_6.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_7 (v : ℝ) (hl : (47 / 768) ≤ v) (hu : v ≤ (67 / 1056)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (47 / 768)) (u := (67 / 1056))
    (a := (1396821067 / 500000000)) (b := (65549133 / 1000000000)) (c := (2757550843 / 1000000000)) (d := (12630119 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_7.2 (by convert! log_c_8.2 using 1; norm_num)
    log_v_8.1 (by convert! log_c_7.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_8 (v : ℝ) (hl : (67 / 1056) ≤ v) (hu : v ≤ (185 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (67 / 1056)) (u := (185 / 2816))
    (a := (2757550847 / 1000000000)) (b := (67953437 / 1000000000)) (c := (272271689 / 100000000)) (d := (16387283 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_8.2 (by convert! log_c_9.2 using 1; norm_num)
    log_v_9.1 (by convert! log_c_8.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_9 (v : ℝ) (hl : (185 / 2816) ≤ v) (hu : v ≤ (287 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (185 / 2816)) (u := (287 / 4224))
    (a := (1361358447 / 500000000)) (b := (14072707 / 200000000)) (c := (2689055607 / 1000000000)) (d := (16988359 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_9.2 (by convert! log_c_10.2 using 1; norm_num)
    log_v_10.1 (by convert! log_c_9.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_10 (v : ℝ) (hl : (287 / 4224) ≤ v) (hu : v ≤ (593 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (287 / 4224)) (u := (593 / 8448))
    (a := (2689055611 / 1000000000)) (b := (1137179 / 15625000)) (c := (531298121 / 200000000)) (d := (35181767 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_10.2 (by convert! log_c_11.2 using 1; norm_num)
    log_v_11.1 (by convert! log_c_10.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_11 (v : ℝ) (hl : (593 / 8448) ≤ v) (hu : v ≤ (51 / 704)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (593 / 8448)) (u := (51 / 704))
    (a := (2656490609 / 1000000000)) (b := (75201227 / 1000000000)) (c := (2624952721 / 1000000000)) (d := (14555891 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_11.2 (by convert! log_c_12.2 using 1; norm_num)
    log_v_12.1 (by convert! log_c_11.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_12 (v : ℝ) (hl : (51 / 704) ≤ v) (hu : v ≤ (631 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (51 / 704)) (u := (631 / 8448))
    (a := (104998109 / 40000000)) (b := (38814439 / 500000000)) (c := (2594379141 / 1000000000)) (d := (37600613 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_12.2 (by convert! log_c_13.2 using 1; norm_num)
    log_v_13.1 (by convert! log_c_12.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_13 (v : ℝ) (hl : (631 / 8448) ≤ v) (hu : v ≤ (325 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (631 / 8448)) (u := (325 / 4224))
    (a := (518875829 / 200000000)) (b := (80062437 / 1000000000)) (c := (2564712641 / 1000000000)) (d := (77628877 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_13.2 (by convert! log_c_14.2 using 1; norm_num)
    log_v_14.1 (by convert! log_c_13.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_14 (v : ℝ) (hl : (325 / 4224) ≤ v) (hu : v ≤ (223 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (325 / 4224)) (u := (223 / 2816))
    (a := (512942529 / 200000000)) (b := (20625483 / 250000000)) (c := (158493809 / 62500000)) (d := (20015609 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_14.2 (by convert! log_c_15.2 using 1; norm_num)
    log_v_15.1 (by convert! log_c_14.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_15 (v : ℝ) (hl : (223 / 2816) ≤ v) (hu : v ≤ (43 / 528)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (223 / 2816)) (u := (43 / 528))
    (a := (633975237 / 250000000)) (b := (84947393 / 1000000000)) (c := (1253948083 / 500000000)) (d := (82501931 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_15.2 (by convert! log_c_16.2 using 1; norm_num)
    log_v_16.1 (by convert! log_c_15.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


