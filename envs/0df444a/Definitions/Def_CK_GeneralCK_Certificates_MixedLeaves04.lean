-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves04
-- name    : CK_GeneralCK_Certificates_MixedLeaves04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:40.841728+00:00
-- url     : https://prove2.me/theorems/fe428993-2057-40e0-80e6-a5ccbf29de1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves04.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_64 (v : ℝ) (hl : (25 / 132) ≤ v) (hu : v ≤ (1619 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (25 / 132)) (u := (1619 / 8448))
    (a := (1663926099 / 1000000000)) (b := (212751477 / 1000000000)) (c := (1652121051 / 1000000000)) (d := (6561659 / 31250000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_64.2 (by convert! log_c_65.2 using 1; norm_num)
    log_v_65.1 (by convert! log_c_64.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_65 (v : ℝ) (hl : (1619 / 8448) ≤ v) (hu : v ≤ (273 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1619 / 8448)) (u := (273 / 1408))
    (a := (826060527 / 500000000)) (b := (215537607 / 1000000000)) (c := (82022687 / 50000000)) (d := (53187869 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_65.2 (by convert! log_c_66.2 using 1; norm_num)
    log_v_66.1 (by convert! log_c_65.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_66 (v : ℝ) (hl : (273 / 1408) ≤ v) (hu : v ≤ (1657 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (273 / 1408)) (u := (1657 / 8448))
    (a := (1640453743 / 1000000000)) (b := (218331521 / 1000000000)) (c := (1628920987 / 1000000000)) (d := (107768803 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_66.2 (by convert! log_c_67.2 using 1; norm_num)
    log_v_67.1 (by convert! log_c_66.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_67 (v : ℝ) (hl : (1657 / 8448) ≤ v) (hu : v ≤ (419 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1657 / 8448)) (u := (419 / 2112))
    (a := (162892099 / 100000000)) (b := (221133263 / 1000000000)) (c := (1617519723 / 1000000000)) (d := (341143 / 1562500))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_67.2 (by convert! log_c_68.2 using 1; norm_num)
    log_v_68.1 (by convert! log_c_67.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_68 (v : ℝ) (hl : (419 / 2112) ≤ v) (hu : v ≤ (565 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (419 / 2112)) (u := (565 / 2816))
    (a := (808759863 / 500000000)) (b := (223942877 / 1000000000)) (c := (321249397 / 200000000)) (d := (110566631 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_68.2 (by convert! log_c_69.2 using 1; norm_num)
    log_v_69.1 (by convert! log_c_68.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_69 (v : ℝ) (hl : (565 / 2816) ≤ v) (hu : v ≤ (857 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (565 / 2816)) (u := (857 / 4224))
    (a := (401561747 / 250000000)) (b := (226760407 / 1000000000)) (c := (319019981 / 200000000)) (d := (55985719 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_69.2 (by convert! log_c_70.2 using 1; norm_num)
    log_v_70.1 (by convert! log_c_69.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_70 (v : ℝ) (hl : (857 / 4224) ≤ v) (hu : v ≤ (1733 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (857 / 4224)) (u := (1733 / 8448))
    (a := (398774977 / 250000000)) (b := (229585897 / 1000000000)) (c := (316815143 / 200000000)) (d := (113380203 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_70.2 (by convert! log_c_71.2 using 1; norm_num)
    log_v_71.1 (by convert! log_c_70.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_71 (v : ℝ) (hl : (1733 / 8448) ≤ v) (hu : v ≤ (73 / 352)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1733 / 8448)) (u := (73 / 352))
    (a := (792037859 / 500000000)) (b := (116209697 / 500000000)) (c := (1573171733 / 1000000000)) (d := (28698237 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_71.2 (by convert! log_c_72.2 using 1; norm_num)
    log_v_72.1 (by convert! log_c_71.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_72 (v : ℝ) (hl : (73 / 352) ≤ v) (hu : v ≤ (161 / 768)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (73 / 352)) (u := (161 / 768))
    (a := (196646467 / 125000000)) (b := (235260943 / 1000000000)) (c := (1562385367 / 1000000000)) (d := (232419393 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_72.2 (by convert! log_c_73.2 using 1; norm_num)
    log_v_73.1 (by convert! log_c_72.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_73 (v : ℝ) (hl : (161 / 768) ≤ v) (hu : v ≤ (895 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (161 / 768)) (u := (895 / 4224))
    (a := (156238537 / 100000000)) (b := (59527647 / 250000000)) (c := (310342821 / 200000000)) (d := (117630471 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_73.2 (by convert! log_c_74.2 using 1; norm_num)
    log_v_74.1 (by convert! log_c_73.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_74 (v : ℝ) (hl : (895 / 4224) ≤ v) (hu : v ≤ (603 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (895 / 4224)) (u := (603 / 2816))
    (a := (387928527 / 250000000)) (b := (120484189 / 500000000)) (c := (1541155519 / 1000000000)) (d := (238110587 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_74.2 (by convert! log_c_75.2 using 1; norm_num)
    log_v_75.1 (by convert! log_c_74.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_75 (v : ℝ) (hl : (603 / 2816) ≤ v) (hu : v ≤ (457 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (603 / 2816)) (u := (457 / 2112))
    (a := (770577761 / 500000000)) (b := (121917179 / 500000000)) (c := (382676813 / 250000000)) (d := (240968377 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_75.2 (by convert! log_c_76.2 using 1; norm_num)
    log_v_76.1 (by convert! log_c_75.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_76 (v : ℝ) (hl : (457 / 2112) ≤ v) (hu : v ≤ (1847 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (457 / 2112)) (u := (1847 / 8448))
    (a := (306141451 / 200000000)) (b := (9868343 / 40000000)) (c := (95022939 / 62500000)) (d := (243834357 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_76.2 (by convert! log_c_77.2 using 1; norm_num)
    log_v_77.1 (by convert! log_c_76.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_77 (v : ℝ) (hl : (1847 / 8448) ≤ v) (hu : v ≤ (311 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1847 / 8448)) (u := (311 / 1408))
    (a := (1520367027 / 1000000000)) (b := (249591077 / 1000000000)) (c := (1510132623 / 1000000000)) (d := (123354287 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_77.2 (by convert! log_c_78.2 using 1; norm_num)
    log_v_78.1 (by convert! log_c_77.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_78 (v : ℝ) (hl : (311 / 1408) ≤ v) (hu : v ≤ (1885 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (311 / 1408)) (u := (1885 / 8448))
    (a := (755066313 / 500000000)) (b := (31560239 / 125000000)) (c := (93750119 / 62500000)) (d := (62397769 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_78.2 (by convert! log_c_79.2 using 1; norm_num)
    log_v_79.1 (by convert! log_c_78.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_79 (v : ℝ) (hl : (1885 / 8448) ≤ v) (hu : v ≤ (119 / 528)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1885 / 8448)) (u := (119 / 528))
    (a := (1500001907 / 1000000000)) (b := (31922641 / 125000000)) (c := (1489972789 / 1000000000)) (d := (252481911 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_79.2 (by convert! log_c_80.2 using 1; norm_num)
    log_v_80.1 (by convert! log_c_79.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


