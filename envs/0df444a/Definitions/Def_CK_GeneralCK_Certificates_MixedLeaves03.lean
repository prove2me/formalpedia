-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves03
-- name    : CK_GeneralCK_Certificates_MixedLeaves03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:31:48.381101+00:00
-- url     : https://prove2.me/theorems/832517e6-89c5-47e3-8370-ca6ca17d07d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves03` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves03` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves03` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves03 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves03.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_48 (v : ℝ) (hl : (27 / 176) ≤ v) (hu : v ≤ (1315 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (27 / 176)) (u := (1315 / 8448))
    (a := (187464713 / 100000000)) (b := (660929 / 3906250)) (c := (93004653 / 50000000)) (d := (166537689 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_48.2 (by convert! log_c_49.2 using 1; norm_num)
    log_v_49.1 (by convert! log_c_48.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_49 (v : ℝ) (hl : (1315 / 8448) ≤ v) (hu : v ≤ (667 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1315 / 8448)) (u := (667 / 4224))
    (a := (1860093063 / 1000000000)) (b := (85932527 / 500000000)) (c := (922873889 / 500000000)) (d := (169197823 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_49.2 (by convert! log_c_50.2 using 1; norm_num)
    log_v_50.1 (by convert! log_c_49.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_50 (v : ℝ) (hl : (667 / 4224) ≤ v) (hu : v ≤ (41 / 256)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (667 / 4224)) (u := (41 / 256))
    (a := (1845747781 / 1000000000)) (b := (174539417 / 1000000000)) (c := (14309417 / 7812500)) (d := (171865053 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_50.2 (by convert! log_c_51.2 using 1; norm_num)
    log_v_51.1 (by convert! log_c_50.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_51 (v : ℝ) (hl : (41 / 256) ≤ v) (hu : v ≤ (343 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (41 / 256)) (u := (343 / 2112))
    (a := (1831605379 / 1000000000)) (b := (177220951 / 1000000000)) (c := (454415049 / 250000000)) (d := (21817427 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_51.2 (by convert! log_c_52.2 using 1; norm_num)
    log_v_52.1 (by convert! log_c_51.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_52 (v : ℝ) (hl : (343 / 2112) ≤ v) (hu : v ≤ (1391 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (343 / 2112)) (u := (1391 / 8448))
    (a := (1817660199 / 1000000000)) (b := (35981939 / 200000000)) (c := (450976703 / 250000000)) (d := (3544419 / 20000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_52.2 (by convert! log_c_53.2 using 1; norm_num)
    log_v_53.1 (by convert! log_c_52.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_53 (v : ℝ) (hl : (1391 / 8448) ≤ v) (hu : v ≤ (235 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1391 / 8448)) (u := (235 / 1408))
    (a := (360781363 / 200000000)) (b := (182605689 / 1000000000)) (c := (1790340021 / 1000000000)) (d := (89954847 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_53.2 (by convert! log_c_54.2 using 1; norm_num)
    log_v_54.1 (by convert! log_c_53.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_54 (v : ℝ) (hl : (235 / 1408) ≤ v) (hu : v ≤ (1429 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (235 / 1408)) (u := (1429 / 8448))
    (a := (223792503 / 125000000)) (b := (18530897 / 100000000)) (c := (888477413 / 500000000)) (d := (22825711 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_54.2 (by convert! log_c_55.2 using 1; norm_num)
    log_v_55.1 (by convert! log_c_54.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_55 (v : ℝ) (hl : (1429 / 8448) ≤ v) (hu : v ≤ (181 / 1056)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1429 / 8448)) (u := (181 / 1056))
    (a := (1776954829 / 1000000000)) (b := (94009789 / 500000000)) (c := (1763746431 / 1000000000)) (d := (185308969 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_55.2 (by convert! log_c_56.2 using 1; norm_num)
    log_v_56.1 (by convert! log_c_55.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_56 (v : ℝ) (hl : (181 / 1056) ≤ v) (hu : v ≤ (489 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (181 / 1056)) (u := (489 / 2816))
    (a := (881873217 / 500000000)) (b := (95368777 / 500000000)) (c := (875355113 / 500000000)) (d := (188019577 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_56.2 (by convert! log_c_57.2 using 1; norm_num)
    log_v_57.1 (by convert! log_c_56.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_57 (v : ℝ) (hl : (489 / 2816) ≤ v) (hu : v ≤ (743 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (489 / 2816)) (u := (743 / 4224))
    (a := (1750710229 / 1000000000)) (b := (96731469 / 500000000)) (c := (1737841779 / 1000000000)) (d := (190737553 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_57.2 (by convert! log_c_58.2 using 1; norm_num)
    log_v_58.1 (by convert! log_c_57.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_58 (v : ℝ) (hl : (743 / 4224) ≤ v) (hu : v ≤ (1505 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (743 / 4224)) (u := (1505 / 8448))
    (a := (868920891 / 500000000)) (b := (19619577 / 100000000)) (c := (1725136827 / 1000000000)) (d := (193462937 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_58.2 (by convert! log_c_59.2 using 1; norm_num)
    log_v_59.1 (by convert! log_c_58.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_59 (v : ℝ) (hl : (1505 / 8448) ≤ v) (hu : v ≤ (127 / 704)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1505 / 8448)) (u := (127 / 704))
    (a := (172513683 / 100000000)) (b := (19893609 / 100000000)) (c := (428147817 / 250000000)) (d := (196195769 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_59.2 (by convert! log_c_60.2 using 1; norm_num)
    log_v_60.1 (by convert! log_c_59.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_60 (v : ℝ) (hl : (127 / 704) ≤ v) (hu : v ≤ (1543 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (127 / 704)) (u := (1543 / 8448))
    (a := (1712591271 / 1000000000)) (b := (201683941 / 1000000000)) (c := (26565643 / 15625000)) (d := (198936089 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_60.2 (by convert! log_c_61.2 using 1; norm_num)
    log_v_61.1 (by convert! log_c_60.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_61 (v : ℝ) (hl : (1543 / 8448) ≤ v) (hu : v ≤ (71 / 384)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1543 / 8448)) (u := (71 / 384))
    (a := (340040231 / 200000000)) (b := (204439363 / 1000000000)) (c := (843981337 / 500000000)) (d := (10084197 / 50000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_61.2 (by convert! log_c_62.2 using 1; norm_num)
    log_v_62.1 (by convert! log_c_61.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_62 (v : ℝ) (hl : (71 / 384) ≤ v) (hu : v ≤ (527 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (71 / 384)) (u := (527 / 2816))
    (a := (1687962677 / 1000000000)) (b := (103601199 / 500000000)) (c := (1675872167 / 1000000000)) (d := (102219681 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_62.2 (by convert! log_c_63.2 using 1; norm_num)
    log_v_63.1 (by convert! log_c_62.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_63 (v : ℝ) (hl : (527 / 2816) ≤ v) (hu : v ≤ (25 / 132)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (527 / 2816)) (u := (25 / 132))
    (a := (167587217 / 100000000)) (b := (209973089 / 1000000000)) (c := (103995381 / 62500000)) (d := (207202397 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_63.2 (by convert! log_c_64.2 using 1; norm_num)
    log_v_64.1 (by convert! log_c_63.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


