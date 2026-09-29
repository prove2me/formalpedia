-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves05
-- name    : CK_GeneralCK_Certificates_MixedLeaves05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:33:18.358075+00:00
-- url     : https://prove2.me/theorems/0625320f-c0c3-4a5d-8ea1-045d7c4a2428
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves05` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves05` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves05` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves05 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves05.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_80 (v : ℝ) (hl : (119 / 528) ≤ v) (hu : v ≤ (641 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (119 / 528)) (u := (641 / 2816))
    (a := (186246599 / 125000000)) (b := (129144387 / 500000000)) (c := (1480043259 / 1000000000)) (d := (255381127 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_80.2 (by convert! log_c_81.2 using 1; norm_num)
    log_v_81.1 (by convert! log_c_80.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_81 (v : ℝ) (hl : (641 / 2816) ≤ v) (hu : v ≤ (971 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (641 / 2816)) (u := (971 / 4224))
    (a := (740021631 / 500000000)) (b := (261204899 / 1000000000)) (c := (294042271 / 200000000)) (d := (258288773 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_81.2 (by convert! log_c_82.2 using 1; norm_num)
    log_v_82.1 (by convert! log_c_81.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_82 (v : ℝ) (hl : (971 / 4224) ≤ v) (hu : v ≤ (1961 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (971 / 4224)) (u := (1961 / 8448))
    (a := (735105679 / 500000000)) (b := (264129553 / 1000000000)) (c := (730237589 / 500000000)) (d := (130602449 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_82.2 (by convert! log_c_83.2 using 1; norm_num)
    log_v_83.1 (by convert! log_c_82.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_83 (v : ℝ) (hl : (1961 / 8448) ≤ v) (hu : v ≤ (15 / 64)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1961 / 8448)) (u := (15 / 64))
    (a := (1460475181 / 1000000000)) (b := (133531393 / 500000000)) (c := (1450832881 / 1000000000)) (d := (16508097 / 62500000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_83.2 (by convert! log_c_84.2 using 1; norm_num)
    log_v_84.1 (by convert! log_c_83.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_84 (v : ℝ) (hl : (15 / 64) ≤ v) (hu : v ≤ (1999 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (15 / 64)) (u := (1999 / 8448))
    (a := (362708221 / 250000000)) (b := (270004647 / 1000000000)) (c := (144128267 / 100000000)) (d := (53412557 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_84.2 (by convert! log_c_85.2 using 1; norm_num)
    log_v_85.1 (by convert! log_c_84.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_85 (v : ℝ) (hl : (1999 / 8448) ≤ v) (hu : v ≤ (1009 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1999 / 8448)) (u := (1009 / 4224))
    (a := (1441282673 / 1000000000)) (b := (272955189 / 1000000000)) (c := (1431822803 / 1000000000)) (d := (135002323 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_85.2 (by convert! log_c_86.2 using 1; norm_num)
    log_v_86.1 (by convert! log_c_85.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_86 (v : ℝ) (hl : (1009 / 4224) ≤ v) (hu : v ≤ (679 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1009 / 4224)) (u := (679 / 2816))
    (a := (715911403 / 500000000)) (b := (137957231 / 500000000)) (c := (355612897 / 250000000)) (d := (68238797 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_86.2 (by convert! log_c_87.2 using 1; norm_num)
    log_v_87.1 (by convert! log_c_86.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_87 (v : ℝ) (hl : (679 / 2816) ≤ v) (hu : v ≤ (257 / 1056)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (679 / 2816)) (u := (257 / 1056))
    (a := (1422451591 / 1000000000)) (b := (278882519 / 1000000000)) (c := (706583689 / 500000000)) (d := (275914461 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_87.2 (by convert! log_c_88.2 using 1; norm_num)
    log_v_88.1 (by convert! log_c_87.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_88 (v : ℝ) (hl : (257 / 1056) ≤ v) (hu : v ≤ (2075 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (257 / 1056)) (u := (2075 / 8448))
    (a := (1413167381 / 1000000000)) (b := (281859411 / 1000000000)) (c := (350992143 / 250000000)) (d := (139441259 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_88.2 (by convert! log_c_89.2 using 1; norm_num)
    log_v_89.1 (by convert! log_c_88.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_89 (v : ℝ) (hl : (2075 / 8448) ≤ v) (hu : v ≤ (349 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (2075 / 8448)) (u := (349 / 1408))
    (a := (56158743 / 40000000)) (b := (35605649 / 125000000)) (c := (1394853613 / 1000000000)) (d := (28185941 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_89.2 (by convert! log_c_90.2 using 1; norm_num)
    log_v_90.1 (by convert! log_c_89.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_90 (v : ℝ) (hl : (349 / 1408) ≤ v) (hu : v ≤ (533 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (349 / 1408)) (u := (533 / 2112))
    (a := (87178351 / 62500000)) (b := (290843631 / 1000000000)) (c := (68843461 / 50000000)) (d := (284845191 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_90.2 (by convert! log_c_91.2 using 1; norm_num)
    log_v_91.1 (by convert! log_c_90.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_91 (v : ℝ) (hl : (533 / 2112) ≤ v) (hu : v ≤ (1085 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (533 / 2112)) (u := (1085 / 4224))
    (a := (688434611 / 500000000)) (b := (296878269 / 1000000000)) (c := (679601279 / 500000000)) (d := (29084363 / 100000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_91.2 (by convert! log_c_92.2 using 1; norm_num)
    log_v_92.1 (by convert! log_c_91.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_92 (v : ℝ) (hl : (1085 / 4224) ≤ v) (hu : v ≤ (23 / 88)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1085 / 4224)) (u := (23 / 88))
    (a := (1061877 / 781250)) (b := (60589909 / 200000000)) (c := (1341842597 / 1000000000)) (d := (74219567 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_92.2 (by convert! log_c_93.2 using 1; norm_num)
    log_v_93.1 (by convert! log_c_92.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_93 (v : ℝ) (hl : (23 / 88) ≤ v) (hu : v ≤ (1123 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (23 / 88)) (u := (1123 / 4224))
    (a := (1341842599 / 1000000000)) (b := (309057907 / 1000000000)) (c := (132477887 / 100000000)) (d := (37868693 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_93.2 (by convert! log_c_94.2 using 1; norm_num)
    log_v_94.1 (by convert! log_c_93.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_94 (v : ℝ) (hl : (1123 / 4224) ≤ v) (hu : v ≤ (571 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1123 / 4224)) (u := (571 / 2112))
    (a := (165597359 / 125000000)) (b := (31520381 / 100000000)) (c := (654000717 / 500000000)) (d := (154528953 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_94.2 (by convert! log_c_95.2 using 1; norm_num)
    log_v_95.1 (by convert! log_c_94.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_95 (v : ℝ) (hl : (571 / 2112) ≤ v) (hu : v ≤ (387 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (571 / 2112)) (u := (387 / 1408))
    (a := (327000359 / 250000000)) (b := (321387719 / 1000000000)) (c := (1291500843 / 1000000000)) (d := (315203809 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_95.2 (by convert! log_c_96.2 using 1; norm_num)
    log_v_96.1 (by convert! log_c_95.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


