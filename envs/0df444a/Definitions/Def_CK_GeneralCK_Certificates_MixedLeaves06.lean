-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves06
-- name    : CK_GeneralCK_Certificates_MixedLeaves06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:30:27.85004+00:00
-- url     : https://prove2.me/theorems/57f3257c-72b0-4f35-8ab5-f4bb68a82259
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves06` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves06` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves06` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves06 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves06.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_96 (v : ℝ) (hl : (387 / 1408) ≤ v) (hu : v ≤ (295 / 1056)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (387 / 1408)) (u := (295 / 1056))
    (a := (258300169 / 200000000)) (b := (327610107 / 1000000000)) (c := (1275268107 / 1000000000)) (d := (160693859 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_96.2 (by convert! log_c_97.2 using 1; norm_num)
    log_v_97.1 (by convert! log_c_96.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_97 (v : ℝ) (hl : (295 / 1056) ≤ v) (hu : v ≤ (109 / 384)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (295 / 1056)) (u := (109 / 384))
    (a := (1275268109 / 1000000000)) (b := (66774291 / 200000000)) (c := (1259294669 / 1000000000)) (d := (163805053 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_97.2 (by convert! log_c_98.2 using 1; norm_num)
    log_v_98.1 (by convert! log_c_97.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_98 (v : ℝ) (hl : (109 / 384) ≤ v) (hu : v ≤ (203 / 704)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (109 / 384)) (u := (203 / 704))
    (a := (1259294671 / 1000000000)) (b := (10630383 / 31250000)) (c := (155446547 / 125000000)) (d := (166935727 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_98.2 (by convert! log_c_99.2 using 1; norm_num)
    log_v_99.1 (by convert! log_c_98.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_99 (v : ℝ) (hl : (203 / 704) ≤ v) (hu : v ≤ (1237 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (203 / 704)) (u := (1237 / 4224))
    (a := (621786189 / 500000000)) (b := (21657063 / 62500000)) (c := (307023363 / 250000000)) (d := (68034451 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_99.2 (by convert! log_c_100.2 using 1; norm_num)
    log_v_100.1 (by convert! log_c_99.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_100 (v : ℝ) (hl : (1237 / 4224) ≤ v) (hu : v ≤ (157 / 528)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1237 / 4224)) (u := (157 / 528))
    (a := (614046727 / 500000000)) (b := (176447111 / 500000000)) (c := (1212850477 / 1000000000)) (d := (346513007 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_100.2 (by convert! log_c_101.2 using 1; norm_num)
    log_v_101.1 (by convert! log_c_100.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_101 (v : ℝ) (hl : (157 / 528) ≤ v) (hu : v ≤ (647 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (157 / 528)) (u := (647 / 2112))
    (a := (1212850479 / 1000000000)) (b := (91445031 / 250000000)) (c := (1183044349 / 1000000000)) (d := (352894221 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_101.2 (by convert! log_c_102.2 using 1; norm_num)
    log_v_102.1 (by convert! log_c_101.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_102 (v : ℝ) (hl : (647 / 2112) ≤ v) (hu : v ≤ (111 / 352)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (647 / 2112)) (u := (111 / 352))
    (a := (1183044351 / 1000000000)) (b := (378834243 / 1000000000)) (c := (1154100973 / 1000000000)) (d := (365780123 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_102.2 (by convert! log_c_103.2 using 1; norm_num)
    log_v_103.1 (by convert! log_c_102.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_103 (v : ℝ) (hl : (111 / 352) ≤ v) (hu : v ≤ (685 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (111 / 352)) (u := (685 / 2112))
    (a := (46164039 / 40000000)) (b := (98015257 / 250000000)) (c := (562985903 / 500000000)) (d := (189417121 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_103.2 (by convert! log_c_104.2 using 1; norm_num)
    log_v_104.1 (by convert! log_c_103.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_104 (v : ℝ) (hl : (685 / 2112) ≤ v) (hu : v ≤ (1 / 3)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (685 / 2112)) (u := (1 / 3))
    (a := (35186619 / 31250000)) (b := (405465109 / 1000000000)) (c := (17165817 / 15625000)) (d := (392061027 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_104.2 (by convert! log_c_105.2 using 1; norm_num)
    log_v_105.1 (by convert! log_c_104.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


