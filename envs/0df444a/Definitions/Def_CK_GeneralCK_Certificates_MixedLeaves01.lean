-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves01
-- name    : CK_GeneralCK_Certificates_MixedLeaves01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:14.425463+00:00
-- url     : https://prove2.me/theorems/3605df3d-2f49-4e80-b0d0-4fffb71f0cf7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves01` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves01` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves01` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves01 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves01.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_16 (v : ℝ) (hl : (43 / 528) ≤ v) (hu : v ≤ (707 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (43 / 528)) (u := (707 / 8448))
    (a := (250789617 / 100000000)) (b := (87398849 / 1000000000)) (c := (1240327169 / 500000000)) (d := (1327303 / 15625000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_16.2 (by convert! log_c_17.2 using 1; norm_num)
    log_v_17.1 (by convert! log_c_16.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_17 (v : ℝ) (hl : (707 / 8448) ≤ v) (hu : v ≤ (11 / 128)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (707 / 8448)) (u := (11 / 128))
    (a := (1240327171 / 500000000)) (b := (8985633 / 100000000)) (c := (2454134989 / 1000000000)) (d := (1365607 / 15625000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_17.2 (by convert! log_c_18.2 using 1; norm_num)
    log_v_18.1 (by convert! log_c_17.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_18 (v : ℝ) (hl : (11 / 128) ≤ v) (hu : v ≤ (745 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (11 / 128)) (u := (745 / 8448))
    (a := (2454134993 / 1000000000)) (b := (11539983 / 125000000)) (c := (485660157 / 200000000)) (d := (89856329 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_18.2 (by convert! log_c_19.2 using 1; norm_num)
    log_v_19.1 (by convert! log_c_18.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_19 (v : ℝ) (hl : (745 / 8448) ≤ v) (hu : v ≤ (191 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (745 / 8448)) (u := (191 / 2112))
    (a := (2428300789 / 1000000000)) (b := (94789483 / 1000000000)) (c := (480623443 / 200000000)) (d := (92319863 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_19.2 (by convert! log_c_20.2 using 1; norm_num)
    log_v_20.1 (by convert! log_c_19.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_20 (v : ℝ) (hl : (191 / 2112) ≤ v) (hu : v ≤ (261 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (191 / 2112)) (u := (261 / 2816))
    (a := (2403117219 / 1000000000)) (b := (19453043 / 200000000)) (c := (594638077 / 250000000)) (d := (47394741 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_20.2 (by convert! log_c_21.2 using 1; norm_num)
    log_v_21.1 (by convert! log_c_20.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_21 (v : ℝ) (hl : (261 / 2816) ≤ v) (hu : v ≤ (401 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (261 / 2816)) (u := (401 / 4224))
    (a := (297319039 / 125000000)) (b := (24936773 / 250000000)) (c := (588644099 / 250000000)) (d := (48632607 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_21.2 (by convert! log_c_22.2 using 1; norm_num)
    log_v_22.1 (by convert! log_c_21.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_22 (v : ℝ) (hl : (401 / 4224) ≤ v) (hu : v ≤ (821 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (401 / 4224)) (u := (821 / 8448))
    (a := (5886441 / 2500000)) (b := (12779393 / 125000000)) (c := (1165580947 / 500000000)) (d := (99747091 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_22.2 (by convert! log_c_23.2 using 1; norm_num)
    log_v_23.1 (by convert! log_c_22.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_23 (v : ℝ) (hl : (821 / 8448) ≤ v) (hu : v ≤ (35 / 352)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (821 / 8448)) (u := (35 / 352))
    (a := (1165580949 / 500000000)) (b := (52364701 / 500000000)) (c := (288535389 / 125000000)) (d := (102235143 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_23.2 (by convert! log_c_24.2 using 1; norm_num)
    log_v_24.1 (by convert! log_c_23.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_24 (v : ℝ) (hl : (35 / 352) ≤ v) (hu : v ≤ (859 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (35 / 352)) (u := (859 / 8448))
    (a := (577070779 / 250000000)) (b := (107229897 / 1000000000)) (c := (1142958041 / 500000000)) (d := (104729401 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_24.2 (by convert! log_c_25.2 using 1; norm_num)
    log_v_25.1 (by convert! log_c_24.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_25 (v : ℝ) (hl : (859 / 8448) ≤ v) (hu : v ≤ (439 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (859 / 8448)) (u := (439 / 4224))
    (a := (1142958043 / 500000000)) (b := (5486833 / 50000000)) (c := (226403841 / 100000000)) (d := (13403737 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_25.2 (by convert! log_c_26.2 using 1; norm_num)
    log_v_26.1 (by convert! log_c_25.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_26 (v : ℝ) (hl : (439 / 4224) ≤ v) (hu : v ≤ (299 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (439 / 4224)) (u := (299 / 2816))
    (a := (1132019207 / 500000000)) (b := (112249723 / 1000000000)) (c := (1121314571 / 500000000)) (d := (109736659 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_26.2 (by convert! log_c_27.2 using 1; norm_num)
    log_v_27.1 (by convert! log_c_26.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_27 (v : ℝ) (hl : (299 / 2816) ≤ v) (hu : v ≤ (229 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (299 / 2816)) (u := (229 / 2112))
    (a := (1121314573 / 500000000)) (b := (114769117 / 1000000000)) (c := (2221668639 / 1000000000)) (d := (56124861 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_27.2 (by convert! log_c_28.2 using 1; norm_num)
    log_v_28.1 (by convert! log_c_27.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_28 (v : ℝ) (hl : (229 / 2112) ≤ v) (hu : v ≤ (85 / 768)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (229 / 2112)) (u := (85 / 768))
    (a := (2221668643 / 1000000000)) (b := (58647437 / 500000000)) (c := (1100569237 / 500000000)) (d := (28692279 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_28.2 (by convert! log_c_29.2 using 1; norm_num)
    log_v_29.1 (by convert! log_c_28.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_29 (v : ℝ) (hl : (85 / 768) ≤ v) (hu : v ≤ (159 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (85 / 768)) (u := (159 / 1408))
    (a := (1100569239 / 500000000)) (b := (119827027 / 1000000000)) (c := (545255333 / 250000000)) (d := (117294873 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_29.2 (by convert! log_c_30.2 using 1; norm_num)
    log_v_30.1 (by convert! log_c_29.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_30 (v : ℝ) (hl : (159 / 1408) ≤ v) (hu : v ≤ (973 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (159 / 1408)) (u := (973 / 8448))
    (a := (272627667 / 125000000)) (b := (15295701 / 125000000)) (c := (1080650461 / 500000000)) (d := (59913513 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_30.2 (by convert! log_c_31.2 using 1; norm_num)
    log_v_31.1 (by convert! log_c_30.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_31 (v : ℝ) (hl : (973 / 8448) ≤ v) (hu : v ≤ (31 / 264)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (973 / 8448)) (u := (31 / 264))
    (a := (1080650463 / 500000000)) (b := (2498213 / 20000000)) (c := (267745237 / 125000000)) (d := (122365607 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_31.2 (by convert! log_c_32.2 using 1; norm_num)
    log_v_32.1 (by convert! log_c_31.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


