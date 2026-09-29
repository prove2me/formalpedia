-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedLeaves02
-- name    : CK_GeneralCK_Certificates_MixedLeaves02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:14.752416+00:00
-- url     : https://prove2.me/theorems/97311247-c207-444e-ba01-fef7a5cbbecc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedLeaves02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedLeaves02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedLeaves02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedLeaves02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedLeaves02.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedLogs

namespace GeneralCK.Certificates.Mixed

theorem leaf_32 (v : ℝ) (hl : (31 / 264) ≤ v) (hu : v ≤ (337 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (31 / 264)) (u := (337 / 2816))
    (a := (21419619 / 10000000)) (b := (63731093 / 500000000)) (c := (424597957 / 200000000)) (d := (124910649 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_32.2 (by convert! log_c_33.2 using 1; norm_num)
    log_v_33.1 (by convert! log_c_32.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_33 (v : ℝ) (hl : (337 / 2816) ≤ v) (hu : v ≤ (515 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (337 / 2816)) (u := (515 / 4224))
    (a := (2122989789 / 1000000000)) (b := (16252531 / 125000000)) (c := (2104370923 / 1000000000)) (d := (25492437 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_33.2 (by convert! log_c_34.2 using 1; norm_num)
    log_v_34.1 (by convert! log_c_33.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_34 (v : ℝ) (hl : (515 / 4224) ≤ v) (hu : v ≤ (1049 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (515 / 4224)) (u := (1049 / 8448))
    (a := (2104370927 / 1000000000)) (b := (16573109 / 125000000)) (c := (417218479 / 200000000)) (d := (130020247 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_34.2 (by convert! log_c_35.2 using 1; norm_num)
    log_v_35.1 (by convert! log_c_34.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_35 (v : ℝ) (hl : (1049 / 8448) ≤ v) (hu : v ≤ (89 / 704)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1049 / 8448)) (u := (89 / 704))
    (a := (2086092399 / 1000000000)) (b := (135156089 / 1000000000)) (c := (413628397 / 200000000)) (d := (132584871 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_35.2 (by convert! log_c_36.2 using 1; norm_num)
    log_v_36.1 (by convert! log_c_35.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_36 (v : ℝ) (hl : (89 / 704) ≤ v) (hu : v ≤ (1087 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (89 / 704)) (u := (1087 / 8448))
    (a := (517035497 / 250000000)) (b := (68866967 / 500000000)) (c := (2050508117 / 1000000000)) (d := (16894511 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_36.2 (by convert! log_c_37.2 using 1; norm_num)
    log_v_37.1 (by convert! log_c_36.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_37 (v : ℝ) (hl : (1087 / 8448) ≤ v) (hu : v ≤ (553 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1087 / 8448)) (u := (553 / 4224))
    (a := (51262703 / 25000000)) (b := (70159221 / 500000000)) (c := (1016589911 / 500000000)) (d := (137733933 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_37.2 (by convert! log_c_38.2 using 1; norm_num)
    log_v_38.1 (by convert! log_c_37.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_38 (v : ℝ) (hl : (553 / 4224) ≤ v) (hu : v ≤ (375 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (553 / 4224)) (u := (375 / 2816))
    (a := (81327193 / 40000000)) (b := (142909647 / 1000000000)) (c := (201614669 / 100000000)) (d := (140318441 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_38.2 (by convert! log_c_39.2 using 1; norm_num)
    log_v_39.1 (by convert! log_c_38.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_39 (v : ℝ) (hl : (375 / 2816) ≤ v) (hu : v ≤ (13 / 96)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (375 / 2816)) (u := (13 / 96))
    (a := (2016146693 / 1000000000)) (b := (568389 / 3906250)) (c := (124962427 / 62500000)) (d := (71454823 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_39.2 (by convert! log_c_40.2 using 1; norm_num)
    log_v_40.1 (by convert! log_c_39.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_40 (v : ℝ) (hl : (13 / 96) ≤ v) (hu : v ≤ (1163 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (13 / 96)) (u := (1163 / 8448))
    (a := (399879767 / 200000000)) (b := (4628509 / 31250000)) (c := (495731713 / 250000000)) (d := (145507583 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_40.2 (by convert! log_c_41.2 using 1; norm_num)
    log_v_41.1 (by convert! log_c_40.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_41 (v : ℝ) (hl : (1163 / 8448) ≤ v) (hu : v ≤ (197 / 1408)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1163 / 8448)) (u := (197 / 1408))
    (a := (396585371 / 200000000)) (b := (75361897 / 500000000)) (c := (983360903 / 500000000)) (d := (148112287 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_41.2 (by convert! log_c_42.2 using 1; norm_num)
    log_v_42.1 (by convert! log_c_41.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_42 (v : ℝ) (hl : (197 / 1408) ≤ v) (hu : v ≤ (1201 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (197 / 1408)) (u := (1201 / 8448))
    (a := (1966721809 / 1000000000)) (b := (153342137 / 1000000000)) (c := (975387591 / 500000000)) (d := (150723793 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_42.2 (by convert! log_c_43.2 using 1; norm_num)
    log_v_43.1 (by convert! log_c_42.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_43 (v : ℝ) (hl : (1201 / 8448) ≤ v) (hu : v ≤ (305 / 2112)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1201 / 8448)) (u := (305 / 2112))
    (a := (390155037 / 200000000)) (b := (31193471 / 200000000)) (c := (1935078867 / 1000000000)) (d := (19167767 / 125000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_43.2 (by convert! log_c_44.2 using 1; norm_num)
    log_v_44.1 (by convert! log_c_43.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_44 (v : ℝ) (hl : (305 / 2112) ≤ v) (hu : v ≤ (413 / 2816)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (305 / 2112)) (u := (413 / 2816))
    (a := (193507887 / 100000000)) (b := (79299741 / 500000000)) (c := (1919625123 / 1000000000)) (d := (77983677 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_44.2 (by convert! log_c_45.2 using 1; norm_num)
    log_v_45.1 (by convert! log_c_44.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_45 (v : ℝ) (hl : (413 / 2816) ≤ v) (hu : v ≤ (629 / 4224)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (413 / 2816)) (u := (629 / 4224))
    (a := (959812563 / 500000000)) (b := (40309639 / 250000000)) (c := (1904406567 / 1000000000)) (d := (158599481 / 1000000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_45.2 (by convert! log_c_46.2 using 1; norm_num)
    log_v_46.1 (by convert! log_c_45.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_46 (v : ℝ) (hl : (629 / 4224) ≤ v) (hu : v ≤ (1277 / 8448)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (629 / 4224)) (u := (1277 / 8448))
    (a := (190440657 / 100000000)) (b := (163884613 / 1000000000)) (c := (472354037 / 250000000)) (d := (32247711 / 200000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_46.2 (by convert! log_c_47.2 using 1; norm_num)
    log_v_47.1 (by convert! log_c_46.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem leaf_47 (v : ℝ) (hl : (1277 / 8448) ≤ v) (hu : v ≤ (27 / 176)) :
    profile v ≤ 13/6 := by
  exact leaf_bound (l := (1277 / 8448)) (u := (27 / 176))
    (a := (1889416151 / 1000000000)) (b := (16653769 / 100000000)) (c := (1874647127 / 1000000000)) (d := (40971153 / 250000000))
    (by norm_num) (by norm_num) (by norm_num) hl hu
    log_v_47.2 (by convert! log_c_48.2 using 1; norm_num)
    log_v_48.1 (by convert! log_c_47.1 using 1; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end GeneralCK.Certificates.Mixed


