-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs13
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:45:13.711078+00:00
-- url     : https://prove2.me/theorems/a6db22e9-e96e-4463-904e-f0d554f4283a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs13.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_208 : (2482253919 / 1000000000) ≤ -Real.log (2139 / 25600) ∧
    -Real.log (2139 / 25600) ≤ (2482253923 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 5339)) (n := 12)
    (lo := (402812379 / 1000000000)) (hi := (20140619 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2139) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2139) = 1/(2139 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_208 : (87252883 / 1000000000) ≤ -Real.log (23461 / 25600) ∧
    -Real.log (23461 / 25600) ≤ (21813221 / 250000000) := by
  have h := checkLog_sound (w := (2139 / 49061)) (n := 12)
    (lo := (87252883 / 1000000000)) (hi := (21813221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 23461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 23461) = 1/(23461 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_208 : (479000207 / 400000000) ≤ xi (2139 / 25600) ∧ xi (2139 / 25600) ≤ (29937513 / 25000000) ∧
    (1284753401 / 1000000000) ≤ kap (2139 / 25600) ∧ kap (2139 / 25600) ≤ (2569506807 / 2000000000) := by
  have h := endpoint_bounds (v := ((2139 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_208.1 (by convert! log_c_208.1 using 1; norm_num)
    log_v_208.2 (by convert! log_c_208.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_209 : (2461510607 / 1000000000) ≤ -Real.log (13103 / 153600) ∧
    -Real.log (13103 / 153600) ≤ (2461510611 / 1000000000) := by
  have h := checkLog_sound (w := (6097 / 32303)) (n := 12)
    (lo := (382069067 / 1000000000)) (hi := (95517267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 13103) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 13103) = 1/(13103 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_209 : (22291421 / 250000000) ≤ -Real.log (140497 / 153600) ∧
    -Real.log (140497 / 153600) ≤ (17833137 / 200000000) := by
  have h := checkLog_sound (w := (13103 / 294097)) (n := 12)
    (lo := (22291421 / 250000000)) (hi := (17833137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 140497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 140497) = 1/(140497 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_209 : (1186172461 / 1000000000) ≤ xi (13103 / 153600) ∧ xi (13103 / 153600) ≤ (2372344927 / 2000000000) ∧
    (2550676291 / 2000000000) ≤ kap (13103 / 153600) ∧ kap (13103 / 153600) ≤ (318834537 / 250000000) := by
  have h := endpoint_bounds (v := ((13103 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_209.1 (by convert! log_c_209.1 using 1; norm_num)
    log_v_209.2 (by convert! log_c_209.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_210 : (48823777 / 20000000) ≤ -Real.log (3343 / 38400) ∧
    -Real.log (3343 / 38400) ≤ (1220594427 / 500000000) := by
  have h := checkLog_sound (w := (1457 / 8143)) (n := 12)
    (lo := (36174731 / 100000000)) (hi := (361747311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3343) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4800 / 3343) = 1/(3343 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_210 : (91082151 / 1000000000) ≤ -Real.log (35057 / 38400) ∧
    -Real.log (35057 / 38400) ≤ (11385269 / 125000000) := by
  have h := checkLog_sound (w := (3343 / 73457)) (n := 12)
    (lo := (91082151 / 1000000000)) (hi := (11385269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 35057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 35057) = 1/(35057 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_210 : (1175053349 / 1000000000) ≤ xi (3343 / 38400) ∧ xi (3343 / 38400) ≤ (2350106703 / 2000000000) ∧
    (2532271001 / 2000000000) ≤ kap (3343 / 38400) ∧ kap (3343 / 38400) ≤ (1266135503 / 1000000000) := by
  have h := endpoint_bounds (v := ((3343 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_210.1 (by convert! log_c_210.1 using 1; norm_num)
    log_v_210.2 (by convert! log_c_210.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_211 : (484254371 / 200000000) ≤ -Real.log (4547 / 51200) ∧
    -Real.log (4547 / 51200) ≤ (2421271859 / 1000000000) := by
  have h := checkLog_sound (w := (1853 / 10947)) (n := 12)
    (lo := (68366063 / 200000000)) (hi := (85457579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4547) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 4547) = 1/(4547 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_211 : (46501149 / 500000000) ≤ -Real.log (46653 / 51200) ∧
    -Real.log (46653 / 51200) ≤ (93002299 / 1000000000) := by
  have h := checkLog_sound (w := (4547 / 97853)) (n := 12)
    (lo := (46501149 / 500000000)) (hi := (93002299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51200 / 46653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51200 / 46653) = 1/(46653 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_211 : (582067389 / 500000000) ≤ xi (4547 / 51200) ∧ xi (4547 / 51200) ≤ (2328269561 / 2000000000) ∧
    (2514274153 / 2000000000) ≤ kap (4547 / 51200) ∧ kap (4547 / 51200) ≤ (1257137079 / 1000000000) := by
  have h := endpoint_bounds (v := ((4547 / 51200) : ℝ)) (by norm_num) (by norm_num)
    log_v_211.1 (by convert! log_c_211.1 using 1; norm_num)
    log_v_211.2 (by convert! log_c_211.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_212 : (2401743813 / 1000000000) ≤ -Real.log (1391 / 15360) ∧
    -Real.log (1391 / 15360) ≤ (2401743817 / 1000000000) := by
  have h := checkLog_sound (w := (529 / 3311)) (n := 12)
    (lo := (322302273 / 1000000000)) (hi := (161151137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 1391) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1920 / 1391) = 1/(1391 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_212 : (47463069 / 500000000) ≤ -Real.log (13969 / 15360) ∧
    -Real.log (13969 / 15360) ≤ (94926139 / 1000000000) := by
  have h := checkLog_sound (w := (1391 / 29329)) (n := 12)
    (lo := (47463069 / 500000000)) (hi := (94926139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15360 / 13969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15360 / 13969) = 1/(13969 / 15360) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_212 : (1153408837 / 1000000000) ≤ xi (1391 / 15360) ∧ xi (1391 / 15360) ≤ (2306817679 / 2000000000) ∧
    (2496669951 / 2000000000) ≤ kap (1391 / 15360) ∧ kap (1391 / 15360) ≤ (624167489 / 500000000) := by
  have h := endpoint_bounds (v := ((1391 / 15360) : ℝ)) (by norm_num) (by norm_num)
    log_v_212.1 (by convert! log_c_212.1 using 1; norm_num)
    log_v_212.2 (by convert! log_c_212.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_213 : (1191294911 / 500000000) ≤ -Real.log (14179 / 153600) ∧
    -Real.log (14179 / 153600) ≤ (1191294913 / 500000000) := by
  have h := checkLog_sound (w := (5021 / 33379)) (n := 12)
    (lo := (151574141 / 500000000)) (hi := (303148283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14179) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 14179) = 1/(14179 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_213 : (12106711 / 125000000) ≤ -Real.log (139421 / 153600) ∧
    -Real.log (139421 / 153600) ≤ (96853689 / 1000000000) := by
  have h := checkLog_sound (w := (14179 / 293021)) (n := 12)
    (lo := (12106711 / 125000000)) (hi := (96853689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 139421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 139421) = 1/(139421 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_213 : (2285736133 / 2000000000) ≤ xi (14179 / 153600) ∧ xi (14179 / 153600) ≤ (1142868069 / 1000000000) ∧
    (247944351 / 200000000) ≤ kap (14179 / 153600) ∧ kap (14179 / 153600) ≤ (495888703 / 400000000) := by
  have h := endpoint_bounds (v := ((14179 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_213.1 (by convert! log_c_213.1 using 1; norm_num)
    log_v_213.2 (by convert! log_c_213.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_214 : (1181897911 / 500000000) ≤ -Real.log (301 / 3200) ∧
    -Real.log (301 / 3200) ≤ (1181897913 / 500000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 301) = 1/(301 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_214 : (98784959 / 1000000000) ≤ -Real.log (2899 / 3200) ∧
    -Real.log (2899 / 3200) ≤ (308703 / 3125000) := by
  have h := checkLog_sound (w := (301 / 6099)) (n := 12)
    (lo := (98784959 / 1000000000)) (hi := (308703 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3200 / 2899) = 1/(2899 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_214 : (1132505431 / 1000000000) ≤ xi (301 / 3200) ∧ xi (301 / 3200) ≤ (2265010867 / 2000000000) ∧
    (2462580781 / 2000000000) ≤ kap (301 / 3200) ∧ kap (301 / 3200) ≤ (1231290393 / 1000000000) := by
  have h := endpoint_bounds (v := ((301 / 3200) : ℝ)) (by norm_num) (by norm_num)
    log_v_214.1 (by convert! log_c_214.1 using 1; norm_num)
    log_v_214.2 (by convert! log_c_214.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_215 : (234534853 / 100000000) ≤ -Real.log (14717 / 153600) ∧
    -Real.log (14717 / 153600) ≤ (1172674267 / 500000000) := by
  have h := checkLog_sound (w := (4483 / 33917)) (n := 12)
    (lo := (26590699 / 100000000)) (hi := (265906991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 14717) = 1/(14717 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_215 : (3147499 / 31250000) ≤ -Real.log (138883 / 153600) ∧
    -Real.log (138883 / 153600) ≤ (100719969 / 1000000000) := by
  have h := checkLog_sound (w := (14717 / 292483)) (n := 12)
    (lo := (3147499 / 31250000)) (hi := (100719969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 138883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 138883) = 1/(138883 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_215 : (2244628561 / 2000000000) ≤ xi (14717 / 153600) ∧ xi (14717 / 153600) ≤ (1122314283 / 1000000000) ∧
    (1223034249 / 1000000000) ≤ kap (14717 / 153600) ∧ kap (14717 / 153600) ≤ (2446068503 / 2000000000) := by
  have h := endpoint_bounds (v := ((14717 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_215.1 (by convert! log_c_215.1 using 1; norm_num)
    log_v_215.2 (by convert! log_c_215.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_216 : (2327235387 / 1000000000) ≤ -Real.log (7493 / 76800) ∧
    -Real.log (7493 / 76800) ≤ (2327235391 / 1000000000) := by
  have h := checkLog_sound (w := (2107 / 17093)) (n := 12)
    (lo := (247793847 / 1000000000)) (hi := (30974231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 7493) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(9600 / 7493) = 1/(7493 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_216 : (12832341 / 125000000) ≤ -Real.log (69307 / 76800) ∧
    -Real.log (69307 / 76800) ≤ (102658729 / 1000000000) := by
  have h := checkLog_sound (w := (7493 / 146107)) (n := 12)
    (lo := (12832341 / 125000000)) (hi := (102658729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 69307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 69307) = 1/(69307 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_216 : (1112288329 / 1000000000) ≤ xi (7493 / 76800) ∧ xi (7493 / 76800) ≤ (2224576663 / 2000000000) ∧
    (485978823 / 400000000) ≤ kap (7493 / 76800) ∧ kap (7493 / 76800) ≤ (60747353 / 50000000) := by
  have h := endpoint_bounds (v := ((7493 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_216.1 (by convert! log_c_216.1 using 1; norm_num)
    log_v_216.2 (by convert! log_c_216.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_217 : (4618889 / 2000000) ≤ -Real.log (1017 / 10240) ∧
    -Real.log (1017 / 10240) ≤ (288680563 / 125000000) := by
  have h := checkLog_sound (w := (263 / 2297)) (n := 12)
    (lo := (2875037 / 12500000)) (hi := (230002961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1017) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1280 / 1017) = 1/(1017 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_217 : (20920251 / 200000000) ≤ -Real.log (9223 / 10240) ∧
    -Real.log (9223 / 10240) ≤ (13075157 / 125000000) := by
  have h := checkLog_sound (w := (1017 / 19463)) (n := 12)
    (lo := (20920251 / 200000000)) (hi := (13075157 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 9223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 9223) = 1/(9223 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_217 : (551210811 / 500000000) ≤ xi (1017 / 10240) ∧ xi (1017 / 10240) ≤ (2204843249 / 2000000000) ∧
    (482809151 / 400000000) ≤ kap (1017 / 10240) ∧ kap (1017 / 10240) ≤ (7543893 / 6250000) := by
  have h := endpoint_bounds (v := ((1017 / 10240) : ℝ)) (by norm_num) (by norm_num)
    log_v_217.1 (by convert! log_c_217.1 using 1; norm_num)
    log_v_217.2 (by convert! log_c_217.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_218 : (458392921 / 200000000) ≤ -Real.log (3881 / 38400) ∧
    -Real.log (3881 / 38400) ≤ (2291964609 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 8681)) (n := 12)
    (lo := (42504613 / 200000000)) (hi := (106261533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3881) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4800 / 3881) = 1/(3881 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_218 : (53273781 / 500000000) ≤ -Real.log (34519 / 38400) ∧
    -Real.log (34519 / 38400) ≤ (106547563 / 1000000000) := by
  have h := checkLog_sound (w := (3881 / 72919)) (n := 12)
    (lo := (53273781 / 500000000)) (hi := (106547563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 34519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 34519) = 1/(34519 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_218 : (1092708521 / 1000000000) ≤ xi (3881 / 38400) ∧ xi (3881 / 38400) ≤ (2185417047 / 2000000000) ∧
    (2398512167 / 2000000000) ≤ kap (3881 / 38400) ∧ kap (3881 / 38400) ≤ (599628043 / 500000000) := by
  have h := endpoint_bounds (v := ((3881 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_218.1 (by convert! log_c_218.1 using 1; norm_num)
    log_v_218.2 (by convert! log_c_218.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_219 : (454957003 / 200000000) ≤ -Real.log (15793 / 153600) ∧
    -Real.log (15793 / 153600) ≤ (2274785019 / 1000000000) := by
  have h := checkLog_sound (w := (3407 / 34993)) (n := 12)
    (lo := (7813739 / 40000000)) (hi := (48835869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 15793) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 15793) = 1/(15793 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_219 : (21699533 / 200000000) ≤ -Real.log (137807 / 153600) ∧
    -Real.log (137807 / 153600) ≤ (54248833 / 500000000) := by
  have h := checkLog_sound (w := (15793 / 291407)) (n := 12)
    (lo := (21699533 / 200000000)) (hi := (54248833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 137807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 137807) = 1/(137807 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_219 : (2166287349 / 2000000000) ≤ xi (15793 / 153600) ∧ xi (15793 / 153600) ≤ (1083143677 / 1000000000) ∧
    (59582067 / 50000000) ≤ kap (15793 / 153600) ∧ kap (15793 / 153600) ≤ (476656537 / 400000000) := by
  have h := endpoint_bounds (v := ((15793 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_219.1 (by convert! log_c_219.1 using 1; norm_num)
    log_v_219.2 (by convert! log_c_219.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_220 : (451579117 / 200000000) ≤ -Real.log (2677 / 25600) ∧
    -Real.log (2677 / 25600) ≤ (2257895589 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 5877)) (n := 12)
    (lo := (35690809 / 200000000)) (hi := (89227023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2677) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2677) = 1/(2677 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_220 : (55225789 / 500000000) ≤ -Real.log (22923 / 25600) ∧
    -Real.log (22923 / 25600) ≤ (110451579 / 1000000000) := by
  have h := checkLog_sound (w := (2677 / 48523)) (n := 12)
    (lo := (55225789 / 500000000)) (hi := (110451579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 22923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 22923) = 1/(22923 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_220 : (1073722003 / 1000000000) ≤ xi (2677 / 25600) ∧ xi (2677 / 25600) ≤ (2147444011 / 2000000000) ∧
    (2368347163 / 2000000000) ≤ kap (2677 / 25600) ∧ kap (2677 / 25600) ≤ (74010849 / 62500000) := by
  have h := endpoint_bounds (v := ((2677 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_220.1 (by convert! log_c_220.1 using 1; norm_num)
    log_v_220.2 (by convert! log_c_220.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_221 : (560321669 / 250000000) ≤ -Real.log (16331 / 153600) ∧
    -Real.log (16331 / 153600) ≤ (56032167 / 25000000) := by
  have h := checkLog_sound (w := (2869 / 35531)) (n := 12)
    (lo := (10115321 / 62500000)) (hi := (161845137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 16331) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(19200 / 16331) = 1/(16331 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_221 : (28102329 / 250000000) ≤ -Real.log (137269 / 153600) ∧
    -Real.log (137269 / 153600) ≤ (112409317 / 1000000000) := by
  have h := checkLog_sound (w := (16331 / 290869)) (n := 12)
    (lo := (28102329 / 250000000)) (hi := (112409317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153600 / 137269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153600 / 137269) = 1/(137269 / 153600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_221 : (2128877359 / 2000000000) ≤ xi (16331 / 153600) ∧ xi (16331 / 153600) ≤ (532219341 / 500000000) ∧
    (294211999 / 250000000) ≤ kap (16331 / 153600) ∧ kap (16331 / 153600) ≤ (2353695997 / 2000000000) := by
  have h := endpoint_bounds (v := ((16331 / 153600) : ℝ)) (by norm_num) (by norm_num)
    log_v_221.1 (by convert! log_c_221.1 using 1; norm_num)
    log_v_221.2 (by convert! log_c_221.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_222 : (2224949123 / 1000000000) ≤ -Real.log (83 / 768) ∧
    -Real.log (83 / 768) ≤ (2224949127 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 179)) (n := 12)
    (lo := (145507583 / 1000000000)) (hi := (568389 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96 / 83) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(96 / 83) = 1/(83 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_222 : (57185447 / 500000000) ≤ -Real.log (685 / 768) ∧
    -Real.log (685 / 768) ≤ (22874179 / 200000000) := by
  have h := checkLog_sound (w := (83 / 1453)) (n := 12)
    (lo := (57185447 / 500000000)) (hi := (22874179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768 / 685) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768 / 685) = 1/(685 / 768) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_222 : (527644557 / 500000000) ≤ xi (83 / 768) ∧ xi (83 / 768) ≤ (2110578233 / 2000000000) ∧
    (2339320017 / 2000000000) ≤ kap (83 / 768) ∧ kap (83 / 768) ≤ (1169660011 / 1000000000) := by
  have h := endpoint_bounds (v := ((83 / 768) : ℝ)) (by norm_num) (by norm_num)
    log_v_222.1 (by convert! log_c_222.1 using 1; norm_num)
    log_v_222.2 (by convert! log_c_222.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_223 : (1096526799 / 500000000) ≤ -Real.log (8569 / 76800) ∧
    -Real.log (8569 / 76800) ≤ (1096526801 / 500000000) := by
  have h := checkLog_sound (w := (1031 / 18169)) (n := 12)
    (lo := (56806029 / 500000000)) (hi := (113612059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 8569) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(9600 / 8569) = 1/(8569 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_223 : (118305633 / 1000000000) ≤ -Real.log (68231 / 76800) ∧
    -Real.log (68231 / 76800) ≤ (59152817 / 500000000) := by
  have h := checkLog_sound (w := (8569 / 145031)) (n := 12)
    (lo := (118305633 / 1000000000)) (hi := (59152817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76800 / 68231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76800 / 68231) = 1/(68231 / 76800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_223 : (518686991 / 500000000) ≤ xi (8569 / 76800) ∧ xi (8569 / 76800) ≤ (2074747969 / 2000000000) ∧
    (2311359231 / 2000000000) ≤ kap (8569 / 76800) ∧ kap (8569 / 76800) ≤ (577839809 / 500000000) := by
  have h := endpoint_bounds (v := ((8569 / 76800) : ℝ)) (by norm_num) (by norm_num)
    log_v_223.1 (by convert! log_c_223.1 using 1; norm_num)
    log_v_223.2 (by convert! log_c_223.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


