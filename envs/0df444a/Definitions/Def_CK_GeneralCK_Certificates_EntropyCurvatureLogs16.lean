-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureLogs16
-- name    : CK_GeneralCK_Certificates_EntropyCurvatureLogs16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:47:11.639589+00:00
-- url     : https://prove2.me/theorems/2ce1022c-ca8b-435c-9e8b-5407c8849a42
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.EntropyCurvatureLogs16` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.EntropyCurvatureLogs16` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.EntropyCurvatureLogs16` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.EntropyCurvatureLogs16 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/EntropyCurvatureLogs16.lean)

import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureBounds

namespace GeneralCK.Certificates.EntropyCurvature
open Mixed GeneralCK.EntropyCurvature

theorem log_v_256 : (618578111 / 500000000) ≤ -Real.log (1393 / 4800) ∧
    -Real.log (1393 / 4800) ≤ (9665283 / 7812500) := by
  have h := checkLog_sound (w := (1007 / 3793)) (n := 12)
    (lo := (272004521 / 500000000)) (hi := (544009043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400 / 1393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2400 / 1393) = 1/(1393 / 4800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_256 : (342783779 / 1000000000) ≤ -Real.log (3407 / 4800) ∧
    -Real.log (3407 / 4800) ≤ (17139189 / 50000000) := by
  have h := checkLog_sound (w := (1393 / 8207)) (n := 12)
    (lo := (342783779 / 1000000000)) (hi := (17139189 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4800 / 3407) = 1/(3407 / 4800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_256 : (447186221 / 1000000000) ≤ xi (1393 / 4800) ∧ xi (1393 / 4800) ≤ (178874489 / 400000000) ∧
    (1579940001 / 2000000000) ≤ kap (1393 / 4800) ∧ kap (1393 / 4800) ≤ (394985001 / 500000000) := by
  have h := endpoint_bounds (v := ((1393 / 4800) : ℝ)) (by norm_num) (by norm_num)
    log_v_256.1 (by convert! log_c_256.1 using 1; norm_num)
    log_v_256.2 (by convert! log_c_256.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_257 : (606652201 / 500000000) ≤ -Real.log (11413 / 38400) ∧
    -Real.log (11413 / 38400) ≤ (303326101 / 250000000) := by
  have h := checkLog_sound (w := (7787 / 30613)) (n := 12)
    (lo := (260078611 / 500000000)) (hi := (520157223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 11413) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 11413) = 1/(11413 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_257 : (352702191 / 1000000000) ≤ -Real.log (26987 / 38400) ∧
    -Real.log (26987 / 38400) ≤ (22043887 / 62500000) := by
  have h := checkLog_sound (w := (11413 / 65387)) (n := 12)
    (lo := (352702191 / 1000000000)) (hi := (22043887 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 26987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 26987) = 1/(26987 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_257 : (86060221 / 200000000) ≤ xi (11413 / 38400) ∧ xi (11413 / 38400) ≤ (860602213 / 2000000000) ∧
    (1566006593 / 2000000000) ≤ kap (11413 / 38400) ∧ kap (11413 / 38400) ≤ (391501649 / 500000000) := by
  have h := endpoint_bounds (v := ((11413 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_257.1 (by convert! log_c_257.1 using 1; norm_num)
    log_v_257.2 (by convert! log_c_257.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_258 : (1190008263 / 1000000000) ≤ -Real.log (1947 / 6400) ∧
    -Real.log (1947 / 6400) ≤ (238001653 / 200000000) := by
  have h := checkLog_sound (w := (1253 / 5147)) (n := 12)
    (lo := (496861083 / 1000000000)) (hi := (124215271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1947) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3200 / 1947) = 1/(1947 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_258 : (90679991 / 250000000) ≤ -Real.log (4453 / 6400) ∧
    -Real.log (4453 / 6400) ≤ (72543993 / 200000000) := by
  have h := checkLog_sound (w := (1947 / 10853)) (n := 12)
    (lo := (90679991 / 250000000)) (hi := (72543993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6400 / 4453) = 1/(4453 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_258 : (413644149 / 1000000000) ≤ xi (1947 / 6400) ∧ xi (1947 / 6400) ≤ (827288301 / 2000000000) ∧
    (1552728227 / 2000000000) ≤ kap (1947 / 6400) ∧ kap (1947 / 6400) ≤ (155272823 / 200000000) := by
  have h := endpoint_bounds (v := ((1947 / 6400) : ℝ)) (by norm_num) (by norm_num)
    log_v_258.1 (by convert! log_c_258.1 using 1; norm_num)
    log_v_258.2 (by convert! log_c_258.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_259 : (583621251 / 500000000) ≤ -Real.log (11951 / 38400) ∧
    -Real.log (11951 / 38400) ≤ (145905313 / 125000000) := by
  have h := checkLog_sound (w := (7249 / 31151)) (n := 12)
    (lo := (237047661 / 500000000)) (hi := (474095323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 11951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 11951) = 1/(11951 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_259 : (372839109 / 1000000000) ≤ -Real.log (26449 / 38400) ∧
    -Real.log (26449 / 38400) ≤ (37283911 / 100000000) := by
  have h := checkLog_sound (w := (11951 / 64849)) (n := 12)
    (lo := (372839109 / 1000000000)) (hi := (37283911 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 26449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 26449) = 1/(26449 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_259 : (12412553 / 31250000) ≤ xi (11951 / 38400) ∧ xi (11951 / 38400) ≤ (158880679 / 400000000) ∧
    (1540081611 / 2000000000) ≤ kap (11951 / 38400) ∧ kap (11951 / 38400) ≤ (770040807 / 1000000000) := by
  have h := endpoint_bounds (v := ((11951 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_259.1 (by convert! log_c_259.1 using 1; norm_num)
    log_v_259.2 (by convert! log_c_259.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_260 : (228996701 / 200000000) ≤ -Real.log (611 / 1920) ∧
    -Real.log (611 / 1920) ≤ (1144983507 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1571)) (n := 12)
    (lo := (18073453 / 40000000)) (hi := (225918163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960 / 611) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(960 / 611) = 1/(611 / 1920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_260 : (383061699 / 1000000000) ≤ -Real.log (1309 / 1920) ∧
    -Real.log (1309 / 1920) ≤ (3830617 / 10000000) := by
  have h := checkLog_sound (w := (611 / 3229)) (n := 12)
    (lo := (383061699 / 1000000000)) (hi := (3830617 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920 / 1309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1920 / 1309) = 1/(1309 / 1920) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_260 : (152384361 / 400000000) ≤ xi (611 / 1920) ∧ xi (611 / 1920) ≤ (47620113 / 125000000) ∧
    (382011301 / 500000000) ≤ kap (611 / 1920) ∧ kap (611 / 1920) ≤ (1528045207 / 2000000000) := by
  have h := endpoint_bounds (v := ((611 / 1920) : ℝ)) (by norm_num) (by norm_num)
    log_v_260.1 (by convert! log_c_260.1 using 1; norm_num)
    log_v_260.2 (by convert! log_c_260.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_261 : (561604601 / 500000000) ≤ -Real.log (4163 / 12800) ∧
    -Real.log (4163 / 12800) ≤ (280802301 / 250000000) := by
  have h := checkLog_sound (w := (2237 / 10563)) (n := 12)
    (lo := (215031011 / 500000000)) (hi := (430062023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4163) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6400 / 4163) = 1/(4163 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_261 : (39338987 / 100000000) ≤ -Real.log (8637 / 12800) ∧
    -Real.log (8637 / 12800) ≤ (393389871 / 1000000000) := by
  have h := checkLog_sound (w := (4163 / 21437)) (n := 12)
    (lo := (39338987 / 100000000)) (hi := (393389871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 8637) = 1/(8637 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_261 : (729819331 / 2000000000) ≤ xi (4163 / 12800) ∧ xi (4163 / 12800) ≤ (364909667 / 1000000000) ∧
    (47393721 / 62500000) ≤ kap (4163 / 12800) ∧ kap (4163 / 12800) ≤ (60663963 / 80000000) := by
  have h := endpoint_bounds (v := ((4163 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_261.1 (by convert! log_c_261.1 using 1; norm_num)
    log_v_261.2 (by convert! log_c_261.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_262 : (1101898933 / 1000000000) ≤ -Real.log (6379 / 19200) ∧
    -Real.log (6379 / 19200) ≤ (220379787 / 200000000) := by
  have h := checkLog_sound (w := (3221 / 15979)) (n := 12)
    (lo := (408751753 / 1000000000)) (hi := (204375877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6379) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9600 / 6379) = 1/(6379 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_262 : (403825827 / 1000000000) ≤ -Real.log (12821 / 19200) ∧
    -Real.log (12821 / 19200) ≤ (100956457 / 250000000) := by
  have h := checkLog_sound (w := (6379 / 32021)) (n := 12)
    (lo := (403825827 / 1000000000)) (hi := (100956457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 12821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 12821) = 1/(12821 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_262 : (139614621 / 400000000) ≤ xi (6379 / 19200) ∧ xi (6379 / 19200) ≤ (174518277 / 500000000) ∧
    (37643119 / 50000000) ≤ kap (6379 / 19200) ∧ kap (6379 / 19200) ≤ (1505724763 / 2000000000) := by
  have h := endpoint_bounds (v := ((6379 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_262.1 (by convert! log_c_262.1 using 1; norm_num)
    log_v_262.2 (by convert! log_c_262.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_263 : (270258333 / 250000000) ≤ -Real.log (13027 / 38400) ∧
    -Real.log (13027 / 38400) ≤ (540516667 / 500000000) := by
  have h := checkLog_sound (w := (6173 / 32227)) (n := 12)
    (lo := (48485769 / 125000000)) (hi := (387886153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 13027) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 13027) = 1/(13027 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_263 : (414371843 / 1000000000) ≤ -Real.log (25373 / 38400) ∧
    -Real.log (25373 / 38400) ≤ (103592961 / 250000000) := by
  have h := checkLog_sound (w := (13027 / 63773)) (n := 12)
    (lo := (414371843 / 1000000000)) (hi := (103592961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 25373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 25373) = 1/(25373 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_263 : (41666343 / 125000000) ≤ xi (13027 / 38400) ∧ xi (13027 / 38400) ≤ (666661491 / 2000000000) ∧
    (59816207 / 80000000) ≤ kap (13027 / 38400) ∧ kap (13027 / 38400) ≤ (747702589 / 1000000000) := by
  have h := endpoint_bounds (v := ((13027 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_263.1 (by convert! log_c_263.1 using 1; norm_num)
    log_v_263.2 (by convert! log_c_263.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_264 : (53029711 / 50000000) ≤ -Real.log (277 / 800) ∧
    -Real.log (277 / 800) ≤ (530297111 / 500000000) := by
  have h := checkLog_sound (w := (123 / 677)) (n := 12)
    (lo := (143534 / 390625)) (hi := (367447041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 277) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 277) = 1/(277 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_264 : (425030263 / 1000000000) ≤ -Real.log (523 / 800) ∧
    -Real.log (523 / 800) ≤ (53128783 / 125000000) := by
  have h := checkLog_sound (w := (277 / 1323)) (n := 12)
    (lo := (425030263 / 1000000000)) (hi := (53128783 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 523) = 1/(523 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_264 : (158890989 / 500000000) ≤ xi (277 / 800) ∧ xi (277 / 800) ≤ (635563959 / 2000000000) ∧
    (1485624483 / 2000000000) ≤ kap (277 / 800) ∧ kap (277 / 800) ≤ (742812243 / 1000000000) := by
  have h := endpoint_bounds (v := ((277 / 800) : ℝ)) (by norm_num) (by norm_num)
    log_v_264.1 (by convert! log_c_264.1 using 1; norm_num)
    log_v_264.2 (by convert! log_c_264.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_265 : (32517641 / 31250000) ≤ -Real.log (2713 / 7680) ∧
    -Real.log (2713 / 7680) ≤ (520282257 / 500000000) := by
  have h := checkLog_sound (w := (1127 / 6553)) (n := 12)
    (lo := (86854333 / 250000000)) (hi := (347417333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3840 / 2713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3840 / 2713) = 1/(2713 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_265 : (435803511 / 1000000000) ≤ -Real.log (4967 / 7680) ∧
    -Real.log (4967 / 7680) ≤ (54475439 / 125000000) := by
  have h := checkLog_sound (w := (2713 / 12647)) (n := 12)
    (lo := (435803511 / 1000000000)) (hi := (54475439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7680 / 4967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7680 / 4967) = 1/(4967 / 7680) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_265 : (604761 / 2000000) ≤ xi (2713 / 7680) ∧ xi (2713 / 7680) ≤ (604761003 / 2000000000) ∧
    (1476368023 / 2000000000) ≤ kap (2713 / 7680) ∧ kap (2713 / 7680) ≤ (738184013 / 1000000000) := by
  have h := endpoint_bounds (v := ((2713 / 7680) : ℝ)) (by norm_num) (by norm_num)
    log_v_265.1 (by convert! log_c_265.1 using 1; norm_num)
    log_v_265.2 (by convert! log_c_265.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_266 : (7976001 / 7812500) ≤ -Real.log (6917 / 19200) ∧
    -Real.log (6917 / 19200) ≤ (102092813 / 100000000) := by
  have h := checkLog_sound (w := (2683 / 16517)) (n := 12)
    (lo := (81945237 / 250000000)) (hi := (327780949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6917) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9600 / 6917) = 1/(6917 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_266 : (223347043 / 500000000) ≤ -Real.log (12283 / 19200) ∧
    -Real.log (12283 / 19200) ≤ (446694087 / 1000000000) := by
  have h := checkLog_sound (w := (6917 / 31483)) (n := 12)
    (lo := (223347043 / 500000000)) (hi := (446694087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 12283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19200 / 12283) = 1/(12283 / 19200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_266 : (574234041 / 2000000000) ≤ xi (6917 / 19200) ∧ xi (6917 / 19200) ≤ (143558511 / 500000000) ∧
    (733811107 / 1000000000) ≤ kap (6917 / 19200) ∧ kap (6917 / 19200) ≤ (1467622217 / 2000000000) := by
  have h := endpoint_bounds (v := ((6917 / 19200) : ℝ)) (by norm_num) (by norm_num)
    log_v_266.1 (by convert! log_c_266.1 using 1; norm_num)
    log_v_266.2 (by convert! log_c_266.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_267 : (500834959 / 500000000) ≤ -Real.log (4701 / 12800) ∧
    -Real.log (4701 / 12800) ≤ (6260437 / 6250000) := by
  have h := checkLog_sound (w := (1699 / 11101)) (n := 12)
    (lo := (154261369 / 500000000)) (hi := (308522739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4701) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6400 / 4701) = 1/(4701 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_267 : (457704573 / 1000000000) ≤ -Real.log (8099 / 12800) ∧
    -Real.log (8099 / 12800) ≤ (228852287 / 500000000) := by
  have h := checkLog_sound (w := (4701 / 20899)) (n := 12)
    (lo := (457704573 / 1000000000)) (hi := (228852287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12800 / 8099) = 1/(8099 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_267 : (16998917 / 62500000) ≤ xi (4701 / 12800) ∧ xi (4701 / 12800) ≤ (543965347 / 2000000000) ∧
    (1459374491 / 2000000000) ≤ kap (4701 / 12800) ∧ kap (4701 / 12800) ≤ (729687247 / 1000000000) := by
  have h := endpoint_bounds (v := ((4701 / 12800) : ℝ)) (by norm_num) (by norm_num)
    log_v_267.1 (by convert! log_c_267.1 using 1; norm_num)
    log_v_267.2 (by convert! log_c_267.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_268 : (99217813 / 100000000) ≤ -Real.log (1139 / 3072) ∧
    -Real.log (1139 / 3072) ≤ (248044533 / 250000000) := by
  have h := checkLog_sound (w := (397 / 2675)) (n := 12)
    (lo := (5980619 / 20000000)) (hi := (299030951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1536 / 1139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1536 / 1139) = 1/(1139 / 3072) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_268 : (92651123 / 200000000) ≤ -Real.log (1933 / 3072) ∧
    -Real.log (1933 / 3072) ≤ (7238369 / 15625000) := by
  have h := checkLog_sound (w := (1139 / 5005)) (n := 12)
    (lo := (92651123 / 200000000)) (hi := (7238369 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3072 / 1933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3072 / 1933) = 1/(1933 / 3072) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_268 : (264461257 / 1000000000) ≤ xi (1139 / 3072) ∧ xi (1139 / 3072) ≤ (528922517 / 2000000000) ∧
    (291086749 / 400000000) ≤ kap (1139 / 3072) ∧ kap (1139 / 3072) ≤ (363858437 / 500000000) := by
  have h := endpoint_bounds (v := ((1139 / 3072) : ℝ)) (by norm_num) (by norm_num)
    log_v_268.1 (by convert! log_c_268.1 using 1; norm_num)
    log_v_268.2 (by convert! log_c_268.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_269 : (982775589 / 1000000000) ≤ -Real.log (3593 / 9600) ∧
    -Real.log (3593 / 9600) ≤ (982775591 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 8393)) (n := 12)
    (lo := (289628409 / 1000000000)) (hi := (28962841 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4800 / 3593) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4800 / 3593) = 1/(3593 / 9600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_269 : (234418821 / 500000000) ≤ -Real.log (6007 / 9600) ∧
    -Real.log (6007 / 9600) ≤ (468837643 / 1000000000) := by
  have h := checkLog_sound (w := (3593 / 15607)) (n := 12)
    (lo := (234418821 / 500000000)) (hi := (468837643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9600 / 6007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9600 / 6007) = 1/(6007 / 9600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_269 : (256968973 / 1000000000) ≤ xi (3593 / 9600) ∧ xi (3593 / 9600) ≤ (513937949 / 2000000000) ∧
    (1451613231 / 2000000000) ≤ kap (3593 / 9600) ∧ kap (3593 / 9600) ≤ (725806617 / 1000000000) := by
  have h := endpoint_bounds (v := ((3593 / 9600) : ℝ)) (by norm_num) (by norm_num)
    log_v_269.1 (by convert! log_c_269.1 using 1; norm_num)
    log_v_269.2 (by convert! log_c_269.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_270 : (486730317 / 500000000) ≤ -Real.log (9671 / 25600) ∧
    -Real.log (9671 / 25600) ≤ (243365159 / 250000000) := by
  have h := checkLog_sound (w := (3129 / 22471)) (n := 12)
    (lo := (140156727 / 500000000)) (hi := (56062691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12800 / 9671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12800 / 9671) = 1/(9671 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_270 : (118612751 / 250000000) ≤ -Real.log (15929 / 25600) ∧
    -Real.log (15929 / 25600) ≤ (94890201 / 200000000) := by
  have h := checkLog_sound (w := (9671 / 41529)) (n := 12)
    (lo := (118612751 / 250000000)) (hi := (94890201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25600 / 15929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25600 / 15929) = 1/(15929 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_270 : (499009629 / 2000000000) ≤ xi (9671 / 25600) ∧ xi (9671 / 25600) ≤ (15594051 / 62500000) ∧
    (723955819 / 1000000000) ≤ kap (9671 / 25600) ∧ kap (9671 / 25600) ≤ (1447911641 / 2000000000) := by
  have h := endpoint_bounds (v := ((9671 / 25600) : ℝ)) (by norm_num) (by norm_num)
    log_v_270.1 (by convert! log_c_270.1 using 1; norm_num)
    log_v_270.2 (by convert! log_c_270.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

theorem log_v_271 : (482115823 / 500000000) ≤ -Real.log (14641 / 38400) ∧
    -Real.log (14641 / 38400) ≤ (30132239 / 31250000) := by
  have h := checkLog_sound (w := (4559 / 33841)) (n := 12)
    (lo := (135542233 / 500000000)) (hi := (271084467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19200 / 14641) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(19200 / 14641) = 1/(14641 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_c_271 : (480096053 / 1000000000) ≤ -Real.log (23759 / 38400) ∧
    -Real.log (23759 / 38400) ≤ (240048027 / 500000000) := by
  have h := checkLog_sound (w := (14641 / 62159)) (n := 12)
    (lo := (480096053 / 1000000000)) (hi := (240048027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38400 / 23759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38400 / 23759) = 1/(23759 / 38400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem endpoint_271 : (60516949 / 250000000) ≤ xi (14641 / 38400) ∧ xi (14641 / 38400) ≤ (96827119 / 400000000) ∧
    (1444327699 / 2000000000) ≤ kap (14641 / 38400) ∧ kap (14641 / 38400) ≤ (722163851 / 1000000000) := by
  have h := endpoint_bounds (v := ((14641 / 38400) : ℝ)) (by norm_num) (by norm_num)
    log_v_271.1 (by convert! log_c_271.1 using 1; norm_num)
    log_v_271.2 (by convert! log_c_271.2 using 1; norm_num)
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.EntropyCurvature


