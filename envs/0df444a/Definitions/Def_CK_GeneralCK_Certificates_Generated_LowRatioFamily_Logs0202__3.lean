-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0202__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0202__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:39:38.46991+00:00
-- url     : https://prove2.me/theorems/4d427e38-891a-479d-9cbb-937dcf3622ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0202 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0203, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0202 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0203, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0204)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0202 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0203, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0204)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0202 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0203, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0204) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0202 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0203, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0204).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0202 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12928_neg : (659454093 / 500000000) ≤ -Real.log (100000000000 / 373933649289) ∧
    -Real.log (100000000000 / 373933649289) ≤ (329727047 / 250000000) := by
  have h := checkLog_sound (w := (173933649289 / 573933649289)) (n := 12)
    (lo := (312880503 / 500000000)) (hi := (625761007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373933649289 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(373933649289 / 200000000000) = 1/(100000000000 / 373933649289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12928 : Bounds (659454093 / 500000000) (329727047 / 250000000) (Real.log (373933649289 / 100000000000)) := by
  have h := reflection_log_12928_neg
  have he : Real.log (373933649289 / 100000000000) = -Real.log (100000000000 / 373933649289) := by
    rw [show ((373933649289 / 100000000000) : ℝ) = ((100000000000 / 373933649289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12929_neg : (331985479 / 250000000) ≤ -Real.log (500000000000 / 1886634844869) ∧
    -Real.log (500000000000 / 1886634844869) ≤ (663970959 / 500000000) := by
  have h := checkLog_sound (w := (886634844869 / 2886634844869)) (n := 12)
    (lo := (39674671 / 62500000)) (hi := (634794737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886634844869 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1886634844869 / 1000000000000) = 1/(500000000000 / 1886634844869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12929 : Bounds (331985479 / 250000000) (663970959 / 500000000) (Real.log (1886634844869 / 500000000000)) := by
  have h := reflection_log_12929_neg
  have he : Real.log (1886634844869 / 500000000000) = -Real.log (500000000000 / 1886634844869) := by
    rw [show ((1886634844869 / 500000000000) : ℝ) = ((500000000000 / 1886634844869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12930_neg : (459953293 / 1000000000) ≤ -Real.log (125 / 198) ∧
    -Real.log (125 / 198) ≤ (229976647 / 500000000) := by
  have h := checkLog_sound (w := (73 / 323)) (n := 12)
    (lo := (459953293 / 1000000000)) (hi := (229976647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198 / 125) = 1/(125 / 198) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12930 : Bounds (459953293 / 1000000000) (229976647 / 500000000) (Real.log (198 / 125)) := by
  have h := reflection_log_12930_neg
  have he : Real.log (198 / 125) = -Real.log (125 / 198) := by
    rw [show ((198 / 125) : ℝ) = ((125 / 198) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12931_neg : (438535009 / 500000000) ≤ -Real.log (52 / 125) ∧
    -Real.log (52 / 125) ≤ (43853501 / 50000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 104) = 1/(52 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12931 : Bounds (-43853501 / 50000000) (-438535009 / 500000000) (Real.log (52 / 125)) := by
  have h := reflection_log_12931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12932_neg : (583829 / 1000000000) ≤ -Real.log (125000 / 125073) ∧
    -Real.log (125000 / 125073) ≤ (58383 / 100000000) := by
  have h := checkLog_sound (w := (73 / 250073)) (n := 12)
    (lo := (583829 / 1000000000)) (hi := (58383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125073 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125073 / 125000) = 1/(125000 / 125073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12932 : Bounds (583829 / 1000000000) (58383 / 100000000) (Real.log (125073 / 125000)) := by
  have h := reflection_log_12932_neg
  have he : Real.log (125073 / 125000) = -Real.log (125000 / 125073) := by
    rw [show ((125073 / 125000) : ℝ) = ((125000 / 125073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12933_neg : (58417 / 100000000) ≤ -Real.log (124927 / 125000) ∧
    -Real.log (124927 / 125000) ≤ (584171 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 249927)) (n := 12)
    (lo := (58417 / 100000000)) (hi := (584171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124927) = 1/(124927 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12933 : Bounds (-584171 / 1000000000) (-58417 / 100000000) (Real.log (124927 / 125000)) := by
  have h := reflection_log_12933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12934_neg : (270008053 / 1000000000) ≤ -Real.log (40000 / 52399) ∧
    -Real.log (40000 / 52399) ≤ (135004027 / 500000000) := by
  have h := checkLog_sound (w := (12399 / 92399)) (n := 12)
    (lo := (270008053 / 1000000000)) (hi := (135004027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52399 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52399 / 40000) = 1/(40000 / 52399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12934 : Bounds (270008053 / 1000000000) (135004027 / 500000000) (Real.log (52399 / 40000)) := by
  have h := reflection_log_12934_neg
  have he : Real.log (52399 / 40000) = -Real.log (40000 / 52399) := by
    rw [show ((52399 / 40000) : ℝ) = ((40000 / 52399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12935_neg : (7420549 / 20000000) ≤ -Real.log (27601 / 40000) ∧
    -Real.log (27601 / 40000) ≤ (371027451 / 1000000000) := by
  have h := checkLog_sound (w := (12399 / 67601)) (n := 12)
    (lo := (7420549 / 20000000)) (hi := (371027451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 27601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 27601) = 1/(27601 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12935 : Bounds (-371027451 / 1000000000) (-7420549 / 20000000) (Real.log (27601 / 40000)) := by
  have h := reflection_log_12935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12936_neg : (271817899 / 1000000000) ≤ -Real.log (250000 / 328087) ∧
    -Real.log (250000 / 328087) ≤ (2718179 / 10000000) := by
  have h := checkLog_sound (w := (78087 / 578087)) (n := 12)
    (lo := (271817899 / 1000000000)) (hi := (2718179 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328087 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328087 / 250000) = 1/(250000 / 328087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12936 : Bounds (271817899 / 1000000000) (2718179 / 10000000) (Real.log (328087 / 250000)) := by
  have h := reflection_log_12936_neg
  have he : Real.log (328087 / 250000) = -Real.log (250000 / 328087) := by
    rw [show ((328087 / 250000) : ℝ) = ((250000 / 328087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12937_neg : (187236191 / 500000000) ≤ -Real.log (171913 / 250000) ∧
    -Real.log (171913 / 250000) ≤ (374472383 / 1000000000) := by
  have h := checkLog_sound (w := (78087 / 421913)) (n := 12)
    (lo := (187236191 / 500000000)) (hi := (374472383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171913) = 1/(171913 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12937 : Bounds (-374472383 / 1000000000) (-187236191 / 500000000) (Real.log (171913 / 250000)) := by
  have h := reflection_log_12937_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12938_neg : (102654483 / 1000000000) ≤ -Real.log (56402420431 / 62500000000) ∧
    -Real.log (56402420431 / 62500000000) ≤ (25663621 / 250000000) := by
  have h := checkLog_sound (w := (6097579569 / 118902420431)) (n := 12)
    (lo := (102654483 / 1000000000)) (hi := (25663621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56402420431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56402420431) = 1/(56402420431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12938 : Bounds (-25663621 / 250000000) (-102654483 / 1000000000) (Real.log (56402420431 / 62500000000)) := by
  have h := reflection_log_12938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12939_neg : (101019397 / 1000000000) ≤ -Real.log (1446264799 / 1600000000) ∧
    -Real.log (1446264799 / 1600000000) ≤ (50509699 / 500000000) := by
  have h := checkLog_sound (w := (153735201 / 3046264799)) (n := 12)
    (lo := (101019397 / 1000000000)) (hi := (50509699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1446264799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1446264799) = 1/(1446264799 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12939 : Bounds (-50509699 / 500000000) (-101019397 / 1000000000) (Real.log (1446264799 / 1600000000)) := by
  have h := reflection_log_12939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12940_neg : (641035503 / 1000000000) ≤ -Real.log (125000000000 / 237305713561) ∧
    -Real.log (125000000000 / 237305713561) ≤ (40064719 / 62500000) := by
  have h := checkLog_sound (w := (112305713561 / 362305713561)) (n := 12)
    (lo := (641035503 / 1000000000)) (hi := (40064719 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237305713561 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237305713561 / 125000000000) = 1/(125000000000 / 237305713561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12940 : Bounds (641035503 / 1000000000) (40064719 / 62500000) (Real.log (237305713561 / 125000000000)) := by
  have h := reflection_log_12940_neg
  have he : Real.log (237305713561 / 125000000000) = -Real.log (125000000000 / 237305713561) := by
    rw [show ((237305713561 / 125000000000) : ℝ) = ((125000000000 / 237305713561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12941_neg : (323145141 / 500000000) ≤ -Real.log (500000000000 / 954223938853) ∧
    -Real.log (500000000000 / 954223938853) ≤ (646290283 / 1000000000) := by
  have h := checkLog_sound (w := (454223938853 / 1454223938853)) (n := 12)
    (lo := (323145141 / 500000000)) (hi := (646290283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((954223938853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(954223938853 / 500000000000) = 1/(500000000000 / 954223938853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12941 : Bounds (323145141 / 500000000) (646290283 / 1000000000) (Real.log (954223938853 / 500000000000)) := by
  have h := reflection_log_12941_neg
  have he : Real.log (954223938853 / 500000000000) = -Real.log (500000000000 / 954223938853) := by
    rw [show ((954223938853 / 500000000000) : ℝ) = ((500000000000 / 954223938853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12942_neg : (331985479 / 250000000) ≤ -Real.log (125000000000 / 471658711217) ∧
    -Real.log (125000000000 / 471658711217) ≤ (663970959 / 500000000) := by
  have h := checkLog_sound (w := (221658711217 / 721658711217)) (n := 12)
    (lo := (39674671 / 62500000)) (hi := (634794737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471658711217 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(471658711217 / 250000000000) = 1/(125000000000 / 471658711217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12942 : Bounds (331985479 / 250000000) (663970959 / 500000000) (Real.log (471658711217 / 125000000000)) := by
  have h := reflection_log_12942_neg
  have he : Real.log (471658711217 / 125000000000) = -Real.log (125000000000 / 471658711217) := by
    rw [show ((471658711217 / 125000000000) : ℝ) = ((125000000000 / 471658711217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12943_neg : (1337023311 / 1000000000) ≤ -Real.log (500000000000 / 1903846153847) ∧
    -Real.log (500000000000 / 1903846153847) ≤ (1337023313 / 1000000000) := by
  have h := checkLog_sound (w := (903846153847 / 2903846153847)) (n := 12)
    (lo := (643876131 / 1000000000)) (hi := (160969033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903846153847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1903846153847 / 1000000000000) = 1/(500000000000 / 1903846153847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12943 : Bounds (1337023311 / 1000000000) (1337023313 / 1000000000) (Real.log (1903846153847 / 500000000000)) := by
  have h := reflection_log_12943_neg
  have he : Real.log (1903846153847 / 500000000000) = -Real.log (500000000000 / 1903846153847) := by
    rw [show ((1903846153847 / 500000000000) : ℝ) = ((500000000000 / 1903846153847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12944_neg : (461845441 / 1000000000) ≤ -Real.log (1000 / 1587) ∧
    -Real.log (1000 / 1587) ≤ (230922721 / 500000000) := by
  have h := checkLog_sound (w := (587 / 2587)) (n := 12)
    (lo := (461845441 / 1000000000)) (hi := (230922721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1587 / 1000) = 1/(1000 / 1587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12944 : Bounds (461845441 / 1000000000) (230922721 / 500000000) (Real.log (1587 / 1000)) := by
  have h := reflection_log_12944_neg
  have he : Real.log (1587 / 1000) = -Real.log (1000 / 1587) := by
    rw [show ((1587 / 1000) : ℝ) = ((1000 / 1587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12945_neg : (176861537 / 200000000) ≤ -Real.log (413 / 1000) ∧
    -Real.log (413 / 1000) ≤ (884307687 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 913)) (n := 12)
    (lo := (38232101 / 200000000)) (hi := (95580253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 413) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 413) = 1/(413 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12945 : Bounds (-884307687 / 1000000000) (-176861537 / 200000000) (Real.log (413 / 1000)) := by
  have h := reflection_log_12945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12946_neg : (586827 / 1000000000) ≤ -Real.log (1000000 / 1000587) ∧
    -Real.log (1000000 / 1000587) ≤ (146707 / 250000000) := by
  have h := checkLog_sound (w := (587 / 2000587)) (n := 12)
    (lo := (586827 / 1000000000)) (hi := (146707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000587 / 1000000) = 1/(1000000 / 1000587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12946 : Bounds (586827 / 1000000000) (146707 / 250000000) (Real.log (1000587 / 1000000)) := by
  have h := reflection_log_12946_neg
  have he : Real.log (1000587 / 1000000) = -Real.log (1000000 / 1000587) := by
    rw [show ((1000587 / 1000000) : ℝ) = ((1000000 / 1000587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12947_neg : (146793 / 250000000) ≤ -Real.log (999413 / 1000000) ∧
    -Real.log (999413 / 1000000) ≤ (587173 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 1999413)) (n := 12)
    (lo := (146793 / 250000000)) (hi := (587173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999413) = 1/(999413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12947 : Bounds (-587173 / 1000000000) (-146793 / 250000000) (Real.log (999413 / 1000000)) := by
  have h := reflection_log_12947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12948_neg : (33925697 / 125000000) ≤ -Real.log (1000000 / 1311807) ∧
    -Real.log (1000000 / 1311807) ≤ (271405577 / 1000000000) := by
  have h := checkLog_sound (w := (311807 / 2311807)) (n := 12)
    (lo := (33925697 / 125000000)) (hi := (271405577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311807 / 1000000) = 1/(1000000 / 1311807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12948 : Bounds (33925697 / 125000000) (271405577 / 1000000000) (Real.log (1311807 / 1000000)) := by
  have h := reflection_log_12948_neg
  have he : Real.log (1311807 / 1000000) = -Real.log (1000000 / 1311807) := by
    rw [show ((1311807 / 1000000) : ℝ) = ((1000000 / 1311807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12949_neg : (373685957 / 1000000000) ≤ -Real.log (688193 / 1000000) ∧
    -Real.log (688193 / 1000000) ≤ (186842979 / 500000000) := by
  have h := checkLog_sound (w := (311807 / 1688193)) (n := 12)
    (lo := (373685957 / 1000000000)) (hi := (186842979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688193) = 1/(688193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12949 : Bounds (-186842979 / 500000000) (-373685957 / 1000000000) (Real.log (688193 / 1000000)) := by
  have h := reflection_log_12949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12950_neg : (136608731 / 500000000) ≤ -Real.log (500000 / 657093) ∧
    -Real.log (500000 / 657093) ≤ (273217463 / 1000000000) := by
  have h := checkLog_sound (w := (157093 / 1157093)) (n := 12)
    (lo := (136608731 / 500000000)) (hi := (273217463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657093 / 500000) = 1/(500000 / 657093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12950 : Bounds (136608731 / 500000000) (273217463 / 1000000000) (Real.log (657093 / 500000)) := by
  have h := reflection_log_12950_neg
  have he : Real.log (657093 / 500000) = -Real.log (500000 / 657093) := by
    rw [show ((657093 / 500000) : ℝ) = ((500000 / 657093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12951_neg : (15085953 / 40000000) ≤ -Real.log (342907 / 500000) ∧
    -Real.log (342907 / 500000) ≤ (188574413 / 500000000) := by
  have h := checkLog_sound (w := (157093 / 842907)) (n := 12)
    (lo := (15085953 / 40000000)) (hi := (188574413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342907) = 1/(342907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12951 : Bounds (-188574413 / 500000000) (-15085953 / 40000000) (Real.log (342907 / 500000)) := by
  have h := reflection_log_12951_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12952_neg : (51965681 / 500000000) ≤ -Real.log (225321789351 / 250000000000) ∧
    -Real.log (225321789351 / 250000000000) ≤ (103931363 / 1000000000) := by
  have h := checkLog_sound (w := (24678210649 / 475321789351)) (n := 12)
    (lo := (51965681 / 500000000)) (hi := (103931363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 225321789351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 225321789351) = 1/(225321789351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12952 : Bounds (-103931363 / 1000000000) (-51965681 / 500000000) (Real.log (225321789351 / 250000000000)) := by
  have h := reflection_log_12952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12953_neg : (102280381 / 1000000000) ≤ -Real.log (902776394751 / 1000000000000) ∧
    -Real.log (902776394751 / 1000000000000) ≤ (51140191 / 500000000) := by
  have h := checkLog_sound (w := (97223605249 / 1902776394751)) (n := 12)
    (lo := (102280381 / 1000000000)) (hi := (51140191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 902776394751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 902776394751) = 1/(902776394751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12953 : Bounds (-51140191 / 500000000) (-102280381 / 1000000000) (Real.log (902776394751 / 1000000000000)) := by
  have h := reflection_log_12953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12954_neg : (645091533 / 1000000000) ≤ -Real.log (10000000000 / 19061614983) ∧
    -Real.log (10000000000 / 19061614983) ≤ (322545767 / 500000000) := by
  have h := checkLog_sound (w := (9061614983 / 29061614983)) (n := 12)
    (lo := (645091533 / 1000000000)) (hi := (322545767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19061614983 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19061614983 / 10000000000) = 1/(10000000000 / 19061614983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12954 : Bounds (645091533 / 1000000000) (322545767 / 500000000) (Real.log (19061614983 / 10000000000)) := by
  have h := reflection_log_12954_neg
  have he : Real.log (19061614983 / 10000000000) = -Real.log (10000000000 / 19061614983) := by
    rw [show ((19061614983 / 10000000000) : ℝ) = ((10000000000 / 19061614983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12955_neg : (650366287 / 1000000000) ≤ -Real.log (100000000000 / 191624259639) ∧
    -Real.log (100000000000 / 191624259639) ≤ (40647893 / 62500000) := by
  have h := checkLog_sound (w := (91624259639 / 291624259639)) (n := 12)
    (lo := (650366287 / 1000000000)) (hi := (40647893 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191624259639 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191624259639 / 100000000000) = 1/(100000000000 / 191624259639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12955 : Bounds (650366287 / 1000000000) (40647893 / 62500000) (Real.log (191624259639 / 100000000000)) := by
  have h := reflection_log_12955_neg
  have he : Real.log (191624259639 / 100000000000) = -Real.log (100000000000 / 191624259639) := by
    rw [show ((191624259639 / 100000000000) : ℝ) = ((100000000000 / 191624259639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12956_neg : (1337023311 / 1000000000) ≤ -Real.log (250000000000 / 951923076923) ∧
    -Real.log (250000000000 / 951923076923) ≤ (1337023313 / 1000000000) := by
  have h := checkLog_sound (w := (451923076923 / 1451923076923)) (n := 12)
    (lo := (643876131 / 1000000000)) (hi := (160969033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951923076923 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(951923076923 / 500000000000) = 1/(250000000000 / 951923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12956 : Bounds (1337023311 / 1000000000) (1337023313 / 1000000000) (Real.log (951923076923 / 250000000000)) := by
  have h := reflection_log_12956_neg
  have he : Real.log (951923076923 / 250000000000) = -Real.log (250000000000 / 951923076923) := by
    rw [show ((951923076923 / 250000000000) : ℝ) = ((250000000000 / 951923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12957_neg : (1346153127 / 1000000000) ≤ -Real.log (250000000000 / 960653753027) ∧
    -Real.log (250000000000 / 960653753027) ≤ (1346153129 / 1000000000) := by
  have h := checkLog_sound (w := (460653753027 / 1460653753027)) (n := 12)
    (lo := (653005947 / 1000000000)) (hi := (163251487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960653753027 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(960653753027 / 500000000000) = 1/(250000000000 / 960653753027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12957 : Bounds (1346153127 / 1000000000) (1346153129 / 1000000000) (Real.log (960653753027 / 250000000000)) := by
  have h := reflection_log_12957_neg
  have he : Real.log (960653753027 / 250000000000) = -Real.log (250000000000 / 960653753027) := by
    rw [show ((960653753027 / 250000000000) : ℝ) = ((250000000000 / 960653753027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12958_neg : (1811461 / 3906250) ≤ -Real.log (100 / 159) ∧
    -Real.log (100 / 159) ≤ (463734017 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 259)) (n := 12)
    (lo := (1811461 / 3906250)) (hi := (463734017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 100) = 1/(100 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12958 : Bounds (1811461 / 3906250) (463734017 / 1000000000) (Real.log (159 / 100)) := by
  have h := reflection_log_12958_neg
  have he : Real.log (159 / 100) = -Real.log (100 / 159) := by
    rw [show ((159 / 100) : ℝ) = ((100 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12959_neg : (445799059 / 500000000) ≤ -Real.log (41 / 100) ∧
    -Real.log (41 / 100) ≤ (22289953 / 25000000) := by
  have h := checkLog_sound (w := (9 / 91)) (n := 12)
    (lo := (99225469 / 500000000)) (hi := (198450939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 41) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50 / 41) = 1/(41 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12959 : Bounds (-22289953 / 25000000) (-445799059 / 500000000) (Real.log (41 / 100)) := by
  have h := reflection_log_12959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12960_neg : (294913 / 500000000) ≤ -Real.log (100000 / 100059) ∧
    -Real.log (100000 / 100059) ≤ (589827 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 200059)) (n := 12)
    (lo := (294913 / 500000000)) (hi := (589827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100059 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100059 / 100000) = 1/(100000 / 100059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12960 : Bounds (294913 / 500000000) (589827 / 1000000000) (Real.log (100059 / 100000)) := by
  have h := reflection_log_12960_neg
  have he : Real.log (100059 / 100000) = -Real.log (100000 / 100059) := by
    rw [show ((100059 / 100000) : ℝ) = ((100000 / 100059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12961_neg : (295087 / 500000000) ≤ -Real.log (99941 / 100000) ∧
    -Real.log (99941 / 100000) ≤ (23607 / 40000000) := by
  have h := checkLog_sound (w := (59 / 199941)) (n := 12)
    (lo := (295087 / 500000000)) (hi := (23607 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99941) = 1/(99941 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12961 : Bounds (-23607 / 40000000) (-295087 / 500000000) (Real.log (99941 / 100000)) := by
  have h := reflection_log_12961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12962_neg : (272804193 / 1000000000) ≤ -Real.log (1000000 / 1313643) ∧
    -Real.log (1000000 / 1313643) ≤ (136402097 / 500000000) := by
  have h := checkLog_sound (w := (313643 / 2313643)) (n := 12)
    (lo := (272804193 / 1000000000)) (hi := (136402097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313643 / 1000000) = 1/(1000000 / 1313643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12962 : Bounds (272804193 / 1000000000) (136402097 / 500000000) (Real.log (1313643 / 1000000)) := by
  have h := reflection_log_12962_neg
  have he : Real.log (1313643 / 1000000) = -Real.log (1000000 / 1313643) := by
    rw [show ((1313643 / 1000000) : ℝ) = ((1000000 / 1313643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12963_neg : (188178689 / 500000000) ≤ -Real.log (686357 / 1000000) ∧
    -Real.log (686357 / 1000000) ≤ (376357379 / 1000000000) := by
  have h := checkLog_sound (w := (313643 / 1686357)) (n := 12)
    (lo := (188178689 / 500000000)) (hi := (376357379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686357) = 1/(686357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12963 : Bounds (-376357379 / 1000000000) (-188178689 / 500000000) (Real.log (686357 / 1000000)) := by
  have h := reflection_log_12963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12964_neg : (274618869 / 1000000000) ≤ -Real.log (1000000 / 1316029) ∧
    -Real.log (1000000 / 1316029) ≤ (27461887 / 100000000) := by
  have h := checkLog_sound (w := (316029 / 2316029)) (n := 12)
    (lo := (274618869 / 1000000000)) (hi := (27461887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1316029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1316029 / 1000000) = 1/(1000000 / 1316029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12964 : Bounds (274618869 / 1000000000) (27461887 / 100000000) (Real.log (1316029 / 1000000)) := by
  have h := reflection_log_12964_neg
  have he : Real.log (1316029 / 1000000) = -Real.log (1000000 / 1316029) := by
    rw [show ((1316029 / 1000000) : ℝ) = ((1000000 / 1316029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12965_neg : (379839759 / 1000000000) ≤ -Real.log (683971 / 1000000) ∧
    -Real.log (683971 / 1000000) ≤ (4747997 / 12500000) := by
  have h := checkLog_sound (w := (316029 / 1683971)) (n := 12)
    (lo := (379839759 / 1000000000)) (hi := (4747997 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 683971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 683971) = 1/(683971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12965 : Bounds (-4747997 / 12500000) (-379839759 / 1000000000) (Real.log (683971 / 1000000)) := by
  have h := reflection_log_12965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12966_neg : (10522089 / 100000000) ≤ -Real.log (900125671159 / 1000000000000) ∧
    -Real.log (900125671159 / 1000000000000) ≤ (105220891 / 1000000000) := by
  have h := checkLog_sound (w := (99874328841 / 1900125671159)) (n := 12)
    (lo := (10522089 / 100000000)) (hi := (105220891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 900125671159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 900125671159) = 1/(900125671159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12966 : Bounds (-105220891 / 1000000000) (-10522089 / 100000000) (Real.log (900125671159 / 1000000000000)) := by
  have h := reflection_log_12966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12967_neg : (3236037 / 31250000) ≤ -Real.log (901628068551 / 1000000000000) ∧
    -Real.log (901628068551 / 1000000000000) ≤ (20710637 / 200000000) := by
  have h := checkLog_sound (w := (98371931449 / 1901628068551)) (n := 12)
    (lo := (3236037 / 31250000)) (hi := (20710637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 901628068551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 901628068551) = 1/(901628068551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12967 : Bounds (-20710637 / 200000000) (-3236037 / 31250000) (Real.log (901628068551 / 1000000000000)) := by
  have h := reflection_log_12967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12968_neg : (162290393 / 250000000) ≤ -Real.log (500000000000 / 956967729621) ∧
    -Real.log (500000000000 / 956967729621) ≤ (649161573 / 1000000000) := by
  have h := checkLog_sound (w := (456967729621 / 1456967729621)) (n := 12)
    (lo := (162290393 / 250000000)) (hi := (649161573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956967729621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956967729621 / 500000000000) = 1/(500000000000 / 956967729621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12968 : Bounds (162290393 / 250000000) (649161573 / 1000000000) (Real.log (956967729621 / 500000000000)) := by
  have h := reflection_log_12968_neg
  have he : Real.log (956967729621 / 500000000000) = -Real.log (500000000000 / 956967729621) := by
    rw [show ((956967729621 / 500000000000) : ℝ) = ((500000000000 / 956967729621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12969_neg : (654458629 / 1000000000) ≤ -Real.log (250000000000 / 481025145803) ∧
    -Real.log (250000000000 / 481025145803) ≤ (65445863 / 100000000) := by
  have h := checkLog_sound (w := (231025145803 / 731025145803)) (n := 12)
    (lo := (654458629 / 1000000000)) (hi := (65445863 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481025145803 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481025145803 / 250000000000) = 1/(250000000000 / 481025145803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12969 : Bounds (654458629 / 1000000000) (65445863 / 100000000) (Real.log (481025145803 / 250000000000)) := by
  have h := reflection_log_12969_neg
  have he : Real.log (481025145803 / 250000000000) = -Real.log (250000000000 / 481025145803) := by
    rw [show ((481025145803 / 250000000000) : ℝ) = ((250000000000 / 481025145803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12970_neg : (1346153127 / 1000000000) ≤ -Real.log (500000000000 / 1921307506053) ∧
    -Real.log (500000000000 / 1921307506053) ≤ (1346153129 / 1000000000) := by
  have h := checkLog_sound (w := (921307506053 / 2921307506053)) (n := 12)
    (lo := (653005947 / 1000000000)) (hi := (163251487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921307506053 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1921307506053 / 1000000000000) = 1/(500000000000 / 1921307506053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12970 : Bounds (1346153127 / 1000000000) (1346153129 / 1000000000) (Real.log (1921307506053 / 500000000000)) := by
  have h := reflection_log_12970_neg
  have he : Real.log (1921307506053 / 500000000000) = -Real.log (500000000000 / 1921307506053) := by
    rw [show ((1921307506053 / 500000000000) : ℝ) = ((500000000000 / 1921307506053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12971_neg : (677666067 / 500000000) ≤ -Real.log (125000000000 / 484756097561) ∧
    -Real.log (125000000000 / 484756097561) ≤ (169416517 / 125000000) := by
  have h := checkLog_sound (w := (234756097561 / 734756097561)) (n := 12)
    (lo := (331092477 / 500000000)) (hi := (132436991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484756097561 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(484756097561 / 250000000000) = 1/(125000000000 / 484756097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12971 : Bounds (677666067 / 500000000) (169416517 / 125000000) (Real.log (484756097561 / 125000000000)) := by
  have h := reflection_log_12971_neg
  have he : Real.log (484756097561 / 125000000000) = -Real.log (125000000000 / 484756097561) := by
    rw [show ((484756097561 / 125000000000) : ℝ) = ((125000000000 / 484756097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12972_neg : (46561903 / 100000000) ≤ -Real.log (1000 / 1593) ∧
    -Real.log (1000 / 1593) ≤ (465619031 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 2593)) (n := 12)
    (lo := (46561903 / 100000000)) (hi := (465619031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593 / 1000) = 1/(1000 / 1593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12972 : Bounds (46561903 / 100000000) (465619031 / 1000000000) (Real.log (1593 / 1000)) := by
  have h := reflection_log_12972_neg
  have he : Real.log (1593 / 1000) = -Real.log (1000 / 1593) := by
    rw [show ((1593 / 1000) : ℝ) = ((1000 / 1593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12973_neg : (224735523 / 250000000) ≤ -Real.log (407 / 1000) ∧
    -Real.log (407 / 1000) ≤ (449471047 / 500000000) := by
  have h := checkLog_sound (w := (93 / 907)) (n := 12)
    (lo := (6431091 / 31250000)) (hi := (205794913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 407) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 407) = 1/(407 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12973 : Bounds (-449471047 / 500000000) (-224735523 / 250000000) (Real.log (407 / 1000)) := by
  have h := reflection_log_12973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12974_neg : (74103 / 125000000) ≤ -Real.log (1000000 / 1000593) ∧
    -Real.log (1000000 / 1000593) ≤ (23713 / 40000000) := by
  have h := checkLog_sound (w := (593 / 2000593)) (n := 12)
    (lo := (74103 / 125000000)) (hi := (23713 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000593 / 1000000) = 1/(1000000 / 1000593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12974 : Bounds (74103 / 125000000) (23713 / 40000000) (Real.log (1000593 / 1000000)) := by
  have h := reflection_log_12974_neg
  have he : Real.log (1000593 / 1000000) = -Real.log (1000000 / 1000593) := by
    rw [show ((1000593 / 1000000) : ℝ) = ((1000000 / 1000593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12975_neg : (23727 / 40000000) ≤ -Real.log (999407 / 1000000) ∧
    -Real.log (999407 / 1000000) ≤ (74147 / 125000000) := by
  have h := checkLog_sound (w := (593 / 1999407)) (n := 12)
    (lo := (23727 / 40000000)) (hi := (74147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999407) = 1/(999407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12975 : Bounds (-74147 / 125000000) (-23727 / 40000000) (Real.log (999407 / 1000000)) := by
  have h := reflection_log_12975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12976_neg : (137102329 / 500000000) ≤ -Real.log (250000 / 328871) ∧
    -Real.log (250000 / 328871) ≤ (274204659 / 1000000000) := by
  have h := checkLog_sound (w := (78871 / 578871)) (n := 12)
    (lo := (137102329 / 500000000)) (hi := (274204659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328871 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328871 / 250000) = 1/(250000 / 328871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12976 : Bounds (137102329 / 500000000) (274204659 / 1000000000) (Real.log (328871 / 250000)) := by
  have h := reflection_log_12976_neg
  have he : Real.log (328871 / 250000) = -Real.log (250000 / 328871) := by
    rw [show ((328871 / 250000) : ℝ) = ((250000 / 328871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12977_neg : (379043259 / 1000000000) ≤ -Real.log (171129 / 250000) ∧
    -Real.log (171129 / 250000) ≤ (18952163 / 50000000) := by
  have h := checkLog_sound (w := (78871 / 421129)) (n := 12)
    (lo := (379043259 / 1000000000)) (hi := (18952163 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171129) = 1/(171129 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12977 : Bounds (-18952163 / 50000000) (-379043259 / 1000000000) (Real.log (171129 / 250000)) := by
  have h := reflection_log_12977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12978_neg : (276021349 / 1000000000) ≤ -Real.log (250000 / 329469) ∧
    -Real.log (250000 / 329469) ≤ (5520427 / 20000000) := by
  have h := checkLog_sound (w := (79469 / 579469)) (n := 12)
    (lo := (276021349 / 1000000000)) (hi := (5520427 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329469 / 250000) = 1/(250000 / 329469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12978 : Bounds (276021349 / 1000000000) (5520427 / 20000000) (Real.log (329469 / 250000)) := by
  have h := reflection_log_12978_neg
  have he : Real.log (329469 / 250000) = -Real.log (250000 / 329469) := by
    rw [show ((329469 / 250000) : ℝ) = ((250000 / 329469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12979_neg : (382543819 / 1000000000) ≤ -Real.log (170531 / 250000) ∧
    -Real.log (170531 / 250000) ≤ (19127191 / 50000000) := by
  have h := checkLog_sound (w := (79469 / 420531)) (n := 12)
    (lo := (382543819 / 1000000000)) (hi := (19127191 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 170531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 170531) = 1/(170531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12979 : Bounds (-19127191 / 50000000) (-382543819 / 1000000000) (Real.log (170531 / 250000)) := by
  have h := reflection_log_12979_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12980_neg : (106522469 / 1000000000) ≤ -Real.log (56184678039 / 62500000000) ∧
    -Real.log (56184678039 / 62500000000) ≤ (10652247 / 100000000) := by
  have h := checkLog_sound (w := (6315321961 / 118684678039)) (n := 12)
    (lo := (106522469 / 1000000000)) (hi := (10652247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56184678039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56184678039) = 1/(56184678039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12980 : Bounds (-10652247 / 100000000) (-106522469 / 1000000000) (Real.log (56184678039 / 62500000000)) := by
  have h := reflection_log_12980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12981_neg : (104838601 / 1000000000) ≤ -Real.log (56279365359 / 62500000000) ∧
    -Real.log (56279365359 / 62500000000) ≤ (52419301 / 500000000) := by
  have h := checkLog_sound (w := (6220634641 / 118779365359)) (n := 12)
    (lo := (104838601 / 1000000000)) (hi := (52419301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56279365359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56279365359) = 1/(56279365359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12981 : Bounds (-52419301 / 500000000) (-104838601 / 1000000000) (Real.log (56279365359 / 62500000000)) := by
  have h := reflection_log_12981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12982_neg : (326623959 / 500000000) ≤ -Real.log (500000000000 / 960886232023) ∧
    -Real.log (500000000000 / 960886232023) ≤ (653247919 / 1000000000) := by
  have h := checkLog_sound (w := (460886232023 / 1460886232023)) (n := 12)
    (lo := (326623959 / 500000000)) (hi := (653247919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960886232023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960886232023 / 500000000000) = 1/(500000000000 / 960886232023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12982 : Bounds (326623959 / 500000000) (653247919 / 1000000000) (Real.log (960886232023 / 500000000000)) := by
  have h := reflection_log_12982_neg
  have he : Real.log (960886232023 / 500000000000) = -Real.log (500000000000 / 960886232023) := by
    rw [show ((960886232023 / 500000000000) : ℝ) = ((500000000000 / 960886232023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12983_neg : (658565169 / 1000000000) ≤ -Real.log (500000000000 / 966009112713) ∧
    -Real.log (500000000000 / 966009112713) ≤ (65856517 / 100000000) := by
  have h := checkLog_sound (w := (466009112713 / 1466009112713)) (n := 12)
    (lo := (658565169 / 1000000000)) (hi := (65856517 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((966009112713 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(966009112713 / 500000000000) = 1/(500000000000 / 966009112713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12983 : Bounds (658565169 / 1000000000) (65856517 / 100000000) (Real.log (966009112713 / 500000000000)) := by
  have h := reflection_log_12983_neg
  have he : Real.log (966009112713 / 500000000000) = -Real.log (500000000000 / 966009112713) := by
    rw [show ((966009112713 / 500000000000) : ℝ) = ((500000000000 / 966009112713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12984_neg : (677666067 / 500000000) ≤ -Real.log (500000000000 / 1939024390243) ∧
    -Real.log (500000000000 / 1939024390243) ≤ (169416517 / 125000000) := by
  have h := checkLog_sound (w := (939024390243 / 2939024390243)) (n := 12)
    (lo := (331092477 / 500000000)) (hi := (132436991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939024390243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1939024390243 / 1000000000000) = 1/(500000000000 / 1939024390243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12984 : Bounds (677666067 / 500000000) (169416517 / 125000000) (Real.log (1939024390243 / 500000000000)) := by
  have h := reflection_log_12984_neg
  have he : Real.log (1939024390243 / 500000000000) = -Real.log (500000000000 / 1939024390243) := by
    rw [show ((1939024390243 / 500000000000) : ℝ) = ((500000000000 / 1939024390243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12985_neg : (1364561123 / 1000000000) ≤ -Real.log (500000000000 / 1957002457003) ∧
    -Real.log (500000000000 / 1957002457003) ≤ (10916489 / 8000000) := by
  have h := checkLog_sound (w := (957002457003 / 2957002457003)) (n := 12)
    (lo := (671413943 / 1000000000)) (hi := (83926743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957002457003 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1957002457003 / 1000000000000) = 1/(500000000000 / 1957002457003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12985 : Bounds (1364561123 / 1000000000) (10916489 / 8000000) (Real.log (1957002457003 / 500000000000)) := by
  have h := reflection_log_12985_neg
  have he : Real.log (1957002457003 / 500000000000) = -Real.log (500000000000 / 1957002457003) := by
    rw [show ((1957002457003 / 500000000000) : ℝ) = ((500000000000 / 1957002457003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12986_neg : (467500499 / 1000000000) ≤ -Real.log (250 / 399) ∧
    -Real.log (250 / 399) ≤ (935001 / 2000000) := by
  have h := checkLog_sound (w := (149 / 649)) (n := 12)
    (lo := (467500499 / 1000000000)) (hi := (935001 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 250) = 1/(250 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12986 : Bounds (467500499 / 1000000000) (935001 / 2000000) (Real.log (399 / 250)) := by
  have h := reflection_log_12986_neg
  have he : Real.log (399 / 250) = -Real.log (250 / 399) := by
    rw [show ((399 / 250) : ℝ) = ((250 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12987_neg : (2265851 / 2500000) ≤ -Real.log (101 / 250) ∧
    -Real.log (101 / 250) ≤ (453170201 / 500000000) := by
  have h := checkLog_sound (w := (12 / 113)) (n := 12)
    (lo := (10659661 / 50000000)) (hi := (213193221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 101) = 1/(101 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12987 : Bounds (-453170201 / 500000000) (-2265851 / 2500000) (Real.log (101 / 250)) := by
  have h := reflection_log_12987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12988_neg : (297911 / 500000000) ≤ -Real.log (250000 / 250149) ∧
    -Real.log (250000 / 250149) ≤ (595823 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 500149)) (n := 12)
    (lo := (297911 / 500000000)) (hi := (595823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250149 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250149 / 250000) = 1/(250000 / 250149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12988 : Bounds (297911 / 500000000) (595823 / 1000000000) (Real.log (250149 / 250000)) := by
  have h := reflection_log_12988_neg
  have he : Real.log (250149 / 250000) = -Real.log (250000 / 250149) := by
    rw [show ((250149 / 250000) : ℝ) = ((250000 / 250149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12989_neg : (596177 / 1000000000) ≤ -Real.log (249851 / 250000) ∧
    -Real.log (249851 / 250000) ≤ (298089 / 500000000) := by
  have h := checkLog_sound (w := (149 / 499851)) (n := 12)
    (lo := (596177 / 1000000000)) (hi := (298089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249851) = 1/(249851 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12989 : Bounds (-298089 / 500000000) (-596177 / 1000000000) (Real.log (249851 / 250000)) := by
  have h := reflection_log_12989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12990_neg : (275606201 / 1000000000) ≤ -Real.log (1000000 / 1317329) ∧
    -Real.log (1000000 / 1317329) ≤ (137803101 / 500000000) := by
  have h := checkLog_sound (w := (317329 / 2317329)) (n := 12)
    (lo := (275606201 / 1000000000)) (hi := (137803101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317329 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317329 / 1000000) = 1/(1000000 / 1317329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12990 : Bounds (275606201 / 1000000000) (137803101 / 500000000) (Real.log (1317329 / 1000000)) := by
  have h := reflection_log_12990_neg
  have he : Real.log (1317329 / 1000000) = -Real.log (1000000 / 1317329) := by
    rw [show ((1317329 / 1000000) : ℝ) = ((1000000 / 1317329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12991_neg : (381742233 / 1000000000) ≤ -Real.log (682671 / 1000000) ∧
    -Real.log (682671 / 1000000) ≤ (190871117 / 500000000) := by
  have h := checkLog_sound (w := (317329 / 1682671)) (n := 12)
    (lo := (381742233 / 1000000000)) (hi := (190871117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682671) = 1/(682671 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12991 : Bounds (-190871117 / 500000000) (-381742233 / 1000000000) (Real.log (682671 / 1000000)) := by
  have h := reflection_log_12991_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0203 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12992_neg : (138712827 / 500000000) ≤ -Real.log (62500 / 82483) ∧
    -Real.log (62500 / 82483) ≤ (55485131 / 200000000) := by
  have h := checkLog_sound (w := (19983 / 144983)) (n := 12)
    (lo := (138712827 / 500000000)) (hi := (55485131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82483 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82483 / 62500) = 1/(62500 / 82483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12992 : Bounds (138712827 / 500000000) (55485131 / 200000000) (Real.log (82483 / 62500)) := by
  have h := reflection_log_12992_neg
  have he : Real.log (82483 / 62500) = -Real.log (62500 / 82483) := by
    rw [show ((82483 / 62500) : ℝ) = ((62500 / 82483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12993_neg : (2407891 / 6250000) ≤ -Real.log (42517 / 62500) ∧
    -Real.log (42517 / 62500) ≤ (385262561 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 105017)) (n := 12)
    (lo := (2407891 / 6250000)) (hi := (385262561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42517) = 1/(42517 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12993 : Bounds (-385262561 / 1000000000) (-2407891 / 6250000) (Real.log (42517 / 62500)) := by
  have h := reflection_log_12993_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12994_neg : (53918453 / 500000000) ≤ -Real.log (3506929711 / 3906250000) ∧
    -Real.log (3506929711 / 3906250000) ≤ (107836907 / 1000000000) := by
  have h := checkLog_sound (w := (399320289 / 7413179711)) (n := 12)
    (lo := (53918453 / 500000000)) (hi := (107836907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3506929711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3506929711) = 1/(3506929711 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12994 : Bounds (-107836907 / 1000000000) (-53918453 / 500000000) (Real.log (3506929711 / 3906250000)) := by
  have h := reflection_log_12994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12995_neg : (3316751 / 31250000) ≤ -Real.log (899302305759 / 1000000000000) ∧
    -Real.log (899302305759 / 1000000000000) ≤ (106136033 / 1000000000) := by
  have h := checkLog_sound (w := (100697694241 / 1899302305759)) (n := 12)
    (lo := (3316751 / 31250000)) (hi := (106136033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 899302305759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 899302305759) = 1/(899302305759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12995 : Bounds (-106136033 / 1000000000) (-3316751 / 31250000) (Real.log (899302305759 / 1000000000000)) := by
  have h := reflection_log_12995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12996_neg : (131469687 / 200000000) ≤ -Real.log (250000000000 / 482417225867) ∧
    -Real.log (250000000000 / 482417225867) ≤ (164337109 / 250000000) := by
  have h := checkLog_sound (w := (232417225867 / 732417225867)) (n := 12)
    (lo := (131469687 / 200000000)) (hi := (164337109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482417225867 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482417225867 / 250000000000) = 1/(250000000000 / 482417225867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12996 : Bounds (131469687 / 200000000) (164337109 / 250000000) (Real.log (482417225867 / 250000000000)) := by
  have h := reflection_log_12996_neg
  have he : Real.log (482417225867 / 250000000000) = -Real.log (250000000000 / 482417225867) := by
    rw [show ((482417225867 / 250000000000) : ℝ) = ((250000000000 / 482417225867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12997_neg : (132537643 / 200000000) ≤ -Real.log (500000000000 / 970000235201) ∧
    -Real.log (500000000000 / 970000235201) ≤ (82836027 / 125000000) := by
  have h := checkLog_sound (w := (470000235201 / 1470000235201)) (n := 12)
    (lo := (132537643 / 200000000)) (hi := (82836027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970000235201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970000235201 / 500000000000) = 1/(500000000000 / 970000235201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12997 : Bounds (132537643 / 200000000) (82836027 / 125000000) (Real.log (970000235201 / 500000000000)) := by
  have h := reflection_log_12997_neg
  have he : Real.log (970000235201 / 500000000000) = -Real.log (500000000000 / 970000235201) := by
    rw [show ((970000235201 / 500000000000) : ℝ) = ((500000000000 / 970000235201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12998_neg : (1364561123 / 1000000000) ≤ -Real.log (250000000000 / 978501228501) ∧
    -Real.log (250000000000 / 978501228501) ≤ (10916489 / 8000000) := by
  have h := checkLog_sound (w := (478501228501 / 1478501228501)) (n := 12)
    (lo := (671413943 / 1000000000)) (hi := (83926743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978501228501 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(978501228501 / 500000000000) = 1/(250000000000 / 978501228501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12998 : Bounds (1364561123 / 1000000000) (10916489 / 8000000) (Real.log (978501228501 / 250000000000)) := by
  have h := reflection_log_12998_neg
  have he : Real.log (978501228501 / 250000000000) = -Real.log (250000000000 / 978501228501) := by
    rw [show ((978501228501 / 250000000000) : ℝ) = ((250000000000 / 978501228501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12999_neg : (1373840899 / 1000000000) ≤ -Real.log (500000000000 / 1975247524753) ∧
    -Real.log (500000000000 / 1975247524753) ≤ (1373840901 / 1000000000) := by
  have h := checkLog_sound (w := (975247524753 / 2975247524753)) (n := 12)
    (lo := (680693719 / 1000000000)) (hi := (17017343 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975247524753 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1975247524753 / 1000000000000) = 1/(500000000000 / 1975247524753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12999 : Bounds (1373840899 / 1000000000) (1373840901 / 1000000000) (Real.log (1975247524753 / 500000000000)) := by
  have h := reflection_log_12999_neg
  have he : Real.log (1975247524753 / 500000000000) = -Real.log (500000000000 / 1975247524753) := by
    rw [show ((1975247524753 / 500000000000) : ℝ) = ((500000000000 / 1975247524753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13000_neg : (469378433 / 1000000000) ≤ -Real.log (1000 / 1599) ∧
    -Real.log (1000 / 1599) ≤ (234689217 / 500000000) := by
  have h := checkLog_sound (w := (599 / 2599)) (n := 12)
    (lo := (469378433 / 1000000000)) (hi := (234689217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599 / 1000) = 1/(1000 / 1599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13000 : Bounds (469378433 / 1000000000) (234689217 / 500000000) (Real.log (1599 / 1000)) := by
  have h := reflection_log_13000_neg
  have he : Real.log (1599 / 1000) = -Real.log (1000 / 1599) := by
    rw [show ((1599 / 1000) : ℝ) = ((1000 / 1599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13001_neg : (913793851 / 1000000000) ≤ -Real.log (401 / 1000) ∧
    -Real.log (401 / 1000) ≤ (913793853 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 901)) (n := 12)
    (lo := (220646671 / 1000000000)) (hi := (13790417 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 401) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 401) = 1/(401 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13001 : Bounds (-913793853 / 1000000000) (-913793851 / 1000000000) (Real.log (401 / 1000)) := by
  have h := reflection_log_13001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13002_neg : (29941 / 50000000) ≤ -Real.log (1000000 / 1000599) ∧
    -Real.log (1000000 / 1000599) ≤ (598821 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 2000599)) (n := 12)
    (lo := (29941 / 50000000)) (hi := (598821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000599 / 1000000) = 1/(1000000 / 1000599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13002 : Bounds (29941 / 50000000) (598821 / 1000000000) (Real.log (1000599 / 1000000)) := by
  have h := reflection_log_13002_neg
  have he : Real.log (1000599 / 1000000) = -Real.log (1000000 / 1000599) := by
    rw [show ((1000599 / 1000000) : ℝ) = ((1000000 / 1000599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13003_neg : (599179 / 1000000000) ≤ -Real.log (999401 / 1000000) ∧
    -Real.log (999401 / 1000000) ≤ (29959 / 50000000) := by
  have h := checkLog_sound (w := (599 / 1999401)) (n := 12)
    (lo := (599179 / 1000000000)) (hi := (29959 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999401) = 1/(999401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13003 : Bounds (-29959 / 50000000) (-599179 / 1000000000) (Real.log (999401 / 1000000)) := by
  have h := reflection_log_13003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13004_neg : (277009573 / 1000000000) ≤ -Real.log (1000000 / 1319179) ∧
    -Real.log (1000000 / 1319179) ≤ (138504787 / 500000000) := by
  have h := checkLog_sound (w := (319179 / 2319179)) (n := 12)
    (lo := (277009573 / 1000000000)) (hi := (138504787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319179 / 1000000) = 1/(1000000 / 1319179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13004 : Bounds (277009573 / 1000000000) (138504787 / 500000000) (Real.log (1319179 / 1000000)) := by
  have h := reflection_log_13004_neg
  have he : Real.log (1319179 / 1000000) = -Real.log (1000000 / 1319179) := by
    rw [show ((1319179 / 1000000) : ℝ) = ((1000000 / 1319179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13005_neg : (24028491 / 62500000) ≤ -Real.log (680821 / 1000000) ∧
    -Real.log (680821 / 1000000) ≤ (384455857 / 1000000000) := by
  have h := checkLog_sound (w := (319179 / 1680821)) (n := 12)
    (lo := (24028491 / 62500000)) (hi := (384455857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680821) = 1/(680821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13005 : Bounds (-384455857 / 1000000000) (-24028491 / 62500000) (Real.log (680821 / 1000000)) := by
  have h := reflection_log_13005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13006_neg : (278831017 / 1000000000) ≤ -Real.log (62500 / 82599) ∧
    -Real.log (62500 / 82599) ≤ (139415509 / 500000000) := by
  have h := checkLog_sound (w := (20099 / 145099)) (n := 12)
    (lo := (278831017 / 1000000000)) (hi := (139415509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82599 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82599 / 62500) = 1/(62500 / 82599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13006 : Bounds (278831017 / 1000000000) (139415509 / 500000000) (Real.log (82599 / 62500)) := by
  have h := reflection_log_13006_neg
  have he : Real.log (82599 / 62500) = -Real.log (62500 / 82599) := by
    rw [show ((82599 / 62500) : ℝ) = ((62500 / 82599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13007_neg : (387994609 / 1000000000) ≤ -Real.log (42401 / 62500) ∧
    -Real.log (42401 / 62500) ≤ (38799461 / 100000000) := by
  have h := checkLog_sound (w := (20099 / 104901)) (n := 12)
    (lo := (387994609 / 1000000000)) (hi := (38799461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42401) = 1/(42401 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13007 : Bounds (-38799461 / 100000000) (-387994609 / 1000000000) (Real.log (42401 / 62500)) := by
  have h := reflection_log_13007_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13008_neg : (13645449 / 125000000) ≤ -Real.log (3502280199 / 3906250000) ∧
    -Real.log (3502280199 / 3906250000) ≤ (109163593 / 1000000000) := by
  have h := checkLog_sound (w := (403969801 / 7408530199)) (n := 12)
    (lo := (13645449 / 125000000)) (hi := (109163593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3502280199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3502280199) = 1/(3502280199 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13008 : Bounds (-109163593 / 1000000000) (-13645449 / 125000000) (Real.log (3502280199 / 3906250000)) := by
  have h := reflection_log_13008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13009_neg : (53723141 / 500000000) ≤ -Real.log (898124765959 / 1000000000000) ∧
    -Real.log (898124765959 / 1000000000000) ≤ (107446283 / 1000000000) := by
  have h := checkLog_sound (w := (101875234041 / 1898124765959)) (n := 12)
    (lo := (53723141 / 500000000)) (hi := (107446283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 898124765959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 898124765959) = 1/(898124765959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13009 : Bounds (-107446283 / 1000000000) (-53723141 / 500000000) (Real.log (898124765959 / 1000000000000)) := by
  have h := reflection_log_13009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13010_neg : (661465429 / 1000000000) ≤ -Real.log (125000000000 / 242203714339) ∧
    -Real.log (125000000000 / 242203714339) ≤ (66146543 / 100000000) := by
  have h := checkLog_sound (w := (117203714339 / 367203714339)) (n := 12)
    (lo := (661465429 / 1000000000)) (hi := (66146543 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242203714339 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242203714339 / 125000000000) = 1/(125000000000 / 242203714339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13010 : Bounds (661465429 / 1000000000) (66146543 / 100000000) (Real.log (242203714339 / 125000000000)) := by
  have h := reflection_log_13010_neg
  have he : Real.log (242203714339 / 125000000000) = -Real.log (125000000000 / 242203714339) := by
    rw [show ((242203714339 / 125000000000) : ℝ) = ((125000000000 / 242203714339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13011_neg : (666825627 / 1000000000) ≤ -Real.log (125000000000 / 243505459777) ∧
    -Real.log (125000000000 / 243505459777) ≤ (166706407 / 250000000) := by
  have h := checkLog_sound (w := (118505459777 / 368505459777)) (n := 12)
    (lo := (666825627 / 1000000000)) (hi := (166706407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243505459777 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243505459777 / 125000000000) = 1/(125000000000 / 243505459777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13011 : Bounds (666825627 / 1000000000) (166706407 / 250000000) (Real.log (243505459777 / 125000000000)) := by
  have h := reflection_log_13011_neg
  have he : Real.log (243505459777 / 125000000000) = -Real.log (125000000000 / 243505459777) := by
    rw [show ((243505459777 / 125000000000) : ℝ) = ((125000000000 / 243505459777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13012_neg : (1373840899 / 1000000000) ≤ -Real.log (31250000000 / 123452970297) ∧
    -Real.log (31250000000 / 123452970297) ≤ (1373840901 / 1000000000) := by
  have h := checkLog_sound (w := (60952970297 / 185952970297)) (n := 12)
    (lo := (680693719 / 1000000000)) (hi := (17017343 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123452970297 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(123452970297 / 62500000000) = 1/(31250000000 / 123452970297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13012 : Bounds (1373840899 / 1000000000) (1373840901 / 1000000000) (Real.log (123452970297 / 31250000000)) := by
  have h := reflection_log_13012_neg
  have he : Real.log (123452970297 / 31250000000) = -Real.log (31250000000 / 123452970297) := by
    rw [show ((123452970297 / 31250000000) : ℝ) = ((31250000000 / 123452970297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13013_neg : (345793071 / 250000000) ≤ -Real.log (100000000000 / 398753117207) ∧
    -Real.log (100000000000 / 398753117207) ≤ (691586143 / 500000000) := by
  have h := checkLog_sound (w := (198753117207 / 598753117207)) (n := 12)
    (lo := (43126569 / 62500000)) (hi := (138005021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398753117207 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(398753117207 / 200000000000) = 1/(100000000000 / 398753117207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13013 : Bounds (345793071 / 250000000) (691586143 / 500000000) (Real.log (398753117207 / 100000000000)) := by
  have h := reflection_log_13013_neg
  have he : Real.log (398753117207 / 100000000000) = -Real.log (100000000000 / 398753117207) := by
    rw [show ((398753117207 / 100000000000) : ℝ) = ((100000000000 / 398753117207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13014_neg : (29453303 / 62500000) ≤ -Real.log (500 / 801) ∧
    -Real.log (500 / 801) ≤ (471252849 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 1301)) (n := 12)
    (lo := (29453303 / 62500000)) (hi := (471252849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801 / 500) = 1/(500 / 801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13014 : Bounds (29453303 / 62500000) (471252849 / 1000000000) (Real.log (801 / 500)) := by
  have h := reflection_log_13014_neg
  have he : Real.log (801 / 500) = -Real.log (500 / 801) := by
    rw [show ((801 / 500) : ℝ) = ((500 / 801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13015_neg : (921303273 / 1000000000) ≤ -Real.log (199 / 500) ∧
    -Real.log (199 / 500) ≤ (36852131 / 40000000) := by
  have h := checkLog_sound (w := (51 / 449)) (n := 12)
    (lo := (228156093 / 1000000000)) (hi := (114078047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 199) = 1/(199 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13015 : Bounds (-36852131 / 40000000) (-921303273 / 1000000000) (Real.log (199 / 500)) := by
  have h := reflection_log_13015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13016_neg : (300909 / 500000000) ≤ -Real.log (500000 / 500301) ∧
    -Real.log (500000 / 500301) ≤ (601819 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 1000301)) (n := 12)
    (lo := (300909 / 500000000)) (hi := (601819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500301 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500301 / 500000) = 1/(500000 / 500301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13016 : Bounds (300909 / 500000000) (601819 / 1000000000) (Real.log (500301 / 500000)) := by
  have h := reflection_log_13016_neg
  have he : Real.log (500301 / 500000) = -Real.log (500000 / 500301) := by
    rw [show ((500301 / 500000) : ℝ) = ((500000 / 500301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13017_neg : (602181 / 1000000000) ≤ -Real.log (499699 / 500000) ∧
    -Real.log (499699 / 500000) ≤ (301091 / 500000000) := by
  have h := checkLog_sound (w := (301 / 999699)) (n := 12)
    (lo := (602181 / 1000000000)) (hi := (301091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499699) = 1/(499699 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13017 : Bounds (-301091 / 500000000) (-602181 / 1000000000) (Real.log (499699 / 500000)) := by
  have h := reflection_log_13017_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13018_neg : (278413249 / 1000000000) ≤ -Real.log (125000 / 165129) ∧
    -Real.log (125000 / 165129) ≤ (1113653 / 4000000) := by
  have h := checkLog_sound (w := (40129 / 290129)) (n := 12)
    (lo := (278413249 / 1000000000)) (hi := (1113653 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165129 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165129 / 125000) = 1/(125000 / 165129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13018 : Bounds (278413249 / 1000000000) (1113653 / 4000000) (Real.log (165129 / 125000)) := by
  have h := reflection_log_13018_neg
  have he : Real.log (165129 / 125000) = -Real.log (125000 / 165129) := by
    rw [show ((165129 / 125000) : ℝ) = ((125000 / 165129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13019_neg : (2419883 / 6250000) ≤ -Real.log (84871 / 125000) ∧
    -Real.log (84871 / 125000) ≤ (387181281 / 1000000000) := by
  have h := checkLog_sound (w := (40129 / 209871)) (n := 12)
    (lo := (2419883 / 6250000)) (hi := (387181281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84871) = 1/(84871 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13019 : Bounds (-387181281 / 1000000000) (-2419883 / 6250000) (Real.log (84871 / 125000)) := by
  have h := reflection_log_13019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13020_neg : (280237429 / 1000000000) ≤ -Real.log (250000 / 330861) ∧
    -Real.log (250000 / 330861) ≤ (28023743 / 100000000) := by
  have h := checkLog_sound (w := (80861 / 580861)) (n := 12)
    (lo := (280237429 / 1000000000)) (hi := (28023743 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330861 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330861 / 250000) = 1/(250000 / 330861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13020 : Bounds (280237429 / 1000000000) (28023743 / 100000000) (Real.log (330861 / 250000)) := by
  have h := reflection_log_13020_neg
  have he : Real.log (330861 / 250000) = -Real.log (250000 / 330861) := by
    rw [show ((330861 / 250000) : ℝ) = ((250000 / 330861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13021_neg : (78148011 / 200000000) ≤ -Real.log (169139 / 250000) ∧
    -Real.log (169139 / 250000) ≤ (48842507 / 125000000) := by
  have h := checkLog_sound (w := (80861 / 419139)) (n := 12)
    (lo := (78148011 / 200000000)) (hi := (48842507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 169139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 169139) = 1/(169139 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13021 : Bounds (-48842507 / 125000000) (-78148011 / 200000000) (Real.log (169139 / 250000)) := by
  have h := reflection_log_13021_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13022_neg : (55251313 / 500000000) ≤ -Real.log (55961498679 / 62500000000) ∧
    -Real.log (55961498679 / 62500000000) ≤ (110502627 / 1000000000) := by
  have h := checkLog_sound (w := (6538501321 / 118461498679)) (n := 12)
    (lo := (55251313 / 500000000)) (hi := (110502627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55961498679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55961498679) = 1/(55961498679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13022 : Bounds (-110502627 / 1000000000) (-55251313 / 500000000) (Real.log (55961498679 / 62500000000)) := by
  have h := reflection_log_13022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13023_neg : (108768031 / 1000000000) ≤ -Real.log (14014663359 / 15625000000) ∧
    -Real.log (14014663359 / 15625000000) ≤ (3399001 / 31250000) := by
  have h := checkLog_sound (w := (1610336641 / 29639663359)) (n := 12)
    (lo := (108768031 / 1000000000)) (hi := (3399001 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14014663359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14014663359) = 1/(14014663359 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13023 : Bounds (-3399001 / 31250000) (-108768031 / 1000000000) (Real.log (14014663359 / 15625000000)) := by
  have h := reflection_log_13023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13024_neg : (665594529 / 1000000000) ≤ -Real.log (31250000000 / 60801466343) ∧
    -Real.log (31250000000 / 60801466343) ≤ (66559453 / 100000000) := by
  have h := checkLog_sound (w := (29551466343 / 92051466343)) (n := 12)
    (lo := (665594529 / 1000000000)) (hi := (66559453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60801466343 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60801466343 / 31250000000) = 1/(31250000000 / 60801466343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13024 : Bounds (665594529 / 1000000000) (66559453 / 100000000) (Real.log (60801466343 / 31250000000)) := by
  have h := reflection_log_13024_neg
  have he : Real.log (60801466343 / 31250000000) = -Real.log (31250000000 / 60801466343) := by
    rw [show ((60801466343 / 31250000000) : ℝ) = ((31250000000 / 60801466343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13025_neg : (134195497 / 200000000) ≤ -Real.log (250000000000 / 489037123313) ∧
    -Real.log (250000000000 / 489037123313) ≤ (335488743 / 500000000) := by
  have h := checkLog_sound (w := (239037123313 / 739037123313)) (n := 12)
    (lo := (134195497 / 200000000)) (hi := (335488743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489037123313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489037123313 / 250000000000) = 1/(250000000000 / 489037123313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13025 : Bounds (134195497 / 200000000) (335488743 / 500000000) (Real.log (489037123313 / 250000000000)) := by
  have h := reflection_log_13025_neg
  have he : Real.log (489037123313 / 250000000000) = -Real.log (250000000000 / 489037123313) := by
    rw [show ((489037123313 / 250000000000) : ℝ) = ((250000000000 / 489037123313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13026_neg : (345793071 / 250000000) ≤ -Real.log (250000000000 / 996882793017) ∧
    -Real.log (250000000000 / 996882793017) ≤ (691586143 / 500000000) := by
  have h := checkLog_sound (w := (496882793017 / 1496882793017)) (n := 12)
    (lo := (43126569 / 62500000)) (hi := (138005021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996882793017 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(996882793017 / 500000000000) = 1/(250000000000 / 996882793017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13026 : Bounds (345793071 / 250000000) (691586143 / 500000000) (Real.log (996882793017 / 250000000000)) := by
  have h := reflection_log_13026_neg
  have he : Real.log (996882793017 / 250000000000) = -Real.log (250000000000 / 996882793017) := by
    rw [show ((996882793017 / 250000000000) : ℝ) = ((250000000000 / 996882793017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13027_neg : (1392556121 / 1000000000) ≤ -Real.log (500000000000 / 2012562814071) ∧
    -Real.log (500000000000 / 2012562814071) ≤ (348139031 / 250000000) := by
  have h := checkLog_sound (w := (12562814071 / 4012562814071)) (n := 12)
    (lo := (6261761 / 1000000000)) (hi := (3130881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2012562814071 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2012562814071 / 2000000000000) = 1/(500000000000 / 2012562814071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13027 : Bounds (1392556121 / 1000000000) (348139031 / 250000000) (Real.log (2012562814071 / 500000000000)) := by
  have h := reflection_log_13027_neg
  have he : Real.log (2012562814071 / 500000000000) = -Real.log (500000000000 / 2012562814071) := by
    rw [show ((2012562814071 / 500000000000) : ℝ) = ((500000000000 / 2012562814071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13028_neg : (118280939 / 250000000) ≤ -Real.log (200 / 321) ∧
    -Real.log (200 / 321) ≤ (473123757 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 521)) (n := 12)
    (lo := (118280939 / 250000000)) (hi := (473123757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 200) = 1/(200 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13028 : Bounds (118280939 / 250000000) (473123757 / 1000000000) (Real.log (321 / 200)) := by
  have h := reflection_log_13028_neg
  have he : Real.log (321 / 200) = -Real.log (200 / 321) := by
    rw [show ((321 / 200) : ℝ) = ((200 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13029_neg : (928869513 / 1000000000) ≤ -Real.log (79 / 200) ∧
    -Real.log (79 / 200) ≤ (185773903 / 200000000) := by
  have h := checkLog_sound (w := (21 / 179)) (n := 12)
    (lo := (235722333 / 1000000000)) (hi := (117861167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 79) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 79) = 1/(79 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13029 : Bounds (-185773903 / 200000000) (-928869513 / 1000000000) (Real.log (79 / 200)) := by
  have h := reflection_log_13029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13030_neg : (604817 / 1000000000) ≤ -Real.log (200000 / 200121) ∧
    -Real.log (200000 / 200121) ≤ (302409 / 500000000) := by
  have h := checkLog_sound (w := (121 / 400121)) (n := 12)
    (lo := (604817 / 1000000000)) (hi := (302409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200121 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200121 / 200000) = 1/(200000 / 200121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13030 : Bounds (604817 / 1000000000) (302409 / 500000000) (Real.log (200121 / 200000)) := by
  have h := reflection_log_13030_neg
  have he : Real.log (200121 / 200000) = -Real.log (200000 / 200121) := by
    rw [show ((200121 / 200000) : ℝ) = ((200000 / 200121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13031_neg : (605183 / 1000000000) ≤ -Real.log (199879 / 200000) ∧
    -Real.log (199879 / 200000) ≤ (1182 / 1953125) := by
  have h := checkLog_sound (w := (121 / 399879)) (n := 12)
    (lo := (605183 / 1000000000)) (hi := (1182 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199879) = 1/(199879 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13031 : Bounds (-1182 / 1953125) (-605183 / 1000000000) (Real.log (199879 / 200000)) := by
  have h := reflection_log_13031_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13032_neg : (279819493 / 1000000000) ≤ -Real.log (1000000 / 1322891) ∧
    -Real.log (1000000 / 1322891) ≤ (139909747 / 500000000) := by
  have h := checkLog_sound (w := (322891 / 2322891)) (n := 12)
    (lo := (279819493 / 1000000000)) (hi := (139909747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322891 / 1000000) = 1/(1000000 / 1322891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13032 : Bounds (279819493 / 1000000000) (139909747 / 500000000) (Real.log (1322891 / 1000000)) := by
  have h := reflection_log_13032_neg
  have he : Real.log (1322891 / 1000000) = -Real.log (1000000 / 1322891) := by
    rw [show ((1322891 / 1000000) : ℝ) = ((1000000 / 1322891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13033_neg : (194961507 / 500000000) ≤ -Real.log (677109 / 1000000) ∧
    -Real.log (677109 / 1000000) ≤ (77984603 / 200000000) := by
  have h := checkLog_sound (w := (322891 / 1677109)) (n := 12)
    (lo := (194961507 / 500000000)) (hi := (77984603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677109) = 1/(677109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13033 : Bounds (-77984603 / 200000000) (-194961507 / 500000000) (Real.log (677109 / 1000000)) := by
  have h := reflection_log_13033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13034_neg : (281645639 / 1000000000) ≤ -Real.log (1000000 / 1325309) ∧
    -Real.log (1000000 / 1325309) ≤ (7041141 / 25000000) := by
  have h := checkLog_sound (w := (325309 / 2325309)) (n := 12)
    (lo := (281645639 / 1000000000)) (hi := (7041141 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325309 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325309 / 1000000) = 1/(1000000 / 1325309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13034 : Bounds (281645639 / 1000000000) (7041141 / 25000000) (Real.log (1325309 / 1000000)) := by
  have h := reflection_log_13034_neg
  have he : Real.log (1325309 / 1000000) = -Real.log (1000000 / 1325309) := by
    rw [show ((1325309 / 1000000) : ℝ) = ((1000000 / 1325309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13035_neg : (39350047 / 100000000) ≤ -Real.log (674691 / 1000000) ∧
    -Real.log (674691 / 1000000) ≤ (393500471 / 1000000000) := by
  have h := checkLog_sound (w := (325309 / 1674691)) (n := 12)
    (lo := (39350047 / 100000000)) (hi := (393500471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674691) = 1/(674691 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13035 : Bounds (-393500471 / 1000000000) (-39350047 / 100000000) (Real.log (674691 / 1000000)) := by
  have h := reflection_log_13035_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13036_neg : (11185483 / 100000000) ≤ -Real.log (894174054519 / 1000000000000) ∧
    -Real.log (894174054519 / 1000000000000) ≤ (111854831 / 1000000000) := by
  have h := checkLog_sound (w := (105825945481 / 1894174054519)) (n := 12)
    (lo := (11185483 / 100000000)) (hi := (111854831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 894174054519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 894174054519) = 1/(894174054519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13036 : Bounds (-111854831 / 1000000000) (-11185483 / 100000000) (Real.log (894174054519 / 1000000000000)) := by
  have h := reflection_log_13036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13037_neg : (110103521 / 1000000000) ≤ -Real.log (895741402119 / 1000000000000) ∧
    -Real.log (895741402119 / 1000000000000) ≤ (55051761 / 500000000) := by
  have h := checkLog_sound (w := (104258597881 / 1895741402119)) (n := 12)
    (lo := (110103521 / 1000000000)) (hi := (55051761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 895741402119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 895741402119) = 1/(895741402119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13037 : Bounds (-55051761 / 500000000) (-110103521 / 1000000000) (Real.log (895741402119 / 1000000000000)) := by
  have h := reflection_log_13037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13038_neg : (669742507 / 1000000000) ≤ -Real.log (500000000000 / 976867092299) ∧
    -Real.log (500000000000 / 976867092299) ≤ (167435627 / 250000000) := by
  have h := checkLog_sound (w := (476867092299 / 1476867092299)) (n := 12)
    (lo := (669742507 / 1000000000)) (hi := (167435627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976867092299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976867092299 / 500000000000) = 1/(500000000000 / 976867092299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13038 : Bounds (669742507 / 1000000000) (167435627 / 250000000) (Real.log (976867092299 / 500000000000)) := by
  have h := reflection_log_13038_neg
  have he : Real.log (976867092299 / 500000000000) = -Real.log (500000000000 / 976867092299) := by
    rw [show ((976867092299 / 500000000000) : ℝ) = ((500000000000 / 976867092299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13039_neg : (67514611 / 100000000) ≤ -Real.log (100000000000 / 196431996277) ∧
    -Real.log (100000000000 / 196431996277) ≤ (675146111 / 1000000000) := by
  have h := checkLog_sound (w := (96431996277 / 296431996277)) (n := 12)
    (lo := (67514611 / 100000000)) (hi := (675146111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196431996277 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196431996277 / 100000000000) = 1/(100000000000 / 196431996277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13039 : Bounds (67514611 / 100000000) (675146111 / 1000000000) (Real.log (196431996277 / 100000000000)) := by
  have h := reflection_log_13039_neg
  have he : Real.log (196431996277 / 100000000000) = -Real.log (100000000000 / 196431996277) := by
    rw [show ((196431996277 / 100000000000) : ℝ) = ((100000000000 / 196431996277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13040_neg : (1392556121 / 1000000000) ≤ -Real.log (50000000000 / 201256281407) ∧
    -Real.log (50000000000 / 201256281407) ≤ (348139031 / 250000000) := by
  have h := checkLog_sound (w := (1256281407 / 401256281407)) (n := 12)
    (lo := (6261761 / 1000000000)) (hi := (3130881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201256281407 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(201256281407 / 200000000000) = 1/(50000000000 / 201256281407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13040 : Bounds (1392556121 / 1000000000) (348139031 / 250000000) (Real.log (201256281407 / 50000000000)) := by
  have h := reflection_log_13040_neg
  have he : Real.log (201256281407 / 50000000000) = -Real.log (50000000000 / 201256281407) := by
    rw [show ((201256281407 / 50000000000) : ℝ) = ((50000000000 / 201256281407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13041_neg : (1401993269 / 1000000000) ≤ -Real.log (500000000000 / 2031645569621) ∧
    -Real.log (500000000000 / 2031645569621) ≤ (175249159 / 125000000) := by
  have h := checkLog_sound (w := (31645569621 / 4031645569621)) (n := 12)
    (lo := (15698909 / 1000000000)) (hi := (1569891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2031645569621 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2031645569621 / 2000000000000) = 1/(500000000000 / 2031645569621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13041 : Bounds (1401993269 / 1000000000) (175249159 / 125000000) (Real.log (2031645569621 / 500000000000)) := by
  have h := reflection_log_13041_neg
  have he : Real.log (2031645569621 / 500000000000) = -Real.log (500000000000 / 2031645569621) := by
    rw [show ((2031645569621 / 500000000000) : ℝ) = ((500000000000 / 2031645569621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13042_neg : (47499117 / 100000000) ≤ -Real.log (125 / 201) ∧
    -Real.log (125 / 201) ≤ (474991171 / 1000000000) := by
  have h := checkLog_sound (w := (38 / 163)) (n := 12)
    (lo := (47499117 / 100000000)) (hi := (474991171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201 / 125) = 1/(125 / 201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13042 : Bounds (47499117 / 100000000) (474991171 / 1000000000) (Real.log (201 / 125)) := by
  have h := reflection_log_13042_neg
  have he : Real.log (201 / 125) = -Real.log (125 / 201) := by
    rw [show ((201 / 125) : ℝ) = ((125 / 201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13043_neg : (468246719 / 500000000) ≤ -Real.log (49 / 125) ∧
    -Real.log (49 / 125) ≤ (1463271 / 1562500) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 98) = 1/(49 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13043 : Bounds (-1463271 / 1562500) (-468246719 / 500000000) (Real.log (49 / 125)) := by
  have h := reflection_log_13043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13044_neg : (121563 / 200000000) ≤ -Real.log (31250 / 31269) ∧
    -Real.log (31250 / 31269) ≤ (75977 / 125000000) := by
  have h := checkLog_sound (w := (19 / 62519)) (n := 12)
    (lo := (121563 / 200000000)) (hi := (75977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31269 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31269 / 31250) = 1/(31250 / 31269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13044 : Bounds (121563 / 200000000) (75977 / 125000000) (Real.log (31269 / 31250)) := by
  have h := reflection_log_13044_neg
  have he : Real.log (31269 / 31250) = -Real.log (31250 / 31269) := by
    rw [show ((31269 / 31250) : ℝ) = ((31250 / 31269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13045_neg : (76023 / 125000000) ≤ -Real.log (31231 / 31250) ∧
    -Real.log (31231 / 31250) ≤ (121637 / 200000000) := by
  have h := checkLog_sound (w := (19 / 62481)) (n := 12)
    (lo := (76023 / 125000000)) (hi := (121637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31231) = 1/(31231 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13045 : Bounds (-121637 / 200000000) (-76023 / 125000000) (Real.log (31231 / 31250)) := by
  have h := reflection_log_13045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13046_neg : (140613013 / 500000000) ≤ -Real.log (1000000 / 1324753) ∧
    -Real.log (1000000 / 1324753) ≤ (281226027 / 1000000000) := by
  have h := checkLog_sound (w := (324753 / 2324753)) (n := 12)
    (lo := (140613013 / 500000000)) (hi := (281226027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1324753 / 1000000) = 1/(1000000 / 1324753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13046 : Bounds (140613013 / 500000000) (281226027 / 1000000000) (Real.log (1324753 / 1000000)) := by
  have h := reflection_log_13046_neg
  have he : Real.log (1324753 / 1000000) = -Real.log (1000000 / 1324753) := by
    rw [show ((1324753 / 1000000) : ℝ) = ((1000000 / 1324753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13047_neg : (392676729 / 1000000000) ≤ -Real.log (675247 / 1000000) ∧
    -Real.log (675247 / 1000000) ≤ (39267673 / 100000000) := by
  have h := checkLog_sound (w := (324753 / 1675247)) (n := 12)
    (lo := (392676729 / 1000000000)) (hi := (39267673 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 675247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 675247) = 1/(675247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13047 : Bounds (-39267673 / 100000000) (-392676729 / 1000000000) (Real.log (675247 / 1000000)) := by
  have h := reflection_log_13047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13048_neg : (70763909 / 250000000) ≤ -Real.log (1000000 / 1327179) ∧
    -Real.log (1000000 / 1327179) ≤ (283055637 / 1000000000) := by
  have h := checkLog_sound (w := (327179 / 2327179)) (n := 12)
    (lo := (70763909 / 250000000)) (hi := (283055637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327179 / 1000000) = 1/(1000000 / 1327179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13048 : Bounds (70763909 / 250000000) (283055637 / 1000000000) (Real.log (1327179 / 1000000)) := by
  have h := reflection_log_13048_neg
  have he : Real.log (1327179 / 1000000) = -Real.log (1000000 / 1327179) := by
    rw [show ((1327179 / 1000000) : ℝ) = ((1000000 / 1327179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13049_neg : (396275957 / 1000000000) ≤ -Real.log (672821 / 1000000) ∧
    -Real.log (672821 / 1000000) ≤ (198137979 / 500000000) := by
  have h := checkLog_sound (w := (327179 / 1672821)) (n := 12)
    (lo := (396275957 / 1000000000)) (hi := (198137979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672821) = 1/(672821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13049 : Bounds (-198137979 / 500000000) (-396275957 / 1000000000) (Real.log (672821 / 1000000)) := by
  have h := reflection_log_13049_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13050_neg : (707627 / 6250000) ≤ -Real.log (892953901959 / 1000000000000) ∧
    -Real.log (892953901959 / 1000000000000) ≤ (113220321 / 1000000000) := by
  have h := checkLog_sound (w := (107046098041 / 1892953901959)) (n := 12)
    (lo := (707627 / 6250000)) (hi := (113220321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 892953901959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 892953901959) = 1/(892953901959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13050 : Bounds (-113220321 / 1000000000) (-707627 / 6250000) (Real.log (892953901959 / 1000000000000)) := by
  have h := reflection_log_13050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13051_neg : (55725351 / 500000000) ≤ -Real.log (894535488991 / 1000000000000) ∧
    -Real.log (894535488991 / 1000000000000) ≤ (111450703 / 1000000000) := by
  have h := checkLog_sound (w := (105464511009 / 1894535488991)) (n := 12)
    (lo := (55725351 / 500000000)) (hi := (111450703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 894535488991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 894535488991) = 1/(894535488991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13051 : Bounds (-111450703 / 1000000000) (-55725351 / 500000000) (Real.log (894535488991 / 1000000000000)) := by
  have h := reflection_log_13051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13052_neg : (168475689 / 250000000) ≤ -Real.log (500000000000 / 980939567299) ∧
    -Real.log (500000000000 / 980939567299) ≤ (673902757 / 1000000000) := by
  have h := checkLog_sound (w := (480939567299 / 1480939567299)) (n := 12)
    (lo := (168475689 / 250000000)) (hi := (673902757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980939567299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980939567299 / 500000000000) = 1/(500000000000 / 980939567299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13052 : Bounds (168475689 / 250000000) (673902757 / 1000000000) (Real.log (980939567299 / 500000000000)) := by
  have h := reflection_log_13052_neg
  have he : Real.log (980939567299 / 500000000000) = -Real.log (500000000000 / 980939567299) := by
    rw [show ((980939567299 / 500000000000) : ℝ) = ((500000000000 / 980939567299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13053_neg : (339665797 / 500000000) ≤ -Real.log (125000000000 / 246569852903) ∧
    -Real.log (125000000000 / 246569852903) ≤ (135866319 / 200000000) := by
  have h := checkLog_sound (w := (121569852903 / 371569852903)) (n := 12)
    (lo := (339665797 / 500000000)) (hi := (135866319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246569852903 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246569852903 / 125000000000) = 1/(125000000000 / 246569852903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13053 : Bounds (339665797 / 500000000) (135866319 / 200000000) (Real.log (246569852903 / 125000000000)) := by
  have h := reflection_log_13053_neg
  have he : Real.log (246569852903 / 125000000000) = -Real.log (125000000000 / 246569852903) := by
    rw [show ((246569852903 / 125000000000) : ℝ) = ((125000000000 / 246569852903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13054_neg : (1401993269 / 1000000000) ≤ -Real.log (25000000000 / 101582278481) ∧
    -Real.log (25000000000 / 101582278481) ≤ (175249159 / 125000000) := by
  have h := checkLog_sound (w := (1582278481 / 201582278481)) (n := 12)
    (lo := (15698909 / 1000000000)) (hi := (1569891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101582278481 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(101582278481 / 100000000000) = 1/(25000000000 / 101582278481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13054 : Bounds (1401993269 / 1000000000) (175249159 / 125000000) (Real.log (101582278481 / 25000000000)) := by
  have h := reflection_log_13054_neg
  have he : Real.log (101582278481 / 25000000000) = -Real.log (25000000000 / 101582278481) := by
    rw [show ((101582278481 / 25000000000) : ℝ) = ((25000000000 / 101582278481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13055_neg : (22054447 / 15625000) ≤ -Real.log (125000000000 / 512755102041) ∧
    -Real.log (125000000000 / 512755102041) ≤ (1411484611 / 1000000000) := by
  have h := checkLog_sound (w := (12755102041 / 1012755102041)) (n := 12)
    (lo := (3148781 / 125000000)) (hi := (25190249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512755102041 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(512755102041 / 500000000000) = 1/(125000000000 / 512755102041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13055 : Bounds (22054447 / 15625000) (1411484611 / 1000000000) (Real.log (512755102041 / 125000000000)) := by
  have h := reflection_log_13055_neg
  have he : Real.log (512755102041 / 125000000000) = -Real.log (125000000000 / 512755102041) := by
    rw [show ((512755102041 / 125000000000) : ℝ) = ((125000000000 / 512755102041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0204 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13056_neg : (7450861 / 15625000) ≤ -Real.log (1000 / 1611) ∧
    -Real.log (1000 / 1611) ≤ (95371021 / 200000000) := by
  have h := checkLog_sound (w := (611 / 2611)) (n := 12)
    (lo := (7450861 / 15625000)) (hi := (95371021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1611 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1611 / 1000) = 1/(1000 / 1611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13056 : Bounds (7450861 / 15625000) (95371021 / 200000000) (Real.log (1611 / 1000)) := by
  have h := reflection_log_13056_neg
  have he : Real.log (1611 / 1000) = -Real.log (1000 / 1611) := by
    rw [show ((1611 / 1000) : ℝ) = ((1000 / 1611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13057_neg : (472087967 / 500000000) ≤ -Real.log (389 / 1000) ∧
    -Real.log (389 / 1000) ≤ (14752749 / 15625000) := by
  have h := checkLog_sound (w := (111 / 889)) (n := 12)
    (lo := (125514377 / 500000000)) (hi := (50205751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 389) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 389) = 1/(389 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13057 : Bounds (-14752749 / 15625000) (-472087967 / 500000000) (Real.log (389 / 1000)) := by
  have h := reflection_log_13057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13058_neg : (610813 / 1000000000) ≤ -Real.log (1000000 / 1000611) ∧
    -Real.log (1000000 / 1000611) ≤ (305407 / 500000000) := by
  have h := checkLog_sound (w := (611 / 2000611)) (n := 12)
    (lo := (610813 / 1000000000)) (hi := (305407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000611 / 1000000) = 1/(1000000 / 1000611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13058 : Bounds (610813 / 1000000000) (305407 / 500000000) (Real.log (1000611 / 1000000)) := by
  have h := reflection_log_13058_neg
  have he : Real.log (1000611 / 1000000) = -Real.log (1000000 / 1000611) := by
    rw [show ((1000611 / 1000000) : ℝ) = ((1000000 / 1000611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13059_neg : (305593 / 500000000) ≤ -Real.log (999389 / 1000000) ∧
    -Real.log (999389 / 1000000) ≤ (611187 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 1999389)) (n := 12)
    (lo := (305593 / 500000000)) (hi := (611187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999389) = 1/(999389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13059 : Bounds (-611187 / 1000000000) (-305593 / 500000000) (Real.log (999389 / 1000000)) := by
  have h := reflection_log_13059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13060_neg : (282635107 / 1000000000) ≤ -Real.log (1000000 / 1326621) ∧
    -Real.log (1000000 / 1326621) ≤ (70658777 / 250000000) := by
  have h := checkLog_sound (w := (326621 / 2326621)) (n := 12)
    (lo := (282635107 / 1000000000)) (hi := (70658777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326621 / 1000000) = 1/(1000000 / 1326621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13060 : Bounds (282635107 / 1000000000) (70658777 / 250000000) (Real.log (1326621 / 1000000)) := by
  have h := reflection_log_13060_neg
  have he : Real.log (1326621 / 1000000) = -Real.log (1000000 / 1326621) := by
    rw [show ((1326621 / 1000000) : ℝ) = ((1000000 / 1326621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13061_neg : (395446957 / 1000000000) ≤ -Real.log (673379 / 1000000) ∧
    -Real.log (673379 / 1000000) ≤ (197723479 / 500000000) := by
  have h := checkLog_sound (w := (326621 / 1673379)) (n := 12)
    (lo := (395446957 / 1000000000)) (hi := (197723479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673379) = 1/(673379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13061 : Bounds (-197723479 / 500000000) (-395446957 / 1000000000) (Real.log (673379 / 1000000)) := by
  have h := reflection_log_13061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13062_neg : (142233329 / 500000000) ≤ -Real.log (1000000 / 1329053) ∧
    -Real.log (1000000 / 1329053) ≤ (284466659 / 1000000000) := by
  have h := checkLog_sound (w := (329053 / 2329053)) (n := 12)
    (lo := (142233329 / 500000000)) (hi := (284466659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329053 / 1000000) = 1/(1000000 / 1329053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13062 : Bounds (142233329 / 500000000) (284466659 / 1000000000) (Real.log (1329053 / 1000000)) := by
  have h := reflection_log_13062_neg
  have he : Real.log (1329053 / 1000000) = -Real.log (1000000 / 1329053) := by
    rw [show ((1329053 / 1000000) : ℝ) = ((1000000 / 1329053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13063_neg : (399065131 / 1000000000) ≤ -Real.log (670947 / 1000000) ∧
    -Real.log (670947 / 1000000) ≤ (99766283 / 250000000) := by
  have h := checkLog_sound (w := (329053 / 1670947)) (n := 12)
    (lo := (399065131 / 1000000000)) (hi := (99766283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670947) = 1/(670947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13063 : Bounds (-99766283 / 250000000) (-399065131 / 1000000000) (Real.log (670947 / 1000000)) := by
  have h := reflection_log_13063_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13064_neg : (114598473 / 1000000000) ≤ -Real.log (891724123191 / 1000000000000) ∧
    -Real.log (891724123191 / 1000000000000) ≤ (57299237 / 500000000) := by
  have h := checkLog_sound (w := (108275876809 / 1891724123191)) (n := 12)
    (lo := (114598473 / 1000000000)) (hi := (57299237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 891724123191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 891724123191) = 1/(891724123191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13064 : Bounds (-57299237 / 500000000) (-114598473 / 1000000000) (Real.log (891724123191 / 1000000000000)) := by
  have h := reflection_log_13064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13065_neg : (112811849 / 1000000000) ≤ -Real.log (893318722359 / 1000000000000) ∧
    -Real.log (893318722359 / 1000000000000) ≤ (2256237 / 20000000) := by
  have h := checkLog_sound (w := (106681277641 / 1893318722359)) (n := 12)
    (lo := (112811849 / 1000000000)) (hi := (2256237 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 893318722359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 893318722359) = 1/(893318722359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13065 : Bounds (-2256237 / 20000000) (-112811849 / 1000000000) (Real.log (893318722359 / 1000000000000)) := by
  have h := reflection_log_13065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13066_neg : (135616413 / 200000000) ≤ -Real.log (500000000000 / 985047796263) ∧
    -Real.log (500000000000 / 985047796263) ≤ (339041033 / 500000000) := by
  have h := checkLog_sound (w := (485047796263 / 1485047796263)) (n := 12)
    (lo := (135616413 / 200000000)) (hi := (339041033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985047796263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985047796263 / 500000000000) = 1/(500000000000 / 985047796263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13066 : Bounds (135616413 / 200000000) (339041033 / 500000000) (Real.log (985047796263 / 500000000000)) := by
  have h := reflection_log_13066_neg
  have he : Real.log (985047796263 / 500000000000) = -Real.log (500000000000 / 985047796263) := by
    rw [show ((985047796263 / 500000000000) : ℝ) = ((500000000000 / 985047796263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13067_neg : (68353179 / 100000000) ≤ -Real.log (500000000000 / 990430689757) ∧
    -Real.log (500000000000 / 990430689757) ≤ (683531791 / 1000000000) := by
  have h := checkLog_sound (w := (490430689757 / 1490430689757)) (n := 12)
    (lo := (68353179 / 100000000)) (hi := (683531791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990430689757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990430689757 / 500000000000) = 1/(500000000000 / 990430689757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13067 : Bounds (68353179 / 100000000) (683531791 / 1000000000) (Real.log (990430689757 / 500000000000)) := by
  have h := reflection_log_13067_neg
  have he : Real.log (990430689757 / 500000000000) = -Real.log (500000000000 / 990430689757) := by
    rw [show ((990430689757 / 500000000000) : ℝ) = ((500000000000 / 990430689757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13068_neg : (22054447 / 15625000) ≤ -Real.log (500000000000 / 2051020408163) ∧
    -Real.log (500000000000 / 2051020408163) ≤ (1411484611 / 1000000000) := by
  have h := checkLog_sound (w := (51020408163 / 4051020408163)) (n := 12)
    (lo := (3148781 / 125000000)) (hi := (25190249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2051020408163 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2051020408163 / 2000000000000) = 1/(500000000000 / 2051020408163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13068 : Bounds (22054447 / 15625000) (1411484611 / 1000000000) (Real.log (2051020408163 / 500000000000)) := by
  have h := reflection_log_13068_neg
  have he : Real.log (2051020408163 / 500000000000) = -Real.log (500000000000 / 2051020408163) := by
    rw [show ((2051020408163 / 500000000000) : ℝ) = ((500000000000 / 2051020408163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13069_neg : (710515519 / 500000000) ≤ -Real.log (125000000000 / 517673521851) ∧
    -Real.log (125000000000 / 517673521851) ≤ (1421031041 / 1000000000) := by
  have h := checkLog_sound (w := (17673521851 / 1017673521851)) (n := 12)
    (lo := (17368339 / 500000000)) (hi := (34736679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517673521851 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(517673521851 / 500000000000) = 1/(125000000000 / 517673521851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13069 : Bounds (710515519 / 500000000) (1421031041 / 1000000000) (Real.log (517673521851 / 125000000000)) := by
  have h := reflection_log_13069_neg
  have he : Real.log (517673521851 / 125000000000) = -Real.log (125000000000 / 517673521851) := by
    rw [show ((517673521851 / 125000000000) : ℝ) = ((125000000000 / 517673521851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13070_neg : (478715569 / 1000000000) ≤ -Real.log (500 / 807) ∧
    -Real.log (500 / 807) ≤ (47871557 / 100000000) := by
  have h := checkLog_sound (w := (307 / 1307)) (n := 12)
    (lo := (478715569 / 1000000000)) (hi := (47871557 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807 / 500) = 1/(500 / 807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13070 : Bounds (478715569 / 1000000000) (47871557 / 100000000) (Real.log (807 / 500)) := by
  have h := reflection_log_13070_neg
  have he : Real.log (807 / 500) = -Real.log (500 / 807) := by
    rw [show ((807 / 500) : ℝ) = ((500 / 807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13071_neg : (237979477 / 250000000) ≤ -Real.log (193 / 500) ∧
    -Real.log (193 / 500) ≤ (95191791 / 100000000) := by
  have h := checkLog_sound (w := (57 / 443)) (n := 12)
    (lo := (32346341 / 125000000)) (hi := (258770729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 193) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 193) = 1/(193 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13071 : Bounds (-95191791 / 100000000) (-237979477 / 250000000) (Real.log (193 / 500)) := by
  have h := reflection_log_13071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13072_neg : (613811 / 1000000000) ≤ -Real.log (500000 / 500307) ∧
    -Real.log (500000 / 500307) ≤ (153453 / 250000000) := by
  have h := checkLog_sound (w := (307 / 1000307)) (n := 12)
    (lo := (613811 / 1000000000)) (hi := (153453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500307 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500307 / 500000) = 1/(500000 / 500307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13072 : Bounds (613811 / 1000000000) (153453 / 250000000) (Real.log (500307 / 500000)) := by
  have h := reflection_log_13072_neg
  have he : Real.log (500307 / 500000) = -Real.log (500000 / 500307) := by
    rw [show ((500307 / 500000) : ℝ) = ((500000 / 500307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13073_neg : (153547 / 250000000) ≤ -Real.log (499693 / 500000) ∧
    -Real.log (499693 / 500000) ≤ (614189 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 999693)) (n := 12)
    (lo := (153547 / 250000000)) (hi := (614189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499693) = 1/(499693 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13073 : Bounds (-614189 / 1000000000) (-153547 / 250000000) (Real.log (499693 / 500000)) := by
  have h := reflection_log_13073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13074_neg : (284045217 / 1000000000) ≤ -Real.log (1000000 / 1328493) ∧
    -Real.log (1000000 / 1328493) ≤ (142022609 / 500000000) := by
  have h := checkLog_sound (w := (328493 / 2328493)) (n := 12)
    (lo := (284045217 / 1000000000)) (hi := (142022609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328493 / 1000000) = 1/(1000000 / 1328493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13074 : Bounds (284045217 / 1000000000) (142022609 / 500000000) (Real.log (1328493 / 1000000)) := by
  have h := reflection_log_13074_neg
  have he : Real.log (1328493 / 1000000) = -Real.log (1000000 / 1328493) := by
    rw [show ((1328493 / 1000000) : ℝ) = ((1000000 / 1328493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13075_neg : (199115419 / 500000000) ≤ -Real.log (671507 / 1000000) ∧
    -Real.log (671507 / 1000000) ≤ (398230839 / 1000000000) := by
  have h := checkLog_sound (w := (328493 / 1671507)) (n := 12)
    (lo := (199115419 / 500000000)) (hi := (398230839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671507) = 1/(671507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13075 : Bounds (-398230839 / 1000000000) (-199115419 / 500000000) (Real.log (671507 / 1000000)) := by
  have h := reflection_log_13075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13076_neg : (35734931 / 125000000) ≤ -Real.log (250000 / 332733) ∧
    -Real.log (250000 / 332733) ≤ (285879449 / 1000000000) := by
  have h := checkLog_sound (w := (82733 / 582733)) (n := 12)
    (lo := (35734931 / 125000000)) (hi := (285879449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332733 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332733 / 250000) = 1/(250000 / 332733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13076 : Bounds (35734931 / 125000000) (285879449 / 1000000000) (Real.log (332733 / 250000)) := by
  have h := reflection_log_13076_neg
  have he : Real.log (332733 / 250000) = -Real.log (250000 / 332733) := by
    rw [show ((332733 / 250000) : ℝ) = ((250000 / 332733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13077_neg : (401869579 / 1000000000) ≤ -Real.log (167267 / 250000) ∧
    -Real.log (167267 / 250000) ≤ (20093479 / 50000000) := by
  have h := checkLog_sound (w := (82733 / 417267)) (n := 12)
    (lo := (401869579 / 1000000000)) (hi := (20093479 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 167267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 167267) = 1/(167267 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13077 : Bounds (-20093479 / 50000000) (-401869579 / 1000000000) (Real.log (167267 / 250000)) := by
  have h := reflection_log_13077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13078_neg : (115990131 / 1000000000) ≤ -Real.log (55655250711 / 62500000000) ∧
    -Real.log (55655250711 / 62500000000) ≤ (28997533 / 250000000) := by
  have h := checkLog_sound (w := (6844749289 / 118155250711)) (n := 12)
    (lo := (115990131 / 1000000000)) (hi := (28997533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55655250711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55655250711) = 1/(55655250711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13078 : Bounds (-28997533 / 250000000) (-115990131 / 1000000000) (Real.log (55655250711 / 62500000000)) := by
  have h := reflection_log_13078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13079_neg : (114185621 / 1000000000) ≤ -Real.log (892092348951 / 1000000000000) ∧
    -Real.log (892092348951 / 1000000000000) ≤ (57092811 / 500000000) := by
  have h := checkLog_sound (w := (107907651049 / 1892092348951)) (n := 12)
    (lo := (114185621 / 1000000000)) (hi := (57092811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 892092348951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 892092348951) = 1/(892092348951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13079 : Bounds (-57092811 / 500000000) (-114185621 / 1000000000) (Real.log (892092348951 / 1000000000000)) := by
  have h := reflection_log_13079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13080_neg : (136455211 / 200000000) ≤ -Real.log (125000000000 / 247296938081) ∧
    -Real.log (125000000000 / 247296938081) ≤ (85284507 / 125000000) := by
  have h := checkLog_sound (w := (122296938081 / 372296938081)) (n := 12)
    (lo := (136455211 / 200000000)) (hi := (85284507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247296938081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247296938081 / 125000000000) = 1/(125000000000 / 247296938081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13080 : Bounds (136455211 / 200000000) (85284507 / 125000000) (Real.log (247296938081 / 125000000000)) := by
  have h := reflection_log_13080_neg
  have he : Real.log (247296938081 / 125000000000) = -Real.log (125000000000 / 247296938081) := by
    rw [show ((247296938081 / 125000000000) : ℝ) = ((125000000000 / 247296938081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13081_neg : (171937257 / 250000000) ≤ -Real.log (500000000000 / 994616391757) ∧
    -Real.log (500000000000 / 994616391757) ≤ (687749029 / 1000000000) := by
  have h := checkLog_sound (w := (494616391757 / 1494616391757)) (n := 12)
    (lo := (171937257 / 250000000)) (hi := (687749029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((994616391757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(994616391757 / 500000000000) = 1/(500000000000 / 994616391757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13081 : Bounds (171937257 / 250000000) (687749029 / 1000000000) (Real.log (994616391757 / 500000000000)) := by
  have h := reflection_log_13081_neg
  have he : Real.log (994616391757 / 500000000000) = -Real.log (500000000000 / 994616391757) := by
    rw [show ((994616391757 / 500000000000) : ℝ) = ((500000000000 / 994616391757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13082_neg : (710515519 / 500000000) ≤ -Real.log (500000000000 / 2070694087403) ∧
    -Real.log (500000000000 / 2070694087403) ≤ (1421031041 / 1000000000) := by
  have h := checkLog_sound (w := (70694087403 / 4070694087403)) (n := 12)
    (lo := (17368339 / 500000000)) (hi := (34736679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2070694087403 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2070694087403 / 2000000000000) = 1/(500000000000 / 2070694087403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13082 : Bounds (710515519 / 500000000) (1421031041 / 1000000000) (Real.log (2070694087403 / 500000000000)) := by
  have h := reflection_log_13082_neg
  have he : Real.log (2070694087403 / 500000000000) = -Real.log (500000000000 / 2070694087403) := by
    rw [show ((2070694087403 / 500000000000) : ℝ) = ((500000000000 / 2070694087403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13083_neg : (715316739 / 500000000) ≤ -Real.log (50000000000 / 209067357513) ∧
    -Real.log (50000000000 / 209067357513) ≤ (1430633481 / 1000000000) := by
  have h := checkLog_sound (w := (9067357513 / 409067357513)) (n := 12)
    (lo := (22169559 / 500000000)) (hi := (44339119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209067357513 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(209067357513 / 200000000000) = 1/(50000000000 / 209067357513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13083 : Bounds (715316739 / 500000000) (1430633481 / 1000000000) (Real.log (209067357513 / 50000000000)) := by
  have h := reflection_log_13083_neg
  have he : Real.log (209067357513 / 50000000000) = -Real.log (50000000000 / 209067357513) := by
    rw [show ((209067357513 / 50000000000) : ℝ) = ((50000000000 / 209067357513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13084_neg : (24028629 / 50000000) ≤ -Real.log (1000 / 1617) ∧
    -Real.log (1000 / 1617) ≤ (480572581 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 2617)) (n := 12)
    (lo := (24028629 / 50000000)) (hi := (480572581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617 / 1000) = 1/(1000 / 1617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13084 : Bounds (24028629 / 50000000) (480572581 / 1000000000) (Real.log (1617 / 1000)) := by
  have h := reflection_log_13084_neg
  have he : Real.log (1617 / 1000) = -Real.log (1000 / 1617) := by
    rw [show ((1617 / 1000) : ℝ) = ((1000 / 1617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13085_neg : (959720289 / 1000000000) ≤ -Real.log (383 / 1000) ∧
    -Real.log (383 / 1000) ≤ (959720291 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 883)) (n := 12)
    (lo := (266573109 / 1000000000)) (hi := (26657311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 383) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 383) = 1/(383 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13085 : Bounds (-959720291 / 1000000000) (-959720289 / 1000000000) (Real.log (383 / 1000)) := by
  have h := reflection_log_13085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13086_neg : (616809 / 1000000000) ≤ -Real.log (1000000 / 1000617) ∧
    -Real.log (1000000 / 1000617) ≤ (61681 / 100000000) := by
  have h := checkLog_sound (w := (617 / 2000617)) (n := 12)
    (lo := (616809 / 1000000000)) (hi := (61681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000617 / 1000000) = 1/(1000000 / 1000617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13086 : Bounds (616809 / 1000000000) (61681 / 100000000) (Real.log (1000617 / 1000000)) := by
  have h := reflection_log_13086_neg
  have he : Real.log (1000617 / 1000000) = -Real.log (1000000 / 1000617) := by
    rw [show ((1000617 / 1000000) : ℝ) = ((1000000 / 1000617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13087_neg : (61719 / 100000000) ≤ -Real.log (999383 / 1000000) ∧
    -Real.log (999383 / 1000000) ≤ (617191 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 1999383)) (n := 12)
    (lo := (61719 / 100000000)) (hi := (617191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999383) = 1/(999383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13087 : Bounds (-617191 / 1000000000) (-61719 / 100000000) (Real.log (999383 / 1000000)) := by
  have h := reflection_log_13087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13088_neg : (285456347 / 1000000000) ≤ -Real.log (1000000 / 1330369) ∧
    -Real.log (1000000 / 1330369) ≤ (71364087 / 250000000) := by
  have h := checkLog_sound (w := (330369 / 2330369)) (n := 12)
    (lo := (285456347 / 1000000000)) (hi := (71364087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1330369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1330369 / 1000000) = 1/(1000000 / 1330369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13088 : Bounds (285456347 / 1000000000) (71364087 / 250000000) (Real.log (1330369 / 1000000)) := by
  have h := reflection_log_13088_neg
  have he : Real.log (1330369 / 1000000) = -Real.log (1000000 / 1330369) := by
    rw [show ((1330369 / 1000000) : ℝ) = ((1000000 / 1330369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13089_neg : (25064279 / 62500000) ≤ -Real.log (669631 / 1000000) ∧
    -Real.log (669631 / 1000000) ≤ (80205693 / 200000000) := by
  have h := checkLog_sound (w := (330369 / 1669631)) (n := 12)
    (lo := (25064279 / 62500000)) (hi := (80205693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 669631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 669631) = 1/(669631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13089 : Bounds (-80205693 / 200000000) (-25064279 / 62500000) (Real.log (669631 / 1000000)) := by
  have h := reflection_log_13089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13090_neg : (143646623 / 500000000) ≤ -Real.log (200000 / 266563) ∧
    -Real.log (200000 / 266563) ≤ (287293247 / 1000000000) := by
  have h := checkLog_sound (w := (66563 / 466563)) (n := 12)
    (lo := (143646623 / 500000000)) (hi := (287293247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266563 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266563 / 200000) = 1/(200000 / 266563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13090 : Bounds (143646623 / 500000000) (287293247 / 1000000000) (Real.log (266563 / 200000)) := by
  have h := reflection_log_13090_neg
  have he : Real.log (266563 / 200000) = -Real.log (200000 / 266563) := by
    rw [show ((266563 / 200000) : ℝ) = ((200000 / 266563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13091_neg : (40468791 / 100000000) ≤ -Real.log (133437 / 200000) ∧
    -Real.log (133437 / 200000) ≤ (404687911 / 1000000000) := by
  have h := checkLog_sound (w := (66563 / 333437)) (n := 12)
    (lo := (40468791 / 100000000)) (hi := (404687911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133437) = 1/(133437 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13091 : Bounds (-404687911 / 1000000000) (-40468791 / 100000000) (Real.log (133437 / 200000)) := by
  have h := reflection_log_13091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13092_neg : (117394663 / 1000000000) ≤ -Real.log (35569367031 / 40000000000) ∧
    -Real.log (35569367031 / 40000000000) ≤ (14674333 / 125000000) := by
  have h := checkLog_sound (w := (4430632969 / 75569367031)) (n := 12)
    (lo := (117394663 / 1000000000)) (hi := (14674333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 35569367031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 35569367031) = 1/(35569367031 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13092 : Bounds (-14674333 / 125000000) (-117394663 / 1000000000) (Real.log (35569367031 / 40000000000)) := by
  have h := reflection_log_13092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13093_neg : (115572117 / 1000000000) ≤ -Real.log (890856323839 / 1000000000000) ∧
    -Real.log (890856323839 / 1000000000000) ≤ (57786059 / 500000000) := by
  have h := checkLog_sound (w := (109143676161 / 1890856323839)) (n := 12)
    (lo := (115572117 / 1000000000)) (hi := (57786059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 890856323839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 890856323839) = 1/(890856323839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13093 : Bounds (-57786059 / 500000000) (-115572117 / 1000000000) (Real.log (890856323839 / 1000000000000)) := by
  have h := reflection_log_13093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13094_neg : (686484811 / 1000000000) ≤ -Real.log (500000000000 / 993359775757) ∧
    -Real.log (500000000000 / 993359775757) ≤ (171621203 / 250000000) := by
  have h := checkLog_sound (w := (493359775757 / 1493359775757)) (n := 12)
    (lo := (686484811 / 1000000000)) (hi := (171621203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993359775757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993359775757 / 500000000000) = 1/(500000000000 / 993359775757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13094 : Bounds (686484811 / 1000000000) (171621203 / 250000000) (Real.log (993359775757 / 500000000000)) := by
  have h := reflection_log_13094_neg
  have he : Real.log (993359775757 / 500000000000) = -Real.log (500000000000 / 993359775757) := by
    rw [show ((993359775757 / 500000000000) : ℝ) = ((500000000000 / 993359775757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13095_neg : (691981157 / 1000000000) ≤ -Real.log (100000000000 / 199766931211) ∧
    -Real.log (100000000000 / 199766931211) ≤ (345990579 / 500000000) := by
  have h := checkLog_sound (w := (99766931211 / 299766931211)) (n := 12)
    (lo := (691981157 / 1000000000)) (hi := (345990579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199766931211 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199766931211 / 100000000000) = 1/(100000000000 / 199766931211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13095 : Bounds (691981157 / 1000000000) (345990579 / 500000000) (Real.log (199766931211 / 100000000000)) := by
  have h := reflection_log_13095_neg
  have he : Real.log (199766931211 / 100000000000) = -Real.log (100000000000 / 199766931211) := by
    rw [show ((199766931211 / 100000000000) : ℝ) = ((100000000000 / 199766931211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13096_neg : (715316739 / 500000000) ≤ -Real.log (500000000000 / 2090673575129) ∧
    -Real.log (500000000000 / 2090673575129) ≤ (1430633481 / 1000000000) := by
  have h := checkLog_sound (w := (90673575129 / 4090673575129)) (n := 12)
    (lo := (22169559 / 500000000)) (hi := (44339119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2090673575129 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2090673575129 / 2000000000000) = 1/(500000000000 / 2090673575129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13096 : Bounds (715316739 / 500000000) (1430633481 / 1000000000) (Real.log (2090673575129 / 500000000000)) := by
  have h := reflection_log_13096_neg
  have he : Real.log (2090673575129 / 500000000000) = -Real.log (500000000000 / 2090673575129) := by
    rw [show ((2090673575129 / 500000000000) : ℝ) = ((500000000000 / 2090673575129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13097_neg : (1440292869 / 1000000000) ≤ -Real.log (250000000000 / 1055483028721) ∧
    -Real.log (250000000000 / 1055483028721) ≤ (180036609 / 125000000) := by
  have h := checkLog_sound (w := (55483028721 / 2055483028721)) (n := 12)
    (lo := (53998509 / 1000000000)) (hi := (5399851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055483028721 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1055483028721 / 1000000000000) = 1/(250000000000 / 1055483028721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13097 : Bounds (1440292869 / 1000000000) (180036609 / 125000000) (Real.log (1055483028721 / 250000000000)) := by
  have h := reflection_log_13097_neg
  have he : Real.log (1055483028721 / 250000000000) = -Real.log (250000000000 / 1055483028721) := by
    rw [show ((1055483028721 / 250000000000) : ℝ) = ((250000000000 / 1055483028721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13098_neg : (482426149 / 1000000000) ≤ -Real.log (50 / 81) ∧
    -Real.log (50 / 81) ≤ (9648523 / 20000000) := by
  have h := checkLog_sound (w := (31 / 131)) (n := 12)
    (lo := (482426149 / 1000000000)) (hi := (9648523 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 50) = 1/(50 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13098 : Bounds (482426149 / 1000000000) (9648523 / 20000000) (Real.log (81 / 50)) := by
  have h := reflection_log_13098_neg
  have he : Real.log (81 / 50) = -Real.log (50 / 81) := by
    rw [show ((81 / 50) : ℝ) = ((50 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13099_neg : (38703361 / 40000000) ≤ -Real.log (19 / 50) ∧
    -Real.log (19 / 50) ≤ (967584027 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 22)) (n := 12)
    (lo := (54887369 / 200000000)) (hi := (137218423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 19) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 19) = 1/(19 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13099 : Bounds (-967584027 / 1000000000) (-38703361 / 40000000) (Real.log (19 / 50)) := by
  have h := reflection_log_13099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13100_neg : (619807 / 1000000000) ≤ -Real.log (50000 / 50031) ∧
    -Real.log (50000 / 50031) ≤ (19369 / 31250000) := by
  have h := checkLog_sound (w := (31 / 100031)) (n := 12)
    (lo := (619807 / 1000000000)) (hi := (19369 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50031 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50031 / 50000) = 1/(50000 / 50031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13100 : Bounds (619807 / 1000000000) (19369 / 31250000) (Real.log (50031 / 50000)) := by
  have h := reflection_log_13100_neg
  have he : Real.log (50031 / 50000) = -Real.log (50000 / 50031) := by
    rw [show ((50031 / 50000) : ℝ) = ((50000 / 50031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13101_neg : (19381 / 31250000) ≤ -Real.log (49969 / 50000) ∧
    -Real.log (49969 / 50000) ≤ (620193 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 99969)) (n := 12)
    (lo := (19381 / 31250000)) (hi := (620193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49969) = 1/(49969 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13101 : Bounds (-620193 / 1000000000) (-19381 / 31250000) (Real.log (49969 / 50000)) := by
  have h := reflection_log_13101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13102_neg : (35858749 / 125000000) ≤ -Real.log (1000000 / 1332251) ∧
    -Real.log (1000000 / 1332251) ≤ (286869993 / 1000000000) := by
  have h := checkLog_sound (w := (332251 / 2332251)) (n := 12)
    (lo := (35858749 / 125000000)) (hi := (286869993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1332251 / 1000000) = 1/(1000000 / 1332251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13102 : Bounds (35858749 / 125000000) (286869993 / 1000000000) (Real.log (1332251 / 1000000)) := by
  have h := reflection_log_13102_neg
  have he : Real.log (1332251 / 1000000) = -Real.log (1000000 / 1332251) := by
    rw [show ((1332251 / 1000000) : ℝ) = ((1000000 / 1332251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13103_neg : (100960731 / 250000000) ≤ -Real.log (667749 / 1000000) ∧
    -Real.log (667749 / 1000000) ≤ (16153717 / 40000000) := by
  have h := checkLog_sound (w := (332251 / 1667749)) (n := 12)
    (lo := (100960731 / 250000000)) (hi := (16153717 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 667749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 667749) = 1/(667749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13103 : Bounds (-16153717 / 40000000) (-100960731 / 250000000) (Real.log (667749 / 1000000)) := by
  have h := reflection_log_13103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13104_neg : (57741759 / 200000000) ≤ -Real.log (1000000 / 1334703) ∧
    -Real.log (1000000 / 1334703) ≤ (72177199 / 250000000) := by
  have h := checkLog_sound (w := (334703 / 2334703)) (n := 12)
    (lo := (57741759 / 200000000)) (hi := (72177199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334703 / 1000000) = 1/(1000000 / 1334703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13104 : Bounds (57741759 / 200000000) (72177199 / 250000000) (Real.log (1334703 / 1000000)) := by
  have h := reflection_log_13104_neg
  have he : Real.log (1334703 / 1000000) = -Real.log (1000000 / 1334703) := by
    rw [show ((1334703 / 1000000) : ℝ) = ((1000000 / 1334703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13105_neg : (407521721 / 1000000000) ≤ -Real.log (665297 / 1000000) ∧
    -Real.log (665297 / 1000000) ≤ (203760861 / 500000000) := by
  have h := checkLog_sound (w := (334703 / 1665297)) (n := 12)
    (lo := (407521721 / 1000000000)) (hi := (203760861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665297) = 1/(665297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13105 : Bounds (-203760861 / 500000000) (-407521721 / 1000000000) (Real.log (665297 / 1000000)) := by
  have h := reflection_log_13105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13106_neg : (59406463 / 500000000) ≤ -Real.log (887973901791 / 1000000000000) ∧
    -Real.log (887973901791 / 1000000000000) ≤ (118812927 / 1000000000) := by
  have h := checkLog_sound (w := (112026098209 / 1887973901791)) (n := 12)
    (lo := (59406463 / 500000000)) (hi := (118812927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 887973901791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 887973901791) = 1/(887973901791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13106 : Bounds (-118812927 / 1000000000) (-59406463 / 500000000) (Real.log (887973901791 / 1000000000000)) := by
  have h := reflection_log_13106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13107_neg : (116972931 / 1000000000) ≤ -Real.log (889609272999 / 1000000000000) ∧
    -Real.log (889609272999 / 1000000000000) ≤ (29243233 / 250000000) := by
  have h := checkLog_sound (w := (110390727001 / 1889609272999)) (n := 12)
    (lo := (116972931 / 1000000000)) (hi := (29243233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 889609272999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 889609272999) = 1/(889609272999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13107 : Bounds (-29243233 / 250000000) (-116972931 / 1000000000) (Real.log (889609272999 / 1000000000000)) := by
  have h := reflection_log_13107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13108_neg : (690712917 / 1000000000) ≤ -Real.log (25000000000 / 49878434861) ∧
    -Real.log (25000000000 / 49878434861) ≤ (345356459 / 500000000) := by
  have h := checkLog_sound (w := (24878434861 / 74878434861)) (n := 12)
    (lo := (690712917 / 1000000000)) (hi := (345356459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49878434861 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49878434861 / 25000000000) = 1/(25000000000 / 49878434861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13108 : Bounds (690712917 / 1000000000) (345356459 / 500000000) (Real.log (49878434861 / 25000000000)) := by
  have h := reflection_log_13108_neg
  have he : Real.log (49878434861 / 25000000000) = -Real.log (25000000000 / 49878434861) := by
    rw [show ((49878434861 / 25000000000) : ℝ) = ((25000000000 / 49878434861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13109_neg : (174057629 / 250000000) ≤ -Real.log (500000000000 / 1003088094491) ∧
    -Real.log (500000000000 / 1003088094491) ≤ (348115259 / 500000000) := by
  have h := checkLog_sound (w := (3088094491 / 2003088094491)) (n := 12)
    (lo := (385417 / 125000000)) (hi := (3083337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003088094491 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003088094491 / 1000000000000) = 1/(500000000000 / 1003088094491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13109 : Bounds (174057629 / 250000000) (348115259 / 500000000) (Real.log (1003088094491 / 500000000000)) := by
  have h := reflection_log_13109_neg
  have he : Real.log (1003088094491 / 500000000000) = -Real.log (500000000000 / 1003088094491) := by
    rw [show ((1003088094491 / 500000000000) : ℝ) = ((500000000000 / 1003088094491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13110_neg : (1440292869 / 1000000000) ≤ -Real.log (500000000000 / 2110966057441) ∧
    -Real.log (500000000000 / 2110966057441) ≤ (180036609 / 125000000) := by
  have h := checkLog_sound (w := (110966057441 / 4110966057441)) (n := 12)
    (lo := (53998509 / 1000000000)) (hi := (5399851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2110966057441 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2110966057441 / 2000000000000) = 1/(500000000000 / 2110966057441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13110 : Bounds (1440292869 / 1000000000) (180036609 / 125000000) (Real.log (2110966057441 / 500000000000)) := by
  have h := reflection_log_13110_neg
  have he : Real.log (2110966057441 / 500000000000) = -Real.log (500000000000 / 2110966057441) := by
    rw [show ((2110966057441 / 500000000000) : ℝ) = ((500000000000 / 2110966057441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13111_neg : (725005087 / 500000000) ≤ -Real.log (500000000000 / 2131578947369) ∧
    -Real.log (500000000000 / 2131578947369) ≤ (1450010177 / 1000000000) := by
  have h := checkLog_sound (w := (131578947369 / 4131578947369)) (n := 12)
    (lo := (31857907 / 500000000)) (hi := (12743163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2131578947369 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2131578947369 / 2000000000000) = 1/(500000000000 / 2131578947369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13111 : Bounds (725005087 / 500000000) (1450010177 / 1000000000) (Real.log (2131578947369 / 500000000000)) := by
  have h := reflection_log_13111_neg
  have he : Real.log (2131578947369 / 500000000000) = -Real.log (500000000000 / 2131578947369) := by
    rw [show ((2131578947369 / 500000000000) : ℝ) = ((500000000000 / 2131578947369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13112_neg : (7566817 / 15625000) ≤ -Real.log (1000 / 1623) ∧
    -Real.log (1000 / 1623) ≤ (484276289 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 2623)) (n := 12)
    (lo := (7566817 / 15625000)) (hi := (484276289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623 / 1000) = 1/(1000 / 1623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13112 : Bounds (7566817 / 15625000) (484276289 / 1000000000) (Real.log (1623 / 1000)) := by
  have h := reflection_log_13112_neg
  have he : Real.log (1623 / 1000) = -Real.log (1000 / 1623) := by
    rw [show ((1623 / 1000) : ℝ) = ((1000 / 1623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13113_neg : (97551009 / 100000000) ≤ -Real.log (377 / 1000) ∧
    -Real.log (377 / 1000) ≤ (243877523 / 250000000) := by
  have h := checkLog_sound (w := (123 / 877)) (n := 12)
    (lo := (28236291 / 100000000)) (hi := (282362911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 377) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 377) = 1/(377 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13113 : Bounds (-243877523 / 250000000) (-97551009 / 100000000) (Real.log (377 / 1000)) := by
  have h := reflection_log_13113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13114_neg : (311403 / 500000000) ≤ -Real.log (1000000 / 1000623) ∧
    -Real.log (1000000 / 1000623) ≤ (622807 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 2000623)) (n := 12)
    (lo := (311403 / 500000000)) (hi := (622807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000623 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000623 / 1000000) = 1/(1000000 / 1000623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13114 : Bounds (311403 / 500000000) (622807 / 1000000000) (Real.log (1000623 / 1000000)) := by
  have h := reflection_log_13114_neg
  have he : Real.log (1000623 / 1000000) = -Real.log (1000000 / 1000623) := by
    rw [show ((1000623 / 1000000) : ℝ) = ((1000000 / 1000623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13115_neg : (311597 / 500000000) ≤ -Real.log (999377 / 1000000) ∧
    -Real.log (999377 / 1000000) ≤ (124639 / 200000000) := by
  have h := checkLog_sound (w := (623 / 1999377)) (n := 12)
    (lo := (311597 / 500000000)) (hi := (124639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999377) = 1/(999377 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13115 : Bounds (-124639 / 200000000) (-311597 / 500000000) (Real.log (999377 / 1000000)) := by
  have h := reflection_log_13115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13116_neg : (1801779 / 6250000) ≤ -Real.log (1000000 / 1334137) ∧
    -Real.log (1000000 / 1334137) ≤ (288284641 / 1000000000) := by
  have h := checkLog_sound (w := (334137 / 2334137)) (n := 12)
    (lo := (1801779 / 6250000)) (hi := (288284641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334137 / 1000000) = 1/(1000000 / 1334137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13116 : Bounds (1801779 / 6250000) (288284641 / 1000000000) (Real.log (1334137 / 1000000)) := by
  have h := reflection_log_13116_neg
  have he : Real.log (1334137 / 1000000) = -Real.log (1000000 / 1334137) := by
    rw [show ((1334137 / 1000000) : ℝ) = ((1000000 / 1334137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13117_neg : (81334267 / 200000000) ≤ -Real.log (665863 / 1000000) ∧
    -Real.log (665863 / 1000000) ≤ (50833917 / 125000000) := by
  have h := checkLog_sound (w := (334137 / 1665863)) (n := 12)
    (lo := (81334267 / 200000000)) (hi := (50833917 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665863) = 1/(665863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13117 : Bounds (-50833917 / 125000000) (-81334267 / 200000000) (Real.log (665863 / 1000000)) := by
  have h := reflection_log_13117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13118_neg : (290126083 / 1000000000) ≤ -Real.log (250000 / 334149) ∧
    -Real.log (250000 / 334149) ≤ (72531521 / 250000000) := by
  have h := checkLog_sound (w := (84149 / 584149)) (n := 12)
    (lo := (290126083 / 1000000000)) (hi := (72531521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334149 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334149 / 250000) = 1/(250000 / 334149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13118 : Bounds (290126083 / 1000000000) (72531521 / 250000000) (Real.log (334149 / 250000)) := by
  have h := reflection_log_13118_neg
  have he : Real.log (334149 / 250000) = -Real.log (250000 / 334149) := by
    rw [show ((334149 / 250000) : ℝ) = ((250000 / 334149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13119_neg : (205185561 / 500000000) ≤ -Real.log (165851 / 250000) ∧
    -Real.log (165851 / 250000) ≤ (410371123 / 1000000000) := by
  have h := checkLog_sound (w := (84149 / 415851)) (n := 12)
    (lo := (205185561 / 500000000)) (hi := (410371123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 165851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 165851) = 1/(165851 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13119 : Bounds (-410371123 / 1000000000) (-205185561 / 500000000) (Real.log (165851 / 250000)) := by
  have h := reflection_log_13119_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


