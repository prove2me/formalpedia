-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0214__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0214__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:04:20.240691+00:00
-- url     : https://prove2.me/theorems/63028280-89d5-47c3-ad8b-5047bc8b3fef
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0214 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0215, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0214 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0215, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0216)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0214 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0215, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0216)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0214 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0215, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0216) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0214 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0215, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0216).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0214 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13696_neg : (893078217 / 1000000000) ≤ -Real.log (250000000000 / 610659264997) ∧
    -Real.log (250000000000 / 610659264997) ≤ (893078219 / 1000000000) := by
  have h := checkLog_sound (w := (110659264997 / 1110659264997)) (n := 12)
    (lo := (199931037 / 1000000000)) (hi := (99965519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610659264997 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(610659264997 / 500000000000) = 1/(250000000000 / 610659264997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13696 : Bounds (893078217 / 1000000000) (893078219 / 1000000000) (Real.log (610659264997 / 250000000000)) := by
  have h := reflection_log_13696_neg
  have he : Real.log (610659264997 / 250000000000) = -Real.log (250000000000 / 610659264997) := by
    rw [show ((610659264997 / 250000000000) : ℝ) = ((250000000000 / 610659264997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13697_neg : (1914286959 / 1000000000) ≤ -Real.log (500000000000 / 3391050583657) ∧
    -Real.log (500000000000 / 3391050583657) ≤ (957143481 / 500000000) := by
  have h := checkLog_sound (w := (1391050583657 / 5391050583657)) (n := 12)
    (lo := (527992599 / 1000000000)) (hi := (2639963 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3391050583657 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3391050583657 / 2000000000000) = 1/(500000000000 / 3391050583657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13697 : Bounds (1914286959 / 1000000000) (957143481 / 500000000) (Real.log (3391050583657 / 500000000000)) := by
  have h := reflection_log_13697_neg
  have he : Real.log (3391050583657 / 500000000000) = -Real.log (500000000000 / 3391050583657) := by
    rw [show ((3391050583657 / 500000000000) : ℝ) = ((500000000000 / 3391050583657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13698_neg : (481937117 / 250000000) ≤ -Real.log (15625000000 / 107406496063) ∧
    -Real.log (15625000000 / 107406496063) ≤ (1927748471 / 1000000000) := by
  have h := checkLog_sound (w := (44906496063 / 169906496063)) (n := 12)
    (lo := (135363527 / 250000000)) (hi := (541454109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107406496063 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(107406496063 / 62500000000) = 1/(15625000000 / 107406496063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13698 : Bounds (481937117 / 250000000) (1927748471 / 1000000000) (Real.log (107406496063 / 15625000000)) := by
  have h := reflection_log_13698_neg
  have he : Real.log (107406496063 / 15625000000) = -Real.log (15625000000 / 107406496063) := by
    rw [show ((107406496063 / 15625000000) : ℝ) = ((15625000000 / 107406496063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13699_neg : (139761049 / 250000000) ≤ -Real.log (1000 / 1749) ∧
    -Real.log (1000 / 1749) ≤ (559044197 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 2749)) (n := 12)
    (lo := (139761049 / 250000000)) (hi := (559044197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1749 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1749 / 1000) = 1/(1000 / 1749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13699 : Bounds (139761049 / 250000000) (559044197 / 1000000000) (Real.log (1749 / 1000)) := by
  have h := reflection_log_13699_neg
  have he : Real.log (1749 / 1000) = -Real.log (1000 / 1749) := by
    rw [show ((1749 / 1000) : ℝ) = ((1000 / 1749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13700_neg : (1382302339 / 1000000000) ≤ -Real.log (251 / 1000) ∧
    -Real.log (251 / 1000) ≤ (1382302341 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 751)) (n := 12)
    (lo := (689155159 / 1000000000)) (hi := (17228879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 251) = 1/(251 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13700 : Bounds (-1382302341 / 1000000000) (-1382302339 / 1000000000) (Real.log (251 / 1000)) := by
  have h := reflection_log_13700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13701_neg : (748719 / 1000000000) ≤ -Real.log (1000000 / 1000749) ∧
    -Real.log (1000000 / 1000749) ≤ (9359 / 12500000) := by
  have h := checkLog_sound (w := (749 / 2000749)) (n := 12)
    (lo := (748719 / 1000000000)) (hi := (9359 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000749 / 1000000) = 1/(1000000 / 1000749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13701 : Bounds (748719 / 1000000000) (9359 / 12500000) (Real.log (1000749 / 1000000)) := by
  have h := reflection_log_13701_neg
  have he : Real.log (1000749 / 1000000) = -Real.log (1000000 / 1000749) := by
    rw [show ((1000749 / 1000000) : ℝ) = ((1000000 / 1000749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13702_neg : (4683 / 6250000) ≤ -Real.log (999251 / 1000000) ∧
    -Real.log (999251 / 1000000) ≤ (749281 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 1999251)) (n := 12)
    (lo := (4683 / 6250000)) (hi := (749281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999251) = 1/(999251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13702 : Bounds (-749281 / 1000000000) (-4683 / 6250000) (Real.log (999251 / 1000000)) := by
  have h := reflection_log_13702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13703_neg : (13981461 / 40000000) ≤ -Real.log (100000 / 141841) ∧
    -Real.log (100000 / 141841) ≤ (174768263 / 500000000) := by
  have h := checkLog_sound (w := (41841 / 241841)) (n := 12)
    (lo := (13981461 / 40000000)) (hi := (174768263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141841 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141841 / 100000) = 1/(100000 / 141841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13703 : Bounds (13981461 / 40000000) (174768263 / 500000000) (Real.log (141841 / 100000)) := by
  have h := reflection_log_13703_neg
  have he : Real.log (141841 / 100000) = -Real.log (100000 / 141841) := by
    rw [show ((141841 / 100000) : ℝ) = ((100000 / 141841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13704_neg : (270994773 / 500000000) ≤ -Real.log (58159 / 100000) ∧
    -Real.log (58159 / 100000) ≤ (541989547 / 1000000000) := by
  have h := checkLog_sound (w := (41841 / 158159)) (n := 12)
    (lo := (270994773 / 500000000)) (hi := (541989547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 58159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 58159) = 1/(58159 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13704 : Bounds (-541989547 / 1000000000) (-270994773 / 500000000) (Real.log (58159 / 100000)) := by
  have h := reflection_log_13704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13705_neg : (21968893 / 62500000) ≤ -Real.log (1000000 / 1421201) ∧
    -Real.log (1000000 / 1421201) ≤ (351502289 / 1000000000) := by
  have h := checkLog_sound (w := (421201 / 2421201)) (n := 12)
    (lo := (21968893 / 62500000)) (hi := (351502289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421201 / 1000000) = 1/(1000000 / 1421201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13705 : Bounds (21968893 / 62500000) (351502289 / 1000000000) (Real.log (1421201 / 1000000)) := by
  have h := reflection_log_13705_neg
  have he : Real.log (1421201 / 1000000) = -Real.log (1000000 / 1421201) := by
    rw [show ((1421201 / 1000000) : ℝ) = ((1000000 / 1421201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13706_neg : (546800011 / 1000000000) ≤ -Real.log (578799 / 1000000) ∧
    -Real.log (578799 / 1000000) ≤ (136700003 / 250000000) := by
  have h := checkLog_sound (w := (421201 / 1578799)) (n := 12)
    (lo := (546800011 / 1000000000)) (hi := (136700003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 578799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 578799) = 1/(578799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13706 : Bounds (-136700003 / 250000000) (-546800011 / 1000000000) (Real.log (578799 / 1000000)) := by
  have h := reflection_log_13706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13707_neg : (195297723 / 1000000000) ≤ -Real.log (822589717599 / 1000000000000) ∧
    -Real.log (822589717599 / 1000000000000) ≤ (48824431 / 250000000) := by
  have h := checkLog_sound (w := (177410282401 / 1822589717599)) (n := 12)
    (lo := (195297723 / 1000000000)) (hi := (48824431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 822589717599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 822589717599) = 1/(822589717599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13707 : Bounds (-48824431 / 250000000) (-195297723 / 1000000000) (Real.log (822589717599 / 1000000000000)) := by
  have h := reflection_log_13707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13708_neg : (9622651 / 50000000) ≤ -Real.log (8249330719 / 10000000000) ∧
    -Real.log (8249330719 / 10000000000) ≤ (192453021 / 1000000000) := by
  have h := checkLog_sound (w := (1750669281 / 18249330719)) (n := 12)
    (lo := (9622651 / 50000000)) (hi := (192453021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8249330719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8249330719) = 1/(8249330719 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13708 : Bounds (-192453021 / 1000000000) (-9622651 / 50000000) (Real.log (8249330719 / 10000000000)) := by
  have h := reflection_log_13708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13709_neg : (111440759 / 125000000) ≤ -Real.log (125000000000 / 304856084183) ∧
    -Real.log (125000000000 / 304856084183) ≤ (445763037 / 500000000) := by
  have h := checkLog_sound (w := (54856084183 / 554856084183)) (n := 12)
    (lo := (49594723 / 250000000)) (hi := (198378893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304856084183 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(304856084183 / 250000000000) = 1/(125000000000 / 304856084183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13709 : Bounds (111440759 / 125000000) (445763037 / 500000000) (Real.log (304856084183 / 125000000000)) := by
  have h := reflection_log_13709_neg
  have he : Real.log (304856084183 / 125000000000) = -Real.log (125000000000 / 304856084183) := by
    rw [show ((304856084183 / 125000000000) : ℝ) = ((125000000000 / 304856084183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13710_neg : (8983023 / 10000000) ≤ -Real.log (100000000000 / 245543098727) ∧
    -Real.log (100000000000 / 245543098727) ≤ (449151151 / 500000000) := by
  have h := checkLog_sound (w := (45543098727 / 445543098727)) (n := 12)
    (lo := (2564439 / 12500000)) (hi := (205155121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245543098727 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(245543098727 / 200000000000) = 1/(100000000000 / 245543098727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13710 : Bounds (8983023 / 10000000) (449151151 / 500000000) (Real.log (245543098727 / 100000000000)) := by
  have h := reflection_log_13710_neg
  have he : Real.log (245543098727 / 100000000000) = -Real.log (100000000000 / 245543098727) := by
    rw [show ((245543098727 / 100000000000) : ℝ) = ((100000000000 / 245543098727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13711_neg : (481937117 / 250000000) ≤ -Real.log (100000000000 / 687401574803) ∧
    -Real.log (100000000000 / 687401574803) ≤ (1927748471 / 1000000000) := by
  have h := checkLog_sound (w := (287401574803 / 1087401574803)) (n := 12)
    (lo := (135363527 / 250000000)) (hi := (541454109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687401574803 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(687401574803 / 400000000000) = 1/(100000000000 / 687401574803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13711 : Bounds (481937117 / 250000000) (1927748471 / 1000000000) (Real.log (687401574803 / 100000000000)) := by
  have h := reflection_log_13711_neg
  have he : Real.log (687401574803 / 100000000000) = -Real.log (100000000000 / 687401574803) := by
    rw [show ((687401574803 / 100000000000) : ℝ) = ((100000000000 / 687401574803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13712_neg : (970673267 / 500000000) ≤ -Real.log (25000000000 / 174203187251) ∧
    -Real.log (25000000000 / 174203187251) ≤ (1941346537 / 1000000000) := by
  have h := checkLog_sound (w := (74203187251 / 274203187251)) (n := 12)
    (lo := (277526087 / 500000000)) (hi := (22202087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174203187251 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(174203187251 / 100000000000) = 1/(25000000000 / 174203187251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13712 : Bounds (970673267 / 500000000) (1941346537 / 1000000000) (Real.log (174203187251 / 25000000000)) := by
  have h := reflection_log_13712_neg
  have he : Real.log (174203187251 / 25000000000) = -Real.log (25000000000 / 174203187251) := by
    rw [show ((174203187251 / 25000000000) : ℝ) = ((25000000000 / 174203187251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13713_neg : (70094749 / 125000000) ≤ -Real.log (125 / 219) ∧
    -Real.log (125 / 219) ≤ (560757993 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 172)) (n := 12)
    (lo := (70094749 / 125000000)) (hi := (560757993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219 / 125) = 1/(125 / 219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13713 : Bounds (70094749 / 125000000) (560757993 / 1000000000) (Real.log (219 / 125)) := by
  have h := reflection_log_13713_neg
  have he : Real.log (219 / 125) = -Real.log (125 / 219) := by
    rw [show ((219 / 125) : ℝ) = ((125 / 219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13714_neg : (1394326531 / 1000000000) ≤ -Real.log (31 / 125) ∧
    -Real.log (31 / 125) ≤ (697163267 / 500000000) := by
  have h := checkLog_sound (w := (1 / 249)) (n := 12)
    (lo := (8032171 / 1000000000)) (hi := (2008043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 124) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 124) = 1/(31 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13714 : Bounds (-697163267 / 500000000) (-1394326531 / 1000000000) (Real.log (31 / 125)) := by
  have h := reflection_log_13714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13715_neg : (751717 / 1000000000) ≤ -Real.log (62500 / 62547) ∧
    -Real.log (62500 / 62547) ≤ (375859 / 500000000) := by
  have h := checkLog_sound (w := (47 / 125047)) (n := 12)
    (lo := (751717 / 1000000000)) (hi := (375859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62547 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62547 / 62500) = 1/(62500 / 62547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13715 : Bounds (751717 / 1000000000) (375859 / 500000000) (Real.log (62547 / 62500)) := by
  have h := reflection_log_13715_neg
  have he : Real.log (62547 / 62500) = -Real.log (62500 / 62547) := by
    rw [show ((62547 / 62500) : ℝ) = ((62500 / 62547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13716_neg : (376141 / 500000000) ≤ -Real.log (62453 / 62500) ∧
    -Real.log (62453 / 62500) ≤ (752283 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 124953)) (n := 12)
    (lo := (376141 / 500000000)) (hi := (752283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62453) = 1/(62453 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13716 : Bounds (-752283 / 1000000000) (-376141 / 500000000) (Real.log (62453 / 62500)) := by
  have h := reflection_log_13716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13717_neg : (43881307 / 125000000) ≤ -Real.log (1000000 / 1420559) ∧
    -Real.log (1000000 / 1420559) ≤ (351050457 / 1000000000) := by
  have h := checkLog_sound (w := (420559 / 2420559)) (n := 12)
    (lo := (43881307 / 125000000)) (hi := (351050457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1420559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1420559 / 1000000) = 1/(1000000 / 1420559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13717 : Bounds (43881307 / 125000000) (351050457 / 1000000000) (Real.log (1420559 / 1000000)) := by
  have h := reflection_log_13717_neg
  have he : Real.log (1420559 / 1000000) = -Real.log (1000000 / 1420559) := by
    rw [show ((1420559 / 1000000) : ℝ) = ((1000000 / 1420559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13718_neg : (545691433 / 1000000000) ≤ -Real.log (579441 / 1000000) ∧
    -Real.log (579441 / 1000000) ≤ (272845717 / 500000000) := by
  have h := checkLog_sound (w := (420559 / 1579441)) (n := 12)
    (lo := (545691433 / 1000000000)) (hi := (272845717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 579441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 579441) = 1/(579441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13718 : Bounds (-272845717 / 500000000) (-545691433 / 1000000000) (Real.log (579441 / 1000000)) := by
  have h := reflection_log_13718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13719_neg : (353020273 / 1000000000) ≤ -Real.log (3125 / 4448) ∧
    -Real.log (3125 / 4448) ≤ (176510137 / 500000000) := by
  have h := checkLog_sound (w := (1323 / 7573)) (n := 12)
    (lo := (353020273 / 1000000000)) (hi := (176510137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4448 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4448 / 3125) = 1/(3125 / 4448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13719 : Bounds (353020273 / 1000000000) (176510137 / 500000000) (Real.log (4448 / 3125)) := by
  have h := reflection_log_13719_neg
  have he : Real.log (4448 / 3125) = -Real.log (3125 / 4448) := by
    rw [show ((4448 / 3125) : ℝ) = ((3125 / 4448) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13720_neg : (137634281 / 250000000) ≤ -Real.log (1802 / 3125) ∧
    -Real.log (1802 / 3125) ≤ (4404297 / 8000000) := by
  have h := checkLog_sound (w := (1323 / 4927)) (n := 12)
    (lo := (137634281 / 250000000)) (hi := (4404297 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1802) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 1802) = 1/(1802 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13720 : Bounds (-4404297 / 8000000) (-137634281 / 250000000) (Real.log (1802 / 3125)) := by
  have h := reflection_log_13720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13721_neg : (3950337 / 20000000) ≤ -Real.log (8015296 / 9765625) ∧
    -Real.log (8015296 / 9765625) ≤ (197516851 / 1000000000) := by
  have h := checkLog_sound (w := (1750329 / 17780921)) (n := 12)
    (lo := (3950337 / 20000000)) (hi := (197516851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 8015296) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 8015296) = 1/(8015296 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13721 : Bounds (-197516851 / 1000000000) (-3950337 / 20000000) (Real.log (8015296 / 9765625)) := by
  have h := reflection_log_13721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13722_neg : (194640977 / 1000000000) ≤ -Real.log (823130127519 / 1000000000000) ∧
    -Real.log (823130127519 / 1000000000000) ≤ (97320489 / 500000000) := by
  have h := checkLog_sound (w := (176869872481 / 1823130127519)) (n := 12)
    (lo := (194640977 / 1000000000)) (hi := (97320489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 823130127519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 823130127519) = 1/(823130127519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13722 : Bounds (-97320489 / 500000000) (-194640977 / 1000000000) (Real.log (823130127519 / 1000000000000)) := by
  have h := reflection_log_13722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13723_neg : (1751449 / 1953125) ≤ -Real.log (500000000000 / 1225801246373) ∧
    -Real.log (500000000000 / 1225801246373) ≤ (89674189 / 100000000) := by
  have h := checkLog_sound (w := (225801246373 / 2225801246373)) (n := 12)
    (lo := (50898677 / 250000000)) (hi := (203594709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225801246373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1225801246373 / 1000000000000) = 1/(500000000000 / 1225801246373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13723 : Bounds (1751449 / 1953125) (89674189 / 100000000) (Real.log (1225801246373 / 500000000000)) := by
  have h := reflection_log_13723_neg
  have he : Real.log (1225801246373 / 500000000000) = -Real.log (500000000000 / 1225801246373) := by
    rw [show ((1225801246373 / 500000000000) : ℝ) = ((500000000000 / 1225801246373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13724_neg : (903557397 / 1000000000) ≤ -Real.log (250000000000 / 617092119867) ∧
    -Real.log (250000000000 / 617092119867) ≤ (903557399 / 1000000000) := by
  have h := checkLog_sound (w := (117092119867 / 1117092119867)) (n := 12)
    (lo := (210410217 / 1000000000)) (hi := (105205109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617092119867 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(617092119867 / 500000000000) = 1/(250000000000 / 617092119867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13724 : Bounds (903557397 / 1000000000) (903557399 / 1000000000) (Real.log (617092119867 / 250000000000)) := by
  have h := reflection_log_13724_neg
  have he : Real.log (617092119867 / 250000000000) = -Real.log (250000000000 / 617092119867) := by
    rw [show ((617092119867 / 250000000000) : ℝ) = ((250000000000 / 617092119867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13725_neg : (970673267 / 500000000) ≤ -Real.log (500000000000 / 3484063745019) ∧
    -Real.log (500000000000 / 3484063745019) ≤ (1941346537 / 1000000000) := by
  have h := checkLog_sound (w := (1484063745019 / 5484063745019)) (n := 12)
    (lo := (277526087 / 500000000)) (hi := (22202087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3484063745019 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3484063745019 / 2000000000000) = 1/(500000000000 / 3484063745019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13725 : Bounds (970673267 / 500000000) (1941346537 / 1000000000) (Real.log (3484063745019 / 500000000000)) := by
  have h := reflection_log_13725_neg
  have he : Real.log (3484063745019 / 500000000000) = -Real.log (500000000000 / 3484063745019) := by
    rw [show ((3484063745019 / 500000000000) : ℝ) = ((500000000000 / 3484063745019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13726_neg : (488771131 / 250000000) ≤ -Real.log (500000000000 / 3532258064517) ∧
    -Real.log (500000000000 / 3532258064517) ≤ (1955084527 / 1000000000) := by
  have h := checkLog_sound (w := (1532258064517 / 5532258064517)) (n := 12)
    (lo := (142197541 / 250000000)) (hi := (113758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3532258064517 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3532258064517 / 2000000000000) = 1/(500000000000 / 3532258064517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13726 : Bounds (488771131 / 250000000) (1955084527 / 1000000000) (Real.log (3532258064517 / 500000000000)) := by
  have h := reflection_log_13726_neg
  have he : Real.log (3532258064517 / 500000000000) = -Real.log (500000000000 / 3532258064517) := by
    rw [show ((3532258064517 / 500000000000) : ℝ) = ((500000000000 / 3532258064517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13727_neg : (70308607 / 125000000) ≤ -Real.log (200 / 351) ∧
    -Real.log (200 / 351) ≤ (562468857 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 551)) (n := 12)
    (lo := (70308607 / 125000000)) (hi := (562468857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 200) = 1/(200 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13727 : Bounds (70308607 / 125000000) (562468857 / 1000000000) (Real.log (351 / 200)) := by
  have h := reflection_log_13727_neg
  have he : Real.log (351 / 200) = -Real.log (200 / 351) := by
    rw [show ((351 / 200) : ℝ) = ((200 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13728_neg : (1406497067 / 1000000000) ≤ -Real.log (49 / 200) ∧
    -Real.log (49 / 200) ≤ (140649707 / 100000000) := by
  have h := checkLog_sound (w := (1 / 99)) (n := 12)
    (lo := (20202707 / 1000000000)) (hi := (5050677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 49) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 49) = 1/(49 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13728 : Bounds (-140649707 / 100000000) (-1406497067 / 1000000000) (Real.log (49 / 200)) := by
  have h := reflection_log_13728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13729_neg : (150943 / 200000000) ≤ -Real.log (200000 / 200151) ∧
    -Real.log (200000 / 200151) ≤ (188679 / 250000000) := by
  have h := checkLog_sound (w := (151 / 400151)) (n := 12)
    (lo := (150943 / 200000000)) (hi := (188679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200151 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200151 / 200000) = 1/(200000 / 200151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13729 : Bounds (150943 / 200000000) (188679 / 250000000) (Real.log (200151 / 200000)) := by
  have h := reflection_log_13729_neg
  have he : Real.log (200151 / 200000) = -Real.log (200000 / 200151) := by
    rw [show ((200151 / 200000) : ℝ) = ((200000 / 200151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13730_neg : (151057 / 200000000) ≤ -Real.log (199849 / 200000) ∧
    -Real.log (199849 / 200000) ≤ (377643 / 500000000) := by
  have h := checkLog_sound (w := (151 / 399849)) (n := 12)
    (lo := (151057 / 200000000)) (hi := (377643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199849) = 1/(199849 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13730 : Bounds (-377643 / 500000000) (-151057 / 200000000) (Real.log (199849 / 200000)) := by
  have h := reflection_log_13730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13731_neg : (352568423 / 1000000000) ≤ -Real.log (1000000 / 1422717) ∧
    -Real.log (1000000 / 1422717) ≤ (44071053 / 125000000) := by
  have h := checkLog_sound (w := (422717 / 2422717)) (n := 12)
    (lo := (352568423 / 1000000000)) (hi := (44071053 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1422717 / 1000000) = 1/(1000000 / 1422717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13731 : Bounds (352568423 / 1000000000) (44071053 / 125000000) (Real.log (1422717 / 1000000)) := by
  have h := reflection_log_13731_neg
  have he : Real.log (1422717 / 1000000) = -Real.log (1000000 / 1422717) := by
    rw [show ((1422717 / 1000000) : ℝ) = ((1000000 / 1422717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13732_neg : (68677833 / 125000000) ≤ -Real.log (577283 / 1000000) ∧
    -Real.log (577283 / 1000000) ≤ (109884533 / 200000000) := by
  have h := checkLog_sound (w := (422717 / 1577283)) (n := 12)
    (lo := (68677833 / 125000000)) (hi := (109884533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 577283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 577283) = 1/(577283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13732 : Bounds (-109884533 / 200000000) (-68677833 / 125000000) (Real.log (577283 / 1000000)) := by
  have h := reflection_log_13732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13733_neg : (354541569 / 1000000000) ≤ -Real.log (1000000 / 1425527) ∧
    -Real.log (1000000 / 1425527) ≤ (35454157 / 100000000) := by
  have h := checkLog_sound (w := (425527 / 2425527)) (n := 12)
    (lo := (354541569 / 1000000000)) (hi := (35454157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1425527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1425527 / 1000000) = 1/(1000000 / 1425527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13733 : Bounds (354541569 / 1000000000) (35454157 / 100000000) (Real.log (1425527 / 1000000)) := by
  have h := reflection_log_13733_neg
  have he : Real.log (1425527 / 1000000) = -Real.log (1000000 / 1425527) := by
    rw [show ((1425527 / 1000000) : ℝ) = ((1000000 / 1425527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13734_neg : (27715109 / 50000000) ≤ -Real.log (574473 / 1000000) ∧
    -Real.log (574473 / 1000000) ≤ (554302181 / 1000000000) := by
  have h := checkLog_sound (w := (425527 / 1574473)) (n := 12)
    (lo := (27715109 / 50000000)) (hi := (554302181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 574473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 574473) = 1/(574473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13734 : Bounds (-554302181 / 1000000000) (-27715109 / 50000000) (Real.log (574473 / 1000000)) := by
  have h := reflection_log_13734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13735_neg : (19976061 / 100000000) ≤ -Real.log (818926772271 / 1000000000000) ∧
    -Real.log (818926772271 / 1000000000000) ≤ (199760611 / 1000000000) := by
  have h := checkLog_sound (w := (181073227729 / 1818926772271)) (n := 12)
    (lo := (19976061 / 100000000)) (hi := (199760611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 818926772271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 818926772271) = 1/(818926772271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13735 : Bounds (-199760611 / 1000000000) (-19976061 / 100000000) (Real.log (818926772271 / 1000000000000)) := by
  have h := reflection_log_13735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13736_neg : (196854241 / 1000000000) ≤ -Real.log (821310337911 / 1000000000000) ∧
    -Real.log (821310337911 / 1000000000000) ≤ (98427121 / 500000000) := by
  have h := checkLog_sound (w := (178689662089 / 1821310337911)) (n := 12)
    (lo := (196854241 / 1000000000)) (hi := (98427121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 821310337911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 821310337911) = 1/(821310337911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13736 : Bounds (-98427121 / 500000000) (-196854241 / 1000000000) (Real.log (821310337911 / 1000000000000)) := by
  have h := reflection_log_13736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13737_neg : (901991087 / 1000000000) ≤ -Real.log (500000000000 / 1232252638653) ∧
    -Real.log (500000000000 / 1232252638653) ≤ (901991089 / 1000000000) := by
  have h := checkLog_sound (w := (232252638653 / 2232252638653)) (n := 12)
    (lo := (208843907 / 1000000000)) (hi := (52210977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232252638653 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1232252638653 / 1000000000000) = 1/(500000000000 / 1232252638653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13737 : Bounds (901991087 / 1000000000) (901991089 / 1000000000) (Real.log (1232252638653 / 500000000000)) := by
  have h := reflection_log_13737_neg
  have he : Real.log (1232252638653 / 500000000000) = -Real.log (500000000000 / 1232252638653) := by
    rw [show ((1232252638653 / 500000000000) : ℝ) = ((500000000000 / 1232252638653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13738_neg : (908843749 / 1000000000) ≤ -Real.log (100000000000 / 248145169573) ∧
    -Real.log (100000000000 / 248145169573) ≤ (908843751 / 1000000000) := by
  have h := checkLog_sound (w := (48145169573 / 448145169573)) (n := 12)
    (lo := (215696569 / 1000000000)) (hi := (21569657 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248145169573 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(248145169573 / 200000000000) = 1/(100000000000 / 248145169573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13738 : Bounds (908843749 / 1000000000) (908843751 / 1000000000) (Real.log (248145169573 / 100000000000)) := by
  have h := reflection_log_13738_neg
  have he : Real.log (248145169573 / 100000000000) = -Real.log (100000000000 / 248145169573) := by
    rw [show ((248145169573 / 100000000000) : ℝ) = ((100000000000 / 248145169573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13739_neg : (488771131 / 250000000) ≤ -Real.log (125000000000 / 883064516129) ∧
    -Real.log (125000000000 / 883064516129) ≤ (1955084527 / 1000000000) := by
  have h := checkLog_sound (w := (383064516129 / 1383064516129)) (n := 12)
    (lo := (142197541 / 250000000)) (hi := (113758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883064516129 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(883064516129 / 500000000000) = 1/(125000000000 / 883064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13739 : Bounds (488771131 / 250000000) (1955084527 / 1000000000) (Real.log (883064516129 / 125000000000)) := by
  have h := reflection_log_13739_neg
  have he : Real.log (883064516129 / 125000000000) = -Real.log (125000000000 / 883064516129) := by
    rw [show ((883064516129 / 125000000000) : ℝ) = ((125000000000 / 883064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13740_neg : (492241481 / 250000000) ≤ -Real.log (250000000000 / 1790816326531) ∧
    -Real.log (250000000000 / 1790816326531) ≤ (1968965927 / 1000000000) := by
  have h := checkLog_sound (w := (790816326531 / 2790816326531)) (n := 12)
    (lo := (145667891 / 250000000)) (hi := (116534313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1790816326531 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1790816326531 / 1000000000000) = 1/(250000000000 / 1790816326531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13740 : Bounds (492241481 / 250000000) (1968965927 / 1000000000) (Real.log (1790816326531 / 250000000000)) := by
  have h := reflection_log_13740_neg
  have he : Real.log (1790816326531 / 250000000000) = -Real.log (250000000000 / 1790816326531) := by
    rw [show ((1790816326531 / 250000000000) : ℝ) = ((250000000000 / 1790816326531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13741_neg : (564176799 / 1000000000) ≤ -Real.log (500 / 879) ∧
    -Real.log (500 / 879) ≤ (705221 / 1250000) := by
  have h := checkLog_sound (w := (379 / 1379)) (n := 12)
    (lo := (564176799 / 1000000000)) (hi := (705221 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879 / 500) = 1/(500 / 879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13741 : Bounds (564176799 / 1000000000) (705221 / 1250000) (Real.log (879 / 500)) := by
  have h := reflection_log_13741_neg
  have he : Real.log (879 / 500) = -Real.log (500 / 879) := by
    rw [show ((879 / 500) : ℝ) = ((500 / 879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13742_neg : (1418817551 / 1000000000) ≤ -Real.log (121 / 500) ∧
    -Real.log (121 / 500) ≤ (709408777 / 500000000) := by
  have h := checkLog_sound (w := (2 / 123)) (n := 12)
    (lo := (32523191 / 1000000000)) (hi := (4065399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 121) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 121) = 1/(121 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13742 : Bounds (-709408777 / 500000000) (-1418817551 / 1000000000) (Real.log (121 / 500)) := by
  have h := reflection_log_13742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13743_neg : (47357 / 62500000) ≤ -Real.log (500000 / 500379) ∧
    -Real.log (500000 / 500379) ≤ (757713 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1000379)) (n := 12)
    (lo := (47357 / 62500000)) (hi := (757713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500379 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500379 / 500000) = 1/(500000 / 500379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13743 : Bounds (47357 / 62500000) (757713 / 1000000000) (Real.log (500379 / 500000)) := by
  have h := reflection_log_13743_neg
  have he : Real.log (500379 / 500000) = -Real.log (500000 / 500379) := by
    rw [show ((500379 / 500000) : ℝ) = ((500000 / 500379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13744_neg : (758287 / 1000000000) ≤ -Real.log (499621 / 500000) ∧
    -Real.log (499621 / 500000) ≤ (47393 / 62500000) := by
  have h := checkLog_sound (w := (379 / 999621)) (n := 12)
    (lo := (758287 / 1000000000)) (hi := (47393 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499621) = 1/(499621 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13744 : Bounds (-47393 / 62500000) (-758287 / 1000000000) (Real.log (499621 / 500000)) := by
  have h := reflection_log_13744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13745_neg : (354089003 / 1000000000) ≤ -Real.log (500000 / 712441) ∧
    -Real.log (500000 / 712441) ≤ (88522251 / 250000000) := by
  have h := checkLog_sound (w := (212441 / 1212441)) (n := 12)
    (lo := (354089003 / 1000000000)) (hi := (88522251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712441 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712441 / 500000) = 1/(500000 / 712441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13745 : Bounds (354089003 / 1000000000) (88522251 / 250000000) (Real.log (712441 / 500000)) := by
  have h := reflection_log_13745_neg
  have he : Real.log (712441 / 500000) = -Real.log (500000 / 712441) := by
    rw [show ((712441 / 500000) : ℝ) = ((500000 / 712441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13746_neg : (553180041 / 1000000000) ≤ -Real.log (287559 / 500000) ∧
    -Real.log (287559 / 500000) ≤ (276590021 / 500000000) := by
  have h := checkLog_sound (w := (212441 / 787559)) (n := 12)
    (lo := (553180041 / 1000000000)) (hi := (276590021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287559) = 1/(287559 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13746 : Bounds (-276590021 / 500000000) (-553180041 / 1000000000) (Real.log (287559 / 500000)) := by
  have h := reflection_log_13746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13747_neg : (178033079 / 500000000) ≤ -Real.log (500000 / 713851) ∧
    -Real.log (500000 / 713851) ≤ (356066159 / 1000000000) := by
  have h := checkLog_sound (w := (213851 / 1213851)) (n := 12)
    (lo := (178033079 / 500000000)) (hi := (356066159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713851 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713851 / 500000) = 1/(500000 / 713851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13747 : Bounds (178033079 / 500000000) (356066159 / 1000000000) (Real.log (713851 / 500000)) := by
  have h := reflection_log_13747_neg
  have he : Real.log (713851 / 500000) = -Real.log (500000 / 713851) := by
    rw [show ((713851 / 500000) : ℝ) = ((500000 / 713851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13748_neg : (139523861 / 250000000) ≤ -Real.log (286149 / 500000) ∧
    -Real.log (286149 / 500000) ≤ (111619089 / 200000000) := by
  have h := checkLog_sound (w := (213851 / 786149)) (n := 12)
    (lo := (139523861 / 250000000)) (hi := (111619089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 286149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 286149) = 1/(286149 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13748 : Bounds (-111619089 / 200000000) (-139523861 / 250000000) (Real.log (286149 / 500000)) := by
  have h := reflection_log_13748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13749_neg : (40405857 / 200000000) ≤ -Real.log (204267749799 / 250000000000) ∧
    -Real.log (204267749799 / 250000000000) ≤ (101014643 / 500000000) := by
  have h := checkLog_sound (w := (45732250201 / 454267749799)) (n := 12)
    (lo := (40405857 / 200000000)) (hi := (101014643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 204267749799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 204267749799) = 1/(204267749799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13749 : Bounds (-101014643 / 500000000) (-40405857 / 200000000) (Real.log (204267749799 / 250000000000)) := by
  have h := reflection_log_13749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13750_neg : (99545519 / 500000000) ≤ -Real.log (204868821519 / 250000000000) ∧
    -Real.log (204868821519 / 250000000000) ≤ (199091039 / 1000000000) := by
  have h := checkLog_sound (w := (45131178481 / 454868821519)) (n := 12)
    (lo := (99545519 / 500000000)) (hi := (199091039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 204868821519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 204868821519) = 1/(204868821519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13750 : Bounds (-199091039 / 1000000000) (-99545519 / 500000000) (Real.log (204868821519 / 250000000000)) := by
  have h := reflection_log_13750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13751_neg : (226817261 / 250000000) ≤ -Real.log (250000000000 / 619386804099) ∧
    -Real.log (250000000000 / 619386804099) ≤ (453634523 / 500000000) := by
  have h := checkLog_sound (w := (119386804099 / 1119386804099)) (n := 12)
    (lo := (26765233 / 125000000)) (hi := (42824373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619386804099 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(619386804099 / 500000000000) = 1/(250000000000 / 619386804099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13751 : Bounds (226817261 / 250000000) (453634523 / 500000000) (Real.log (619386804099 / 250000000000)) := by
  have h := reflection_log_13751_neg
  have he : Real.log (619386804099 / 250000000000) = -Real.log (250000000000 / 619386804099) := by
    rw [show ((619386804099 / 250000000000) : ℝ) = ((250000000000 / 619386804099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13752_neg : (457080801 / 500000000) ≤ -Real.log (50000000000 / 124734142003) ∧
    -Real.log (50000000000 / 124734142003) ≤ (228540401 / 250000000) := by
  have h := checkLog_sound (w := (24734142003 / 224734142003)) (n := 12)
    (lo := (110507211 / 500000000)) (hi := (221014423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124734142003 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(124734142003 / 100000000000) = 1/(50000000000 / 124734142003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13752 : Bounds (457080801 / 500000000) (228540401 / 250000000) (Real.log (124734142003 / 50000000000)) := by
  have h := reflection_log_13752_neg
  have he : Real.log (124734142003 / 50000000000) = -Real.log (50000000000 / 124734142003) := by
    rw [show ((124734142003 / 50000000000) : ℝ) = ((50000000000 / 124734142003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13753_neg : (492241481 / 250000000) ≤ -Real.log (500000000000 / 3581632653061) ∧
    -Real.log (500000000000 / 3581632653061) ≤ (1968965927 / 1000000000) := by
  have h := checkLog_sound (w := (1581632653061 / 5581632653061)) (n := 12)
    (lo := (145667891 / 250000000)) (hi := (116534313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3581632653061 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3581632653061 / 2000000000000) = 1/(500000000000 / 3581632653061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13753 : Bounds (492241481 / 250000000) (1968965927 / 1000000000) (Real.log (3581632653061 / 500000000000)) := by
  have h := reflection_log_13753_neg
  have he : Real.log (3581632653061 / 500000000000) = -Real.log (500000000000 / 3581632653061) := by
    rw [show ((3581632653061 / 500000000000) : ℝ) = ((500000000000 / 3581632653061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13754_neg : (39659887 / 20000000) ≤ -Real.log (500000000000 / 3632231404959) ∧
    -Real.log (500000000000 / 3632231404959) ≤ (1982994353 / 1000000000) := by
  have h := checkLog_sound (w := (1632231404959 / 5632231404959)) (n := 12)
    (lo := (59669999 / 100000000)) (hi := (596699991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3632231404959 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3632231404959 / 2000000000000) = 1/(500000000000 / 3632231404959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13754 : Bounds (39659887 / 20000000) (1982994353 / 1000000000) (Real.log (3632231404959 / 500000000000)) := by
  have h := reflection_log_13754_neg
  have he : Real.log (3632231404959 / 500000000000) = -Real.log (500000000000 / 3632231404959) := by
    rw [show ((3632231404959 / 500000000000) : ℝ) = ((500000000000 / 3632231404959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13755_neg : (565881829 / 1000000000) ≤ -Real.log (1000 / 1761) ∧
    -Real.log (1000 / 1761) ≤ (56588183 / 100000000) := by
  have h := checkLog_sound (w := (761 / 2761)) (n := 12)
    (lo := (565881829 / 1000000000)) (hi := (56588183 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1000) = 1/(1000 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13755 : Bounds (565881829 / 1000000000) (56588183 / 100000000) (Real.log (1761 / 1000)) := by
  have h := reflection_log_13755_neg
  have he : Real.log (1761 / 1000) = -Real.log (1000 / 1761) := by
    rw [show ((1761 / 1000) : ℝ) = ((1000 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13756_neg : (57251669 / 40000000) ≤ -Real.log (239 / 1000) ∧
    -Real.log (239 / 1000) ≤ (89455733 / 62500000) := by
  have h := checkLog_sound (w := (11 / 489)) (n := 12)
    (lo := (8999473 / 200000000)) (hi := (22498683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 239) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 239) = 1/(239 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13756 : Bounds (-89455733 / 62500000) (-57251669 / 40000000) (Real.log (239 / 1000)) := by
  have h := reflection_log_13756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13757_neg : (76071 / 100000000) ≤ -Real.log (1000000 / 1000761) ∧
    -Real.log (1000000 / 1000761) ≤ (760711 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 2000761)) (n := 12)
    (lo := (76071 / 100000000)) (hi := (760711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000761 / 1000000) = 1/(1000000 / 1000761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13757 : Bounds (76071 / 100000000) (760711 / 1000000000) (Real.log (1000761 / 1000000)) := by
  have h := reflection_log_13757_neg
  have he : Real.log (1000761 / 1000000) = -Real.log (1000000 / 1000761) := by
    rw [show ((1000761 / 1000000) : ℝ) = ((1000000 / 1000761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13758_neg : (761289 / 1000000000) ≤ -Real.log (999239 / 1000000) ∧
    -Real.log (999239 / 1000000) ≤ (76129 / 100000000) := by
  have h := checkLog_sound (w := (761 / 1999239)) (n := 12)
    (lo := (761289 / 1000000000)) (hi := (76129 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999239) = 1/(999239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13758 : Bounds (-76129 / 100000000) (-761289 / 1000000000) (Real.log (999239 / 1000000)) := by
  have h := reflection_log_13758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13759_neg : (17780679 / 50000000) ≤ -Real.log (62500 / 89191) ∧
    -Real.log (62500 / 89191) ≤ (355613581 / 1000000000) := by
  have h := checkLog_sound (w := (26691 / 151691)) (n := 12)
    (lo := (17780679 / 50000000)) (hi := (355613581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89191 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89191 / 62500) = 1/(62500 / 89191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13759 : Bounds (17780679 / 50000000) (355613581 / 1000000000) (Real.log (89191 / 62500)) := by
  have h := reflection_log_13759_neg
  have he : Real.log (89191 / 62500) = -Real.log (62500 / 89191) := by
    rw [show ((89191 / 62500) : ℝ) = ((62500 / 89191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0215 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13760_neg : (278483649 / 500000000) ≤ -Real.log (35809 / 62500) ∧
    -Real.log (35809 / 62500) ≤ (556967299 / 1000000000) := by
  have h := checkLog_sound (w := (26691 / 98309)) (n := 12)
    (lo := (278483649 / 500000000)) (hi := (556967299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35809) = 1/(35809 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13760 : Bounds (-556967299 / 1000000000) (-278483649 / 500000000) (Real.log (35809 / 62500)) := by
  have h := reflection_log_13760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13761_neg : (357594021 / 1000000000) ≤ -Real.log (200000 / 285977) ∧
    -Real.log (200000 / 285977) ≤ (178797011 / 500000000) := by
  have h := checkLog_sound (w := (85977 / 485977)) (n := 12)
    (lo := (357594021 / 1000000000)) (hi := (178797011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285977 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285977 / 200000) = 1/(200000 / 285977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13761 : Bounds (357594021 / 1000000000) (178797011 / 500000000) (Real.log (285977 / 200000)) := by
  have h := reflection_log_13761_neg
  have he : Real.log (285977 / 200000) = -Real.log (200000 / 285977) := by
    rw [show ((285977 / 200000) : ℝ) = ((200000 / 285977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13762_neg : (2194989 / 3906250) ≤ -Real.log (114023 / 200000) ∧
    -Real.log (114023 / 200000) ≤ (112383437 / 200000000) := by
  have h := checkLog_sound (w := (85977 / 314023)) (n := 12)
    (lo := (2194989 / 3906250)) (hi := (112383437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 114023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 114023) = 1/(114023 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13762 : Bounds (-112383437 / 200000000) (-2194989 / 3906250) (Real.log (114023 / 200000)) := by
  have h := reflection_log_13762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13763_neg : (102161581 / 500000000) ≤ -Real.log (32607955471 / 40000000000) ∧
    -Real.log (32607955471 / 40000000000) ≤ (204323163 / 1000000000) := by
  have h := checkLog_sound (w := (7392044529 / 72607955471)) (n := 12)
    (lo := (102161581 / 500000000)) (hi := (204323163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 32607955471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 32607955471) = 1/(32607955471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13763 : Bounds (-204323163 / 1000000000) (-102161581 / 500000000) (Real.log (32607955471 / 40000000000)) := by
  have h := reflection_log_13763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13764_neg : (201353717 / 1000000000) ≤ -Real.log (3193840519 / 3906250000) ∧
    -Real.log (3193840519 / 3906250000) ≤ (100676859 / 500000000) := by
  have h := checkLog_sound (w := (712409481 / 7100090519)) (n := 12)
    (lo := (201353717 / 1000000000)) (hi := (100676859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3193840519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3193840519) = 1/(3193840519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13764 : Bounds (-100676859 / 500000000) (-201353717 / 1000000000) (Real.log (3193840519 / 3906250000)) := by
  have h := reflection_log_13764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13765_neg : (456290439 / 500000000) ≤ -Real.log (500000000000 / 1245371275377) ∧
    -Real.log (500000000000 / 1245371275377) ≤ (11407261 / 12500000) := by
  have h := checkLog_sound (w := (245371275377 / 2245371275377)) (n := 12)
    (lo := (109716849 / 500000000)) (hi := (219433699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245371275377 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1245371275377 / 1000000000000) = 1/(500000000000 / 1245371275377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13765 : Bounds (456290439 / 500000000) (11407261 / 12500000) (Real.log (1245371275377 / 500000000000)) := by
  have h := reflection_log_13765_neg
  have he : Real.log (1245371275377 / 500000000000) = -Real.log (500000000000 / 1245371275377) := by
    rw [show ((1245371275377 / 500000000000) : ℝ) = ((500000000000 / 1245371275377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13766_neg : (183902241 / 200000000) ≤ -Real.log (500000000000 / 1254032081247) ∧
    -Real.log (500000000000 / 1254032081247) ≤ (919511207 / 1000000000) := by
  have h := checkLog_sound (w := (254032081247 / 2254032081247)) (n := 12)
    (lo := (9054561 / 40000000)) (hi := (113182013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254032081247 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1254032081247 / 1000000000000) = 1/(500000000000 / 1254032081247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13766 : Bounds (183902241 / 200000000) (919511207 / 1000000000) (Real.log (1254032081247 / 500000000000)) := by
  have h := reflection_log_13766_neg
  have he : Real.log (1254032081247 / 500000000000) = -Real.log (500000000000 / 1254032081247) := by
    rw [show ((1254032081247 / 500000000000) : ℝ) = ((500000000000 / 1254032081247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13767_neg : (39659887 / 20000000) ≤ -Real.log (250000000000 / 1816115702479) ∧
    -Real.log (250000000000 / 1816115702479) ≤ (1982994353 / 1000000000) := by
  have h := checkLog_sound (w := (816115702479 / 2816115702479)) (n := 12)
    (lo := (59669999 / 100000000)) (hi := (596699991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1816115702479 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1816115702479 / 1000000000000) = 1/(250000000000 / 1816115702479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13767 : Bounds (39659887 / 20000000) (1982994353 / 1000000000) (Real.log (1816115702479 / 250000000000)) := by
  have h := reflection_log_13767_neg
  have he : Real.log (1816115702479 / 250000000000) = -Real.log (250000000000 / 1816115702479) := by
    rw [show ((1816115702479 / 250000000000) : ℝ) = ((250000000000 / 1816115702479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13768_neg : (399434711 / 200000000) ≤ -Real.log (500000000000 / 3684100418411) ∧
    -Real.log (500000000000 / 3684100418411) ≤ (998586779 / 500000000) := by
  have h := checkLog_sound (w := (1684100418411 / 5684100418411)) (n := 12)
    (lo := (122175839 / 200000000)) (hi := (152719799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3684100418411 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3684100418411 / 2000000000000) = 1/(500000000000 / 3684100418411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13768 : Bounds (399434711 / 200000000) (998586779 / 500000000) (Real.log (3684100418411 / 500000000000)) := by
  have h := reflection_log_13768_neg
  have he : Real.log (3684100418411 / 500000000000) = -Real.log (500000000000 / 3684100418411) := by
    rw [show ((3684100418411 / 500000000000) : ℝ) = ((500000000000 / 3684100418411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13769_neg : (567583957 / 1000000000) ≤ -Real.log (250 / 441) ∧
    -Real.log (250 / 441) ≤ (283791979 / 500000000) := by
  have h := checkLog_sound (w := (191 / 691)) (n := 12)
    (lo := (567583957 / 1000000000)) (hi := (283791979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 250) = 1/(250 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13769 : Bounds (567583957 / 1000000000) (283791979 / 500000000) (Real.log (441 / 250)) := by
  have h := reflection_log_13769_neg
  have he : Real.log (441 / 250) = -Real.log (250 / 441) := by
    rw [show ((441 / 250) : ℝ) = ((250 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13770_neg : (90245217 / 62500000) ≤ -Real.log (59 / 250) ∧
    -Real.log (59 / 250) ≤ (57756939 / 40000000) := by
  have h := checkLog_sound (w := (7 / 243)) (n := 12)
    (lo := (7203639 / 125000000)) (hi := (57629113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 118) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 118) = 1/(59 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13770 : Bounds (-57756939 / 40000000) (-90245217 / 62500000) (Real.log (59 / 250)) := by
  have h := reflection_log_13770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13771_neg : (190927 / 250000000) ≤ -Real.log (250000 / 250191) ∧
    -Real.log (250000 / 250191) ≤ (763709 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 500191)) (n := 12)
    (lo := (190927 / 250000000)) (hi := (763709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250191 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250191 / 250000) = 1/(250000 / 250191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13771 : Bounds (190927 / 250000000) (763709 / 1000000000) (Real.log (250191 / 250000)) := by
  have h := reflection_log_13771_neg
  have he : Real.log (250191 / 250000) = -Real.log (250000 / 250191) := by
    rw [show ((250191 / 250000) : ℝ) = ((250000 / 250191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13772_neg : (764291 / 1000000000) ≤ -Real.log (249809 / 250000) ∧
    -Real.log (249809 / 250000) ≤ (191073 / 250000000) := by
  have h := checkLog_sound (w := (191 / 499809)) (n := 12)
    (lo := (764291 / 1000000000)) (hi := (191073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249809) = 1/(249809 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13772 : Bounds (-191073 / 250000000) (-764291 / 1000000000) (Real.log (249809 / 250000)) := by
  have h := reflection_log_13772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13773_neg : (71428287 / 200000000) ≤ -Real.log (500000 / 714619) ∧
    -Real.log (500000 / 714619) ≤ (89285359 / 250000000) := by
  have h := checkLog_sound (w := (214619 / 1214619)) (n := 12)
    (lo := (71428287 / 200000000)) (hi := (89285359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714619 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714619 / 500000) = 1/(500000 / 714619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13773 : Bounds (71428287 / 200000000) (89285359 / 250000000) (Real.log (714619 / 500000)) := by
  have h := reflection_log_13773_neg
  have he : Real.log (714619 / 500000) = -Real.log (500000 / 714619) := by
    rw [show ((714619 / 500000) : ℝ) = ((500000 / 714619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13774_neg : (70097871 / 125000000) ≤ -Real.log (285381 / 500000) ∧
    -Real.log (285381 / 500000) ≤ (560782969 / 1000000000) := by
  have h := checkLog_sound (w := (214619 / 785381)) (n := 12)
    (lo := (70097871 / 125000000)) (hi := (560782969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 285381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 285381) = 1/(285381 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13774 : Bounds (-560782969 / 1000000000) (-70097871 / 125000000) (Real.log (285381 / 500000)) := by
  have h := reflection_log_13774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13775_neg : (359125139 / 1000000000) ≤ -Real.log (250000 / 358019) ∧
    -Real.log (250000 / 358019) ≤ (17956257 / 50000000) := by
  have h := checkLog_sound (w := (108019 / 608019)) (n := 12)
    (lo := (359125139 / 1000000000)) (hi := (17956257 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358019 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358019 / 250000) = 1/(250000 / 358019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13775 : Bounds (359125139 / 1000000000) (17956257 / 50000000) (Real.log (358019 / 250000)) := by
  have h := reflection_log_13775_neg
  have he : Real.log (358019 / 250000) = -Real.log (250000 / 358019) := by
    rw [show ((358019 / 250000) : ℝ) = ((250000 / 358019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13776_neg : (70720959 / 125000000) ≤ -Real.log (141981 / 250000) ∧
    -Real.log (141981 / 250000) ≤ (565767673 / 1000000000) := by
  have h := checkLog_sound (w := (108019 / 391981)) (n := 12)
    (lo := (70720959 / 125000000)) (hi := (565767673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 141981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 141981) = 1/(141981 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13776 : Bounds (-565767673 / 1000000000) (-70720959 / 125000000) (Real.log (141981 / 250000)) := by
  have h := reflection_log_13776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13777_neg : (51660633 / 250000000) ≤ -Real.log (50831895639 / 62500000000) ∧
    -Real.log (50831895639 / 62500000000) ≤ (206642533 / 1000000000) := by
  have h := checkLog_sound (w := (11668104361 / 113331895639)) (n := 12)
    (lo := (51660633 / 250000000)) (hi := (206642533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50831895639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50831895639) = 1/(50831895639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13777 : Bounds (-206642533 / 1000000000) (-51660633 / 250000000) (Real.log (50831895639 / 62500000000)) := by
  have h := reflection_log_13777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13778_neg : (203641533 / 1000000000) ≤ -Real.log (203938684839 / 250000000000) ∧
    -Real.log (203938684839 / 250000000000) ≤ (101820767 / 500000000) := by
  have h := checkLog_sound (w := (46061315161 / 453938684839)) (n := 12)
    (lo := (203641533 / 1000000000)) (hi := (101820767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 203938684839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 203938684839) = 1/(203938684839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13778 : Bounds (-101820767 / 500000000) (-203641533 / 1000000000) (Real.log (203938684839 / 250000000000)) := by
  have h := reflection_log_13778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13779_neg : (917924403 / 1000000000) ≤ -Real.log (125000000000 / 313010939761) ∧
    -Real.log (125000000000 / 313010939761) ≤ (183584881 / 200000000) := by
  have h := checkLog_sound (w := (63010939761 / 563010939761)) (n := 12)
    (lo := (224777223 / 1000000000)) (hi := (28097153 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313010939761 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(313010939761 / 250000000000) = 1/(125000000000 / 313010939761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13779 : Bounds (917924403 / 1000000000) (183584881 / 200000000) (Real.log (313010939761 / 125000000000)) := by
  have h := reflection_log_13779_neg
  have he : Real.log (313010939761 / 125000000000) = -Real.log (125000000000 / 313010939761) := by
    rw [show ((313010939761 / 125000000000) : ℝ) = ((125000000000 / 313010939761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13780_neg : (924892811 / 1000000000) ≤ -Real.log (250000000000 / 630399490073) ∧
    -Real.log (250000000000 / 630399490073) ≤ (924892813 / 1000000000) := by
  have h := checkLog_sound (w := (130399490073 / 1130399490073)) (n := 12)
    (lo := (231745631 / 1000000000)) (hi := (7242051 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630399490073 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(630399490073 / 500000000000) = 1/(250000000000 / 630399490073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13780 : Bounds (924892811 / 1000000000) (924892813 / 1000000000) (Real.log (630399490073 / 250000000000)) := by
  have h := reflection_log_13780_neg
  have he : Real.log (630399490073 / 250000000000) = -Real.log (250000000000 / 630399490073) := by
    rw [show ((630399490073 / 250000000000) : ℝ) = ((250000000000 / 630399490073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13781_neg : (399434711 / 200000000) ≤ -Real.log (50000000000 / 368410041841) ∧
    -Real.log (50000000000 / 368410041841) ≤ (998586779 / 500000000) := by
  have h := checkLog_sound (w := (168410041841 / 568410041841)) (n := 12)
    (lo := (122175839 / 200000000)) (hi := (152719799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368410041841 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(368410041841 / 200000000000) = 1/(50000000000 / 368410041841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13781 : Bounds (399434711 / 200000000) (998586779 / 500000000) (Real.log (368410041841 / 50000000000)) := by
  have h := reflection_log_13781_neg
  have he : Real.log (368410041841 / 50000000000) = -Real.log (50000000000 / 368410041841) := by
    rw [show ((368410041841 / 50000000000) : ℝ) = ((50000000000 / 368410041841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13782_neg : (201150743 / 100000000) ≤ -Real.log (250000000000 / 1868644067797) ∧
    -Real.log (250000000000 / 1868644067797) ≤ (2011507433 / 1000000000) := by
  have h := checkLog_sound (w := (868644067797 / 2868644067797)) (n := 12)
    (lo := (62521307 / 100000000)) (hi := (625213071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1868644067797 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1868644067797 / 1000000000000) = 1/(250000000000 / 1868644067797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13782 : Bounds (201150743 / 100000000) (2011507433 / 1000000000) (Real.log (1868644067797 / 250000000000)) := by
  have h := reflection_log_13782_neg
  have he : Real.log (1868644067797 / 250000000000) = -Real.log (250000000000 / 1868644067797) := by
    rw [show ((1868644067797 / 250000000000) : ℝ) = ((250000000000 / 1868644067797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13783_neg : (569283193 / 1000000000) ≤ -Real.log (1000 / 1767) ∧
    -Real.log (1000 / 1767) ≤ (284641597 / 500000000) := by
  have h := checkLog_sound (w := (767 / 2767)) (n := 12)
    (lo := (569283193 / 1000000000)) (hi := (284641597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1767 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1767 / 1000) = 1/(1000 / 1767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13783 : Bounds (569283193 / 1000000000) (284641597 / 500000000) (Real.log (1767 / 1000)) := by
  have h := reflection_log_13783_neg
  have he : Real.log (1767 / 1000) = -Real.log (1000 / 1767) := by
    rw [show ((1767 / 1000) : ℝ) = ((1000 / 1767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13784_neg : (182089603 / 125000000) ≤ -Real.log (233 / 1000) ∧
    -Real.log (233 / 1000) ≤ (1456716827 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 483)) (n := 12)
    (lo := (1100351 / 15625000)) (hi := (14084493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 233) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 233) = 1/(233 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13784 : Bounds (-1456716827 / 1000000000) (-182089603 / 125000000) (Real.log (233 / 1000)) := by
  have h := reflection_log_13784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13785_neg : (383353 / 500000000) ≤ -Real.log (1000000 / 1000767) ∧
    -Real.log (1000000 / 1000767) ≤ (766707 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 2000767)) (n := 12)
    (lo := (383353 / 500000000)) (hi := (766707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000767 / 1000000) = 1/(1000000 / 1000767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13785 : Bounds (383353 / 500000000) (766707 / 1000000000) (Real.log (1000767 / 1000000)) := by
  have h := reflection_log_13785_neg
  have he : Real.log (1000767 / 1000000) = -Real.log (1000000 / 1000767) := by
    rw [show ((1000767 / 1000000) : ℝ) = ((1000000 / 1000767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13786_neg : (383647 / 500000000) ≤ -Real.log (999233 / 1000000) ∧
    -Real.log (999233 / 1000000) ≤ (153459 / 200000000) := by
  have h := checkLog_sound (w := (767 / 1999233)) (n := 12)
    (lo := (383647 / 500000000)) (hi := (153459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999233) = 1/(999233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13786 : Bounds (-153459 / 200000000) (-383647 / 500000000) (Real.log (999233 / 1000000)) := by
  have h := reflection_log_13786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13787_neg : (358672547 / 1000000000) ≤ -Real.log (250000 / 357857) ∧
    -Real.log (250000 / 357857) ≤ (89668137 / 250000000) := by
  have h := checkLog_sound (w := (107857 / 607857)) (n := 12)
    (lo := (358672547 / 1000000000)) (hi := (89668137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357857 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357857 / 250000) = 1/(250000 / 357857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13787 : Bounds (358672547 / 1000000000) (89668137 / 250000000) (Real.log (357857 / 250000)) := by
  have h := reflection_log_13787_neg
  have he : Real.log (357857 / 250000) = -Real.log (250000 / 357857) := by
    rw [show ((357857 / 250000) : ℝ) = ((250000 / 357857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13788_neg : (141156831 / 250000000) ≤ -Real.log (142143 / 250000) ∧
    -Real.log (142143 / 250000) ≤ (22585093 / 40000000) := by
  have h := checkLog_sound (w := (107857 / 392143)) (n := 12)
    (lo := (141156831 / 250000000)) (hi := (22585093 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 142143) = 1/(142143 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13788 : Bounds (-22585093 / 40000000) (-141156831 / 250000000) (Real.log (142143 / 250000)) := by
  have h := reflection_log_13788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13789_neg : (11270631 / 31250000) ≤ -Real.log (250000 / 358569) ∧
    -Real.log (250000 / 358569) ≤ (360660193 / 1000000000) := by
  have h := checkLog_sound (w := (108569 / 608569)) (n := 12)
    (lo := (11270631 / 31250000)) (hi := (360660193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358569 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358569 / 250000) = 1/(250000 / 358569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13789 : Bounds (11270631 / 31250000) (360660193 / 1000000000) (Real.log (358569 / 250000)) := by
  have h := reflection_log_13789_neg
  have he : Real.log (358569 / 250000) = -Real.log (250000 / 358569) := by
    rw [show ((358569 / 250000) : ℝ) = ((250000 / 358569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13790_neg : (71206119 / 125000000) ≤ -Real.log (141431 / 250000) ∧
    -Real.log (141431 / 250000) ≤ (569648953 / 1000000000) := by
  have h := checkLog_sound (w := (108569 / 391431)) (n := 12)
    (lo := (71206119 / 125000000)) (hi := (569648953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 141431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 141431) = 1/(141431 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13790 : Bounds (-569648953 / 1000000000) (-71206119 / 125000000) (Real.log (141431 / 250000)) := by
  have h := reflection_log_13790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13791_neg : (208988759 / 1000000000) ≤ -Real.log (50712772239 / 62500000000) ∧
    -Real.log (50712772239 / 62500000000) ≤ (5224719 / 25000000) := by
  have h := checkLog_sound (w := (11787227761 / 113212772239)) (n := 12)
    (lo := (208988759 / 1000000000)) (hi := (5224719 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50712772239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50712772239) = 1/(50712772239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13791 : Bounds (-5224719 / 25000000) (-208988759 / 1000000000) (Real.log (50712772239 / 62500000000)) := by
  have h := reflection_log_13791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13792_neg : (205954777 / 1000000000) ≤ -Real.log (50866867551 / 62500000000) ∧
    -Real.log (50866867551 / 62500000000) ≤ (102977389 / 500000000) := by
  have h := checkLog_sound (w := (11633132449 / 113366867551)) (n := 12)
    (lo := (205954777 / 1000000000)) (hi := (102977389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50866867551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50866867551) = 1/(50866867551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13792 : Bounds (-102977389 / 500000000) (-205954777 / 1000000000) (Real.log (50866867551 / 62500000000)) := by
  have h := reflection_log_13792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13793_neg : (923299871 / 1000000000) ≤ -Real.log (250000000000 / 629396101109) ∧
    -Real.log (250000000000 / 629396101109) ≤ (923299873 / 1000000000) := by
  have h := checkLog_sound (w := (129396101109 / 1129396101109)) (n := 12)
    (lo := (230152691 / 1000000000)) (hi := (57538173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629396101109 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629396101109 / 500000000000) = 1/(250000000000 / 629396101109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13793 : Bounds (923299871 / 1000000000) (923299873 / 1000000000) (Real.log (629396101109 / 250000000000)) := by
  have h := reflection_log_13793_neg
  have he : Real.log (629396101109 / 250000000000) = -Real.log (250000000000 / 629396101109) := by
    rw [show ((629396101109 / 250000000000) : ℝ) = ((250000000000 / 629396101109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13794_neg : (930309143 / 1000000000) ≤ -Real.log (500000000000 / 1267646414153) ∧
    -Real.log (500000000000 / 1267646414153) ≤ (186061829 / 200000000) := by
  have h := checkLog_sound (w := (267646414153 / 2267646414153)) (n := 12)
    (lo := (237161963 / 1000000000)) (hi := (59290491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267646414153 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1267646414153 / 1000000000000) = 1/(500000000000 / 1267646414153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13794 : Bounds (930309143 / 1000000000) (186061829 / 200000000) (Real.log (1267646414153 / 500000000000)) := by
  have h := reflection_log_13794_neg
  have he : Real.log (1267646414153 / 500000000000) = -Real.log (500000000000 / 1267646414153) := by
    rw [show ((1267646414153 / 500000000000) : ℝ) = ((500000000000 / 1267646414153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13795_neg : (201150743 / 100000000) ≤ -Real.log (500000000000 / 3737288135593) ∧
    -Real.log (500000000000 / 3737288135593) ≤ (2011507433 / 1000000000) := by
  have h := checkLog_sound (w := (1737288135593 / 5737288135593)) (n := 12)
    (lo := (62521307 / 100000000)) (hi := (625213071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3737288135593 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3737288135593 / 2000000000000) = 1/(500000000000 / 3737288135593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13795 : Bounds (201150743 / 100000000) (2011507433 / 1000000000) (Real.log (3737288135593 / 500000000000)) := by
  have h := reflection_log_13795_neg
  have he : Real.log (3737288135593 / 500000000000) = -Real.log (500000000000 / 3737288135593) := by
    rw [show ((3737288135593 / 500000000000) : ℝ) = ((500000000000 / 3737288135593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13796_neg : (2026000017 / 1000000000) ≤ -Real.log (500000000000 / 3791845493563) ∧
    -Real.log (500000000000 / 3791845493563) ≤ (101300001 / 50000000) := by
  have h := checkLog_sound (w := (1791845493563 / 5791845493563)) (n := 12)
    (lo := (639705657 / 1000000000)) (hi := (319852829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3791845493563 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3791845493563 / 2000000000000) = 1/(500000000000 / 3791845493563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13796 : Bounds (2026000017 / 1000000000) (101300001 / 50000000) (Real.log (3791845493563 / 500000000000)) := by
  have h := reflection_log_13796_neg
  have he : Real.log (3791845493563 / 500000000000) = -Real.log (500000000000 / 3791845493563) := by
    rw [show ((3791845493563 / 500000000000) : ℝ) = ((500000000000 / 3791845493563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13797_neg : (285489773 / 500000000) ≤ -Real.log (100 / 177) ∧
    -Real.log (100 / 177) ≤ (570979547 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 277)) (n := 12)
    (lo := (285489773 / 500000000)) (hi := (570979547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 100) = 1/(100 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13797 : Bounds (285489773 / 500000000) (570979547 / 1000000000) (Real.log (177 / 100)) := by
  have h := reflection_log_13797_neg
  have he : Real.log (177 / 100) = -Real.log (100 / 177) := by
    rw [show ((177 / 100) : ℝ) = ((100 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13798_neg : (22963687 / 15625000) ≤ -Real.log (23 / 100) ∧
    -Real.log (23 / 100) ≤ (1469675971 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 23) = 1/(23 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13798 : Bounds (-1469675971 / 1000000000) (-22963687 / 15625000) (Real.log (23 / 100)) := by
  have h := reflection_log_13798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13799_neg : (769703 / 1000000000) ≤ -Real.log (100000 / 100077) ∧
    -Real.log (100000 / 100077) ≤ (96213 / 125000000) := by
  have h := checkLog_sound (w := (77 / 200077)) (n := 12)
    (lo := (769703 / 1000000000)) (hi := (96213 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100077 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100077 / 100000) = 1/(100000 / 100077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13799 : Bounds (769703 / 1000000000) (96213 / 125000000) (Real.log (100077 / 100000)) := by
  have h := reflection_log_13799_neg
  have he : Real.log (100077 / 100000) = -Real.log (100000 / 100077) := by
    rw [show ((100077 / 100000) : ℝ) = ((100000 / 100077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13800_neg : (96287 / 125000000) ≤ -Real.log (99923 / 100000) ∧
    -Real.log (99923 / 100000) ≤ (770297 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 199923)) (n := 12)
    (lo := (96287 / 125000000)) (hi := (770297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99923) = 1/(99923 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13800 : Bounds (-770297 / 1000000000) (-96287 / 125000000) (Real.log (99923 / 100000)) := by
  have h := reflection_log_13800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13801_neg : (90051899 / 250000000) ≤ -Real.log (1000000 / 1433627) ∧
    -Real.log (1000000 / 1433627) ≤ (360207597 / 1000000000) := by
  have h := checkLog_sound (w := (433627 / 2433627)) (n := 12)
    (lo := (90051899 / 250000000)) (hi := (360207597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433627 / 1000000) = 1/(1000000 / 1433627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13801 : Bounds (90051899 / 250000000) (360207597 / 1000000000) (Real.log (1433627 / 1000000)) := by
  have h := reflection_log_13801_neg
  have he : Real.log (1433627 / 1000000) = -Real.log (1000000 / 1433627) := by
    rw [show ((1433627 / 1000000) : ℝ) = ((1000000 / 1433627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13802_neg : (568502407 / 1000000000) ≤ -Real.log (566373 / 1000000) ∧
    -Real.log (566373 / 1000000) ≤ (71062801 / 125000000) := by
  have h := checkLog_sound (w := (433627 / 1566373)) (n := 12)
    (lo := (568502407 / 1000000000)) (hi := (71062801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 566373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 566373) = 1/(566373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13802 : Bounds (-71062801 / 125000000) (-568502407 / 1000000000) (Real.log (566373 / 1000000)) := by
  have h := reflection_log_13802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13803_neg : (362199157 / 1000000000) ≤ -Real.log (200000 / 287297) ∧
    -Real.log (200000 / 287297) ≤ (181099579 / 500000000) := by
  have h := checkLog_sound (w := (87297 / 487297)) (n := 12)
    (lo := (362199157 / 1000000000)) (hi := (181099579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287297 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287297 / 200000) = 1/(200000 / 287297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13803 : Bounds (362199157 / 1000000000) (181099579 / 500000000) (Real.log (287297 / 200000)) := by
  have h := reflection_log_13803_neg
  have he : Real.log (287297 / 200000) = -Real.log (200000 / 287297) := by
    rw [show ((287297 / 200000) : ℝ) = ((200000 / 287297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13804_neg : (286780663 / 500000000) ≤ -Real.log (112703 / 200000) ∧
    -Real.log (112703 / 200000) ≤ (573561327 / 1000000000) := by
  have h := checkLog_sound (w := (87297 / 312703)) (n := 12)
    (lo := (286780663 / 500000000)) (hi := (573561327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 112703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 112703) = 1/(112703 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13804 : Bounds (-573561327 / 1000000000) (-286780663 / 500000000) (Real.log (112703 / 200000)) := by
  have h := reflection_log_13804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13805_neg : (211362169 / 1000000000) ≤ -Real.log (32379233791 / 40000000000) ∧
    -Real.log (32379233791 / 40000000000) ≤ (21136217 / 100000000) := by
  have h := checkLog_sound (w := (7620766209 / 72379233791)) (n := 12)
    (lo := (211362169 / 1000000000)) (hi := (21136217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 32379233791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 32379233791) = 1/(32379233791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13805 : Bounds (-21136217 / 100000000) (-211362169 / 1000000000) (Real.log (32379233791 / 40000000000)) := by
  have h := reflection_log_13805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13806_neg : (20829481 / 100000000) ≤ -Real.log (811967624871 / 1000000000000) ∧
    -Real.log (811967624871 / 1000000000000) ≤ (208294811 / 1000000000) := by
  have h := checkLog_sound (w := (188032375129 / 1811967624871)) (n := 12)
    (lo := (20829481 / 100000000)) (hi := (208294811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 811967624871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 811967624871) = 1/(811967624871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13806 : Bounds (-208294811 / 1000000000) (-20829481 / 100000000) (Real.log (811967624871 / 1000000000000)) := by
  have h := reflection_log_13806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13807_neg : (928710003 / 1000000000) ≤ -Real.log (500000000000 / 1265620889413) ∧
    -Real.log (500000000000 / 1265620889413) ≤ (185742001 / 200000000) := by
  have h := checkLog_sound (w := (265620889413 / 2265620889413)) (n := 12)
    (lo := (235562823 / 1000000000)) (hi := (29445353 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265620889413 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1265620889413 / 1000000000000) = 1/(500000000000 / 1265620889413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13807 : Bounds (928710003 / 1000000000) (185742001 / 200000000) (Real.log (1265620889413 / 500000000000)) := by
  have h := reflection_log_13807_neg
  have he : Real.log (1265620889413 / 500000000000) = -Real.log (500000000000 / 1265620889413) := by
    rw [show ((1265620889413 / 500000000000) : ℝ) = ((500000000000 / 1265620889413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13808_neg : (935760483 / 1000000000) ≤ -Real.log (500000000000 / 1274575654597) ∧
    -Real.log (500000000000 / 1274575654597) ≤ (187152097 / 200000000) := by
  have h := checkLog_sound (w := (274575654597 / 2274575654597)) (n := 12)
    (lo := (242613303 / 1000000000)) (hi := (30326663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274575654597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1274575654597 / 1000000000000) = 1/(500000000000 / 1274575654597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13808 : Bounds (935760483 / 1000000000) (187152097 / 200000000) (Real.log (1274575654597 / 500000000000)) := by
  have h := reflection_log_13808_neg
  have he : Real.log (1274575654597 / 500000000000) = -Real.log (500000000000 / 1274575654597) := by
    rw [show ((1274575654597 / 500000000000) : ℝ) = ((500000000000 / 1274575654597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13809_neg : (2026000017 / 1000000000) ≤ -Real.log (250000000000 / 1895922746781) ∧
    -Real.log (250000000000 / 1895922746781) ≤ (101300001 / 50000000) := by
  have h := checkLog_sound (w := (895922746781 / 2895922746781)) (n := 12)
    (lo := (639705657 / 1000000000)) (hi := (319852829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1895922746781 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1895922746781 / 1000000000000) = 1/(250000000000 / 1895922746781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13809 : Bounds (2026000017 / 1000000000) (101300001 / 50000000) (Real.log (1895922746781 / 250000000000)) := by
  have h := reflection_log_13809_neg
  have he : Real.log (1895922746781 / 250000000000) = -Real.log (250000000000 / 1895922746781) := by
    rw [show ((1895922746781 / 250000000000) : ℝ) = ((250000000000 / 1895922746781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13810_neg : (408131103 / 200000000) ≤ -Real.log (500000000000 / 3847826086957) ∧
    -Real.log (500000000000 / 3847826086957) ≤ (1020327759 / 500000000) := by
  have h := checkLog_sound (w := (1847826086957 / 5847826086957)) (n := 12)
    (lo := (130872231 / 200000000)) (hi := (163590289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3847826086957 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3847826086957 / 2000000000000) = 1/(500000000000 / 3847826086957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13810 : Bounds (408131103 / 200000000) (1020327759 / 500000000) (Real.log (3847826086957 / 500000000000)) := by
  have h := reflection_log_13810_neg
  have he : Real.log (3847826086957 / 500000000000) = -Real.log (500000000000 / 3847826086957) := by
    rw [show ((3847826086957 / 500000000000) : ℝ) = ((500000000000 / 3847826086957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13811_neg : (572673027 / 1000000000) ≤ -Real.log (1000 / 1773) ∧
    -Real.log (1000 / 1773) ≤ (143168257 / 250000000) := by
  have h := checkLog_sound (w := (773 / 2773)) (n := 12)
    (lo := (572673027 / 1000000000)) (hi := (143168257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773 / 1000) = 1/(1000 / 1773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13811 : Bounds (572673027 / 1000000000) (143168257 / 250000000) (Real.log (1773 / 1000)) := by
  have h := reflection_log_13811_neg
  have he : Real.log (1773 / 1000) = -Real.log (1000 / 1773) := by
    rw [show ((1773 / 1000) : ℝ) = ((1000 / 1773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13812_neg : (74140263 / 50000000) ≤ -Real.log (227 / 1000) ∧
    -Real.log (227 / 1000) ≤ (1482805263 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 477)) (n := 12)
    (lo := (965109 / 10000000)) (hi := (96510901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 227) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 227) = 1/(227 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13812 : Bounds (-1482805263 / 1000000000) (-74140263 / 50000000) (Real.log (227 / 1000)) := by
  have h := reflection_log_13812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13813_neg : (772701 / 1000000000) ≤ -Real.log (1000000 / 1000773) ∧
    -Real.log (1000000 / 1000773) ≤ (386351 / 500000000) := by
  have h := checkLog_sound (w := (773 / 2000773)) (n := 12)
    (lo := (772701 / 1000000000)) (hi := (386351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000773 / 1000000) = 1/(1000000 / 1000773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13813 : Bounds (772701 / 1000000000) (386351 / 500000000) (Real.log (1000773 / 1000000)) := by
  have h := reflection_log_13813_neg
  have he : Real.log (1000773 / 1000000) = -Real.log (1000000 / 1000773) := by
    rw [show ((1000773 / 1000000) : ℝ) = ((1000000 / 1000773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13814_neg : (386649 / 500000000) ≤ -Real.log (999227 / 1000000) ∧
    -Real.log (999227 / 1000000) ≤ (773299 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 1999227)) (n := 12)
    (lo := (386649 / 500000000)) (hi := (773299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999227) = 1/(999227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13814 : Bounds (-773299 / 1000000000) (-386649 / 500000000) (Real.log (999227 / 1000000)) := by
  have h := reflection_log_13814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13815_neg : (72349173 / 200000000) ≤ -Real.log (500000 / 717917) ∧
    -Real.log (500000 / 717917) ≤ (180872933 / 500000000) := by
  have h := checkLog_sound (w := (217917 / 1217917)) (n := 12)
    (lo := (72349173 / 200000000)) (hi := (180872933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717917 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717917 / 500000) = 1/(500000 / 717917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13815 : Bounds (72349173 / 200000000) (180872933 / 500000000) (Real.log (717917 / 500000)) := by
  have h := reflection_log_13815_neg
  have he : Real.log (717917 / 500000) = -Real.log (500000 / 717917) := by
    rw [show ((717917 / 500000) : ℝ) = ((500000 / 717917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13816_neg : (71550843 / 125000000) ≤ -Real.log (282083 / 500000) ∧
    -Real.log (282083 / 500000) ≤ (114481349 / 200000000) := by
  have h := checkLog_sound (w := (217917 / 782083)) (n := 12)
    (lo := (71550843 / 125000000)) (hi := (114481349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 282083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 282083) = 1/(282083 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13816 : Bounds (-114481349 / 200000000) (-71550843 / 125000000) (Real.log (282083 / 500000)) := by
  have h := reflection_log_13816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13817_neg : (181870659 / 500000000) ≤ -Real.log (500000 / 719351) ∧
    -Real.log (500000 / 719351) ≤ (363741319 / 1000000000) := by
  have h := checkLog_sound (w := (219351 / 1219351)) (n := 12)
    (lo := (181870659 / 500000000)) (hi := (363741319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719351 / 500000) = 1/(500000 / 719351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13817 : Bounds (181870659 / 500000000) (363741319 / 1000000000) (Real.log (719351 / 500000)) := by
  have h := reflection_log_13817_neg
  have he : Real.log (719351 / 500000) = -Real.log (500000 / 719351) := by
    rw [show ((719351 / 500000) : ℝ) = ((500000 / 719351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13818_neg : (14437583 / 25000000) ≤ -Real.log (280649 / 500000) ∧
    -Real.log (280649 / 500000) ≤ (577503321 / 1000000000) := by
  have h := checkLog_sound (w := (219351 / 780649)) (n := 12)
    (lo := (14437583 / 25000000)) (hi := (577503321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 280649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 280649) = 1/(280649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13818 : Bounds (-577503321 / 1000000000) (-14437583 / 25000000) (Real.log (280649 / 500000)) := by
  have h := reflection_log_13818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13819_neg : (213762001 / 1000000000) ≤ -Real.log (201885138799 / 250000000000) ∧
    -Real.log (201885138799 / 250000000000) ≤ (106881001 / 500000000) := by
  have h := checkLog_sound (w := (48114861201 / 451885138799)) (n := 12)
    (lo := (213762001 / 1000000000)) (hi := (106881001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 201885138799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 201885138799) = 1/(201885138799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13819 : Bounds (-106881001 / 500000000) (-213762001 / 1000000000) (Real.log (201885138799 / 250000000000)) := by
  have h := reflection_log_13819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13820_neg : (210660879 / 1000000000) ≤ -Real.log (202512181111 / 250000000000) ∧
    -Real.log (202512181111 / 250000000000) ≤ (2633261 / 12500000) := by
  have h := checkLog_sound (w := (47487818889 / 452512181111)) (n := 12)
    (lo := (210660879 / 1000000000)) (hi := (2633261 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 202512181111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 202512181111) = 1/(202512181111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13820 : Bounds (-2633261 / 12500000) (-210660879 / 1000000000) (Real.log (202512181111 / 250000000000)) := by
  have h := reflection_log_13820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13821_neg : (934152609 / 1000000000) ≤ -Real.log (500000000000 / 1272527943903) ∧
    -Real.log (500000000000 / 1272527943903) ≤ (934152611 / 1000000000) := by
  have h := checkLog_sound (w := (272527943903 / 2272527943903)) (n := 12)
    (lo := (241005429 / 1000000000)) (hi := (24100543 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272527943903 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1272527943903 / 1000000000000) = 1/(500000000000 / 1272527943903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13821 : Bounds (934152609 / 1000000000) (934152611 / 1000000000) (Real.log (1272527943903 / 500000000000)) := by
  have h := reflection_log_13821_neg
  have he : Real.log (1272527943903 / 500000000000) = -Real.log (500000000000 / 1272527943903) := by
    rw [show ((1272527943903 / 500000000000) : ℝ) = ((500000000000 / 1272527943903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13822_neg : (941244637 / 1000000000) ≤ -Real.log (500000000000 / 1281584826599) ∧
    -Real.log (500000000000 / 1281584826599) ≤ (941244639 / 1000000000) := by
  have h := checkLog_sound (w := (281584826599 / 2281584826599)) (n := 12)
    (lo := (248097457 / 1000000000)) (hi := (124048729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281584826599 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1281584826599 / 1000000000000) = 1/(500000000000 / 1281584826599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13822 : Bounds (941244637 / 1000000000) (941244639 / 1000000000) (Real.log (1281584826599 / 500000000000)) := by
  have h := reflection_log_13822_neg
  have he : Real.log (1281584826599 / 500000000000) = -Real.log (500000000000 / 1281584826599) := by
    rw [show ((1281584826599 / 500000000000) : ℝ) = ((500000000000 / 1281584826599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13823_neg : (408131103 / 200000000) ≤ -Real.log (125000000000 / 961956521739) ∧
    -Real.log (125000000000 / 961956521739) ≤ (1020327759 / 500000000) := by
  have h := checkLog_sound (w := (461956521739 / 1461956521739)) (n := 12)
    (lo := (130872231 / 200000000)) (hi := (163590289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961956521739 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(961956521739 / 500000000000) = 1/(125000000000 / 961956521739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13823 : Bounds (408131103 / 200000000) (1020327759 / 500000000) (Real.log (961956521739 / 125000000000)) := by
  have h := reflection_log_13823_neg
  have he : Real.log (961956521739 / 125000000000) = -Real.log (125000000000 / 961956521739) := by
    rw [show ((961956521739 / 125000000000) : ℝ) = ((125000000000 / 961956521739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0216 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13824_neg : (2055478287 / 1000000000) ≤ -Real.log (500000000000 / 3905286343613) ∧
    -Real.log (500000000000 / 3905286343613) ≤ (205547829 / 100000000) := by
  have h := checkLog_sound (w := (1905286343613 / 5905286343613)) (n := 12)
    (lo := (669183927 / 1000000000)) (hi := (83647991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3905286343613 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3905286343613 / 2000000000000) = 1/(500000000000 / 3905286343613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13824 : Bounds (2055478287 / 1000000000) (205547829 / 100000000) (Real.log (3905286343613 / 500000000000)) := by
  have h := reflection_log_13824_neg
  have he : Real.log (3905286343613 / 500000000000) = -Real.log (500000000000 / 3905286343613) := by
    rw [show ((3905286343613 / 500000000000) : ℝ) = ((500000000000 / 3905286343613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13825_neg : (143590911 / 250000000) ≤ -Real.log (125 / 222) ∧
    -Real.log (125 / 222) ≤ (114872729 / 200000000) := by
  have h := checkLog_sound (w := (97 / 347)) (n := 12)
    (lo := (143590911 / 250000000)) (hi := (114872729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222 / 125) = 1/(125 / 222) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13825 : Bounds (143590911 / 250000000) (114872729 / 200000000) (Real.log (222 / 125)) := by
  have h := reflection_log_13825_neg
  have he : Real.log (222 / 125) = -Real.log (125 / 222) := by
    rw [show ((222 / 125) : ℝ) = ((125 / 222) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13826_neg : (748054613 / 500000000) ≤ -Real.log (28 / 125) ∧
    -Real.log (28 / 125) ≤ (1496109229 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 112) = 1/(28 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13826 : Bounds (-1496109229 / 1000000000) (-748054613 / 500000000) (Real.log (28 / 125)) := by
  have h := reflection_log_13826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13827_neg : (775699 / 1000000000) ≤ -Real.log (125000 / 125097) ∧
    -Real.log (125000 / 125097) ≤ (7757 / 10000000) := by
  have h := checkLog_sound (w := (97 / 250097)) (n := 12)
    (lo := (775699 / 1000000000)) (hi := (7757 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125097 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125097 / 125000) = 1/(125000 / 125097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13827 : Bounds (775699 / 1000000000) (7757 / 10000000) (Real.log (125097 / 125000)) := by
  have h := reflection_log_13827_neg
  have he : Real.log (125097 / 125000) = -Real.log (125000 / 125097) := by
    rw [show ((125097 / 125000) : ℝ) = ((125000 / 125097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13828_neg : (776301 / 1000000000) ≤ -Real.log (124903 / 125000) ∧
    -Real.log (124903 / 125000) ≤ (388151 / 500000000) := by
  have h := checkLog_sound (w := (97 / 249903)) (n := 12)
    (lo := (776301 / 1000000000)) (hi := (388151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124903) = 1/(124903 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13828 : Bounds (-388151 / 500000000) (-776301 / 1000000000) (Real.log (124903 / 125000)) := by
  have h := reflection_log_13828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13829_neg : (363288029 / 1000000000) ≤ -Real.log (20000 / 28761) ∧
    -Real.log (20000 / 28761) ≤ (36328803 / 100000000) := by
  have h := checkLog_sound (w := (8761 / 48761)) (n := 12)
    (lo := (363288029 / 1000000000)) (hi := (36328803 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28761 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28761 / 20000) = 1/(20000 / 28761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13829 : Bounds (363288029 / 1000000000) (36328803 / 100000000) (Real.log (28761 / 20000)) := by
  have h := reflection_log_13829_neg
  have he : Real.log (28761 / 20000) = -Real.log (20000 / 28761) := by
    rw [show ((28761 / 20000) : ℝ) = ((20000 / 28761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13830_neg : (576342401 / 1000000000) ≤ -Real.log (11239 / 20000) ∧
    -Real.log (11239 / 20000) ≤ (288171201 / 500000000) := by
  have h := checkLog_sound (w := (8761 / 31239)) (n := 12)
    (lo := (576342401 / 1000000000)) (hi := (288171201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 11239) = 1/(11239 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13830 : Bounds (-288171201 / 500000000) (-576342401 / 1000000000) (Real.log (11239 / 20000)) := by
  have h := reflection_log_13830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13831_neg : (91322011 / 250000000) ≤ -Real.log (1000000 / 1440929) ∧
    -Real.log (1000000 / 1440929) ≤ (73057609 / 200000000) := by
  have h := checkLog_sound (w := (440929 / 2440929)) (n := 12)
    (lo := (91322011 / 250000000)) (hi := (73057609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1440929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1440929 / 1000000) = 1/(1000000 / 1440929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13831 : Bounds (91322011 / 250000000) (73057609 / 200000000) (Real.log (1440929 / 1000000)) := by
  have h := reflection_log_13831_neg
  have he : Real.log (1440929 / 1000000) = -Real.log (1000000 / 1440929) := by
    rw [show ((1440929 / 1000000) : ℝ) = ((1000000 / 1440929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13832_neg : (581478801 / 1000000000) ≤ -Real.log (559071 / 1000000) ∧
    -Real.log (559071 / 1000000) ≤ (290739401 / 500000000) := by
  have h := checkLog_sound (w := (440929 / 1559071)) (n := 12)
    (lo := (581478801 / 1000000000)) (hi := (290739401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 559071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 559071) = 1/(559071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13832 : Bounds (-290739401 / 500000000) (-581478801 / 1000000000) (Real.log (559071 / 1000000)) := by
  have h := reflection_log_13832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13833_neg : (54047689 / 250000000) ≤ -Real.log (805581616959 / 1000000000000) ∧
    -Real.log (805581616959 / 1000000000000) ≤ (216190757 / 1000000000) := by
  have h := checkLog_sound (w := (194418383041 / 1805581616959)) (n := 12)
    (lo := (54047689 / 250000000)) (hi := (216190757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 805581616959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 805581616959) = 1/(805581616959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13833 : Bounds (-216190757 / 1000000000) (-54047689 / 250000000) (Real.log (805581616959 / 1000000000000)) := by
  have h := reflection_log_13833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13834_neg : (213054371 / 1000000000) ≤ -Real.log (323244879 / 400000000) ∧
    -Real.log (323244879 / 400000000) ≤ (53263593 / 250000000) := by
  have h := checkLog_sound (w := (76755121 / 723244879)) (n := 12)
    (lo := (213054371 / 1000000000)) (hi := (53263593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 323244879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 323244879) = 1/(323244879 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13834 : Bounds (-53263593 / 250000000) (-213054371 / 1000000000) (Real.log (323244879 / 400000000)) := by
  have h := reflection_log_13834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13835_neg : (939630429 / 1000000000) ≤ -Real.log (500000000000 / 1279517750689) ∧
    -Real.log (500000000000 / 1279517750689) ≤ (939630431 / 1000000000) := by
  have h := checkLog_sound (w := (279517750689 / 2279517750689)) (n := 12)
    (lo := (246483249 / 1000000000)) (hi := (985933 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279517750689 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1279517750689 / 1000000000000) = 1/(500000000000 / 1279517750689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13835 : Bounds (939630429 / 1000000000) (939630431 / 1000000000) (Real.log (1279517750689 / 500000000000)) := by
  have h := reflection_log_13835_neg
  have he : Real.log (1279517750689 / 500000000000) = -Real.log (500000000000 / 1279517750689) := by
    rw [show ((1279517750689 / 500000000000) : ℝ) = ((500000000000 / 1279517750689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13836_neg : (189353369 / 200000000) ≤ -Real.log (250000000000 / 644340790347) ∧
    -Real.log (250000000000 / 644340790347) ≤ (946766847 / 1000000000) := by
  have h := checkLog_sound (w := (144340790347 / 1144340790347)) (n := 12)
    (lo := (50723933 / 200000000)) (hi := (126809833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644340790347 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(644340790347 / 500000000000) = 1/(250000000000 / 644340790347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13836 : Bounds (189353369 / 200000000) (946766847 / 1000000000) (Real.log (644340790347 / 250000000000)) := by
  have h := reflection_log_13836_neg
  have he : Real.log (644340790347 / 250000000000) = -Real.log (250000000000 / 644340790347) := by
    rw [show ((644340790347 / 250000000000) : ℝ) = ((250000000000 / 644340790347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13837_neg : (2055478287 / 1000000000) ≤ -Real.log (125000000000 / 976321585903) ∧
    -Real.log (125000000000 / 976321585903) ≤ (205547829 / 100000000) := by
  have h := checkLog_sound (w := (476321585903 / 1476321585903)) (n := 12)
    (lo := (669183927 / 1000000000)) (hi := (83647991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976321585903 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(976321585903 / 500000000000) = 1/(125000000000 / 976321585903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13837 : Bounds (2055478287 / 1000000000) (205547829 / 100000000) (Real.log (976321585903 / 125000000000)) := by
  have h := reflection_log_13837_neg
  have he : Real.log (976321585903 / 125000000000) = -Real.log (125000000000 / 976321585903) := by
    rw [show ((976321585903 / 125000000000) : ℝ) = ((125000000000 / 976321585903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13838_neg : (207047287 / 100000000) ≤ -Real.log (250000000000 / 1982142857143) ∧
    -Real.log (250000000000 / 1982142857143) ≤ (2070472873 / 1000000000) := by
  have h := checkLog_sound (w := (982142857143 / 2982142857143)) (n := 12)
    (lo := (68417851 / 100000000)) (hi := (684178511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982142857143 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1982142857143 / 1000000000000) = 1/(250000000000 / 1982142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13838 : Bounds (207047287 / 100000000) (2070472873 / 1000000000) (Real.log (1982142857143 / 250000000000)) := by
  have h := reflection_log_13838_neg
  have he : Real.log (1982142857143 / 250000000000) = -Real.log (250000000000 / 1982142857143) := by
    rw [show ((1982142857143 / 250000000000) : ℝ) = ((250000000000 / 1982142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13839_neg : (36003213 / 62500000) ≤ -Real.log (1000 / 1779) ∧
    -Real.log (1000 / 1779) ≤ (576051409 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 2779)) (n := 12)
    (lo := (36003213 / 62500000)) (hi := (576051409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779 / 1000) = 1/(1000 / 1779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13839 : Bounds (36003213 / 62500000) (576051409 / 1000000000) (Real.log (1779 / 1000)) := by
  have h := reflection_log_13839_neg
  have he : Real.log (1779 / 1000) = -Real.log (1000 / 1779) := by
    rw [show ((1779 / 1000) : ℝ) = ((1000 / 1779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13840_neg : (2948423 / 1953125) ≤ -Real.log (221 / 1000) ∧
    -Real.log (221 / 1000) ≤ (1509592579 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 471)) (n := 12)
    (lo := (15412277 / 125000000)) (hi := (123298217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 221) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 221) = 1/(221 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13840 : Bounds (-1509592579 / 1000000000) (-2948423 / 1953125) (Real.log (221 / 1000)) := by
  have h := reflection_log_13840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13841_neg : (97337 / 125000000) ≤ -Real.log (1000000 / 1000779) ∧
    -Real.log (1000000 / 1000779) ≤ (778697 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 2000779)) (n := 12)
    (lo := (97337 / 125000000)) (hi := (778697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000779 / 1000000) = 1/(1000000 / 1000779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13841 : Bounds (97337 / 125000000) (778697 / 1000000000) (Real.log (1000779 / 1000000)) := by
  have h := reflection_log_13841_neg
  have he : Real.log (1000779 / 1000000) = -Real.log (1000000 / 1000779) := by
    rw [show ((1000779 / 1000000) : ℝ) = ((1000000 / 1000779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13842_neg : (779303 / 1000000000) ≤ -Real.log (999221 / 1000000) ∧
    -Real.log (999221 / 1000000) ≤ (97413 / 125000000) := by
  have h := checkLog_sound (w := (779 / 1999221)) (n := 12)
    (lo := (779303 / 1000000000)) (hi := (97413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999221) = 1/(999221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13842 : Bounds (-97413 / 125000000) (-779303 / 1000000000) (Real.log (999221 / 1000000)) := by
  have h := reflection_log_13842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13843_neg : (364834761 / 1000000000) ≤ -Real.log (250000 / 360069) ∧
    -Real.log (250000 / 360069) ≤ (182417381 / 500000000) := by
  have h := checkLog_sound (w := (110069 / 610069)) (n := 12)
    (lo := (364834761 / 1000000000)) (hi := (182417381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360069 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360069 / 250000) = 1/(250000 / 360069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13843 : Bounds (364834761 / 1000000000) (182417381 / 500000000) (Real.log (360069 / 250000)) := by
  have h := reflection_log_13843_neg
  have he : Real.log (360069 / 250000) = -Real.log (250000 / 360069) := by
    rw [show ((360069 / 250000) : ℝ) = ((250000 / 360069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13844_neg : (580311473 / 1000000000) ≤ -Real.log (139931 / 250000) ∧
    -Real.log (139931 / 250000) ≤ (290155737 / 500000000) := by
  have h := checkLog_sound (w := (110069 / 389931)) (n := 12)
    (lo := (580311473 / 1000000000)) (hi := (290155737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 139931) = 1/(139931 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13844 : Bounds (-290155737 / 500000000) (-580311473 / 1000000000) (Real.log (139931 / 250000)) := by
  have h := reflection_log_13844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13845_neg : (14673517 / 40000000) ≤ -Real.log (250000 / 360791) ∧
    -Real.log (250000 / 360791) ≤ (183418963 / 500000000) := by
  have h := checkLog_sound (w := (110791 / 610791)) (n := 12)
    (lo := (14673517 / 40000000)) (hi := (183418963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360791 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360791 / 250000) = 1/(250000 / 360791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13845 : Bounds (14673517 / 40000000) (183418963 / 500000000) (Real.log (360791 / 250000)) := by
  have h := reflection_log_13845_neg
  have he : Real.log (360791 / 250000) = -Real.log (250000 / 360791) := by
    rw [show ((360791 / 250000) : ℝ) = ((250000 / 360791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13846_neg : (146371129 / 250000000) ≤ -Real.log (139209 / 250000) ∧
    -Real.log (139209 / 250000) ≤ (585484517 / 1000000000) := by
  have h := checkLog_sound (w := (110791 / 389209)) (n := 12)
    (lo := (146371129 / 250000000)) (hi := (585484517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 139209) = 1/(139209 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13846 : Bounds (-585484517 / 1000000000) (-146371129 / 250000000) (Real.log (139209 / 250000)) := by
  have h := reflection_log_13846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13847_neg : (218646591 / 1000000000) ≤ -Real.log (50225354319 / 62500000000) ∧
    -Real.log (50225354319 / 62500000000) ≤ (3416353 / 15625000) := by
  have h := checkLog_sound (w := (12274645681 / 112725354319)) (n := 12)
    (lo := (218646591 / 1000000000)) (hi := (3416353 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50225354319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50225354319) = 1/(50225354319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13847 : Bounds (-3416353 / 15625000) (-218646591 / 1000000000) (Real.log (50225354319 / 62500000000)) := by
  have h := reflection_log_13847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13848_neg : (26934589 / 125000000) ≤ -Real.log (50384815239 / 62500000000) ∧
    -Real.log (50384815239 / 62500000000) ≤ (215476713 / 1000000000) := by
  have h := checkLog_sound (w := (12115184761 / 112884815239)) (n := 12)
    (lo := (26934589 / 125000000)) (hi := (215476713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 50384815239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 50384815239) = 1/(50384815239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13848 : Bounds (-215476713 / 1000000000) (-26934589 / 125000000) (Real.log (50384815239 / 62500000000)) := by
  have h := reflection_log_13848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13849_neg : (189029247 / 200000000) ≤ -Real.log (500000000000 / 1286594821733) ∧
    -Real.log (500000000000 / 1286594821733) ≤ (945146237 / 1000000000) := by
  have h := checkLog_sound (w := (286594821733 / 2286594821733)) (n := 12)
    (lo := (50399811 / 200000000)) (hi := (15749941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286594821733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1286594821733 / 1000000000000) = 1/(500000000000 / 1286594821733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13849 : Bounds (189029247 / 200000000) (945146237 / 1000000000) (Real.log (1286594821733 / 500000000000)) := by
  have h := reflection_log_13849_neg
  have he : Real.log (1286594821733 / 500000000000) = -Real.log (500000000000 / 1286594821733) := by
    rw [show ((1286594821733 / 500000000000) : ℝ) = ((500000000000 / 1286594821733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13850_neg : (952322441 / 1000000000) ≤ -Real.log (500000000000 / 1295860899799) ∧
    -Real.log (500000000000 / 1295860899799) ≤ (952322443 / 1000000000) := by
  have h := checkLog_sound (w := (295860899799 / 2295860899799)) (n := 12)
    (lo := (259175261 / 1000000000)) (hi := (129587631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295860899799 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1295860899799 / 1000000000000) = 1/(500000000000 / 1295860899799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13850 : Bounds (952322441 / 1000000000) (952322443 / 1000000000) (Real.log (1295860899799 / 500000000000)) := by
  have h := reflection_log_13850_neg
  have he : Real.log (1295860899799 / 500000000000) = -Real.log (500000000000 / 1295860899799) := by
    rw [show ((1295860899799 / 500000000000) : ℝ) = ((500000000000 / 1295860899799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13851_neg : (207047287 / 100000000) ≤ -Real.log (100000000000 / 792857142857) ∧
    -Real.log (100000000000 / 792857142857) ≤ (2070472873 / 1000000000) := by
  have h := checkLog_sound (w := (392857142857 / 1192857142857)) (n := 12)
    (lo := (68417851 / 100000000)) (hi := (684178511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792857142857 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(792857142857 / 400000000000) = 1/(100000000000 / 792857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13851 : Bounds (207047287 / 100000000) (2070472873 / 1000000000) (Real.log (792857142857 / 100000000000)) := by
  have h := reflection_log_13851_neg
  have he : Real.log (792857142857 / 100000000000) = -Real.log (100000000000 / 792857142857) := by
    rw [show ((792857142857 / 100000000000) : ℝ) = ((100000000000 / 792857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13852_neg : (130352749 / 62500000) ≤ -Real.log (500000000000 / 4024886877829) ∧
    -Real.log (500000000000 / 4024886877829) ≤ (521410997 / 250000000) := by
  have h := checkLog_sound (w := (24886877829 / 8024886877829)) (n := 12)
    (lo := (1550611 / 250000000)) (hi := (1240489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4024886877829 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4024886877829 / 4000000000000) = 1/(500000000000 / 4024886877829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13852 : Bounds (130352749 / 62500000) (521410997 / 250000000) (Real.log (4024886877829 / 500000000000)) := by
  have h := reflection_log_13852_neg
  have he : Real.log (4024886877829 / 500000000000) = -Real.log (500000000000 / 4024886877829) := by
    rw [show ((4024886877829 / 500000000000) : ℝ) = ((500000000000 / 4024886877829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13853_neg : (577736329 / 1000000000) ≤ -Real.log (500 / 891) ∧
    -Real.log (500 / 891) ≤ (57773633 / 100000000) := by
  have h := checkLog_sound (w := (391 / 1391)) (n := 12)
    (lo := (577736329 / 1000000000)) (hi := (57773633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891 / 500) = 1/(500 / 891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13853 : Bounds (577736329 / 1000000000) (57773633 / 100000000) (Real.log (891 / 500)) := by
  have h := reflection_log_13853_neg
  have he : Real.log (891 / 500) = -Real.log (500 / 891) := by
    rw [show ((891 / 500) : ℝ) = ((500 / 891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13854_neg : (304652043 / 200000000) ≤ -Real.log (109 / 500) ∧
    -Real.log (109 / 500) ≤ (761630109 / 500000000) := by
  have h := checkLog_sound (w := (8 / 117)) (n := 12)
    (lo := (27393171 / 200000000)) (hi := (4280183 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 109) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 109) = 1/(109 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13854 : Bounds (-761630109 / 500000000) (-304652043 / 200000000) (Real.log (109 / 500)) := by
  have h := reflection_log_13854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13855_neg : (390847 / 500000000) ≤ -Real.log (500000 / 500391) ∧
    -Real.log (500000 / 500391) ≤ (156339 / 200000000) := by
  have h := checkLog_sound (w := (391 / 1000391)) (n := 12)
    (lo := (390847 / 500000000)) (hi := (156339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500391 / 500000) = 1/(500000 / 500391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13855 : Bounds (390847 / 500000000) (156339 / 200000000) (Real.log (500391 / 500000)) := by
  have h := reflection_log_13855_neg
  have he : Real.log (500391 / 500000) = -Real.log (500000 / 500391) := by
    rw [show ((500391 / 500000) : ℝ) = ((500000 / 500391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13856_neg : (156461 / 200000000) ≤ -Real.log (499609 / 500000) ∧
    -Real.log (499609 / 500000) ≤ (391153 / 500000000) := by
  have h := checkLog_sound (w := (391 / 999609)) (n := 12)
    (lo := (156461 / 200000000)) (hi := (391153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499609) = 1/(499609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13856 : Bounds (-391153 / 500000000) (-156461 / 200000000) (Real.log (499609 / 500000)) := by
  have h := reflection_log_13856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13857_neg : (366384651 / 1000000000) ≤ -Real.log (100000 / 144251) ∧
    -Real.log (100000 / 144251) ≤ (91596163 / 250000000) := by
  have h := checkLog_sound (w := (44251 / 244251)) (n := 12)
    (lo := (366384651 / 1000000000)) (hi := (91596163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144251 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144251 / 100000) = 1/(100000 / 144251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13857 : Bounds (366384651 / 1000000000) (91596163 / 250000000) (Real.log (144251 / 100000)) := by
  have h := reflection_log_13857_neg
  have he : Real.log (144251 / 100000) = -Real.log (100000 / 144251) := by
    rw [show ((144251 / 100000) : ℝ) = ((100000 / 144251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13858_neg : (584310713 / 1000000000) ≤ -Real.log (55749 / 100000) ∧
    -Real.log (55749 / 100000) ≤ (292155357 / 500000000) := by
  have h := checkLog_sound (w := (44251 / 155749)) (n := 12)
    (lo := (584310713 / 1000000000)) (hi := (292155357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 55749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 55749) = 1/(55749 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13858 : Bounds (-292155357 / 500000000) (-584310713 / 1000000000) (Real.log (55749 / 100000)) := by
  have h := reflection_log_13858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13859_neg : (184195817 / 500000000) ≤ -Real.log (31250 / 45169) ∧
    -Real.log (31250 / 45169) ≤ (73678327 / 200000000) := by
  have h := checkLog_sound (w := (13919 / 76419)) (n := 12)
    (lo := (184195817 / 500000000)) (hi := (73678327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45169 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45169 / 31250) = 1/(31250 / 45169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13859 : Bounds (184195817 / 500000000) (73678327 / 200000000) (Real.log (45169 / 31250)) := by
  have h := reflection_log_13859_neg
  have he : Real.log (45169 / 31250) = -Real.log (31250 / 45169) := by
    rw [show ((45169 / 31250) : ℝ) = ((31250 / 45169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13860_neg : (58952257 / 100000000) ≤ -Real.log (17331 / 31250) ∧
    -Real.log (17331 / 31250) ≤ (589522571 / 1000000000) := by
  have h := checkLog_sound (w := (13919 / 48581)) (n := 12)
    (lo := (58952257 / 100000000)) (hi := (589522571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 17331) = 1/(17331 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13860 : Bounds (-589522571 / 1000000000) (-58952257 / 100000000) (Real.log (17331 / 31250)) := by
  have h := reflection_log_13860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13861_neg : (27641367 / 125000000) ≤ -Real.log (782823939 / 976562500) ∧
    -Real.log (782823939 / 976562500) ≤ (221130937 / 1000000000) := by
  have h := checkLog_sound (w := (193738561 / 1759386439)) (n := 12)
    (lo := (27641367 / 125000000)) (hi := (221130937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 782823939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 782823939) = 1/(782823939 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13861 : Bounds (-221130937 / 1000000000) (-27641367 / 125000000) (Real.log (782823939 / 976562500)) := by
  have h := reflection_log_13861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13862_neg : (217926061 / 1000000000) ≤ -Real.log (8041848999 / 10000000000) ∧
    -Real.log (8041848999 / 10000000000) ≤ (108963031 / 500000000) := by
  have h := checkLog_sound (w := (1958151001 / 18041848999)) (n := 12)
    (lo := (217926061 / 1000000000)) (hi := (108963031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8041848999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8041848999) = 1/(8041848999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13862 : Bounds (-108963031 / 500000000) (-217926061 / 1000000000) (Real.log (8041848999 / 10000000000)) := by
  have h := reflection_log_13862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13863_neg : (237673841 / 250000000) ≤ -Real.log (62500000000 / 161719268507) ∧
    -Real.log (62500000000 / 161719268507) ≤ (475347683 / 500000000) := by
  have h := checkLog_sound (w := (36719268507 / 286719268507)) (n := 12)
    (lo := (32193523 / 125000000)) (hi := (51509637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161719268507 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(161719268507 / 125000000000) = 1/(62500000000 / 161719268507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13863 : Bounds (237673841 / 250000000) (475347683 / 500000000) (Real.log (161719268507 / 62500000000)) := by
  have h := reflection_log_13863_neg
  have he : Real.log (161719268507 / 62500000000) = -Real.log (62500000000 / 161719268507) := by
    rw [show ((161719268507 / 62500000000) : ℝ) = ((62500000000 / 161719268507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13864_neg : (239478551 / 250000000) ≤ -Real.log (250000000000 / 651563672033) ∧
    -Real.log (250000000000 / 651563672033) ≤ (478957103 / 500000000) := by
  have h := checkLog_sound (w := (151563672033 / 1151563672033)) (n := 12)
    (lo := (16547939 / 62500000)) (hi := (10590681 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651563672033 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(651563672033 / 500000000000) = 1/(250000000000 / 651563672033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13864 : Bounds (239478551 / 250000000) (478957103 / 500000000) (Real.log (651563672033 / 250000000000)) := by
  have h := reflection_log_13864_neg
  have he : Real.log (651563672033 / 250000000000) = -Real.log (250000000000 / 651563672033) := by
    rw [show ((651563672033 / 250000000000) : ℝ) = ((250000000000 / 651563672033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13865_neg : (130352749 / 62500000) ≤ -Real.log (125000000000 / 1006221719457) ∧
    -Real.log (125000000000 / 1006221719457) ≤ (521410997 / 250000000) := by
  have h := checkLog_sound (w := (6221719457 / 2006221719457)) (n := 12)
    (lo := (1550611 / 250000000)) (hi := (1240489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006221719457 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1006221719457 / 1000000000000) = 1/(125000000000 / 1006221719457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13865 : Bounds (130352749 / 62500000) (521410997 / 250000000) (Real.log (1006221719457 / 125000000000)) := by
  have h := reflection_log_13865_neg
  have he : Real.log (1006221719457 / 125000000000) = -Real.log (125000000000 / 1006221719457) := by
    rw [show ((1006221719457 / 125000000000) : ℝ) = ((125000000000 / 1006221719457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13866_neg : (2100996543 / 1000000000) ≤ -Real.log (500000000000 / 4087155963303) ∧
    -Real.log (500000000000 / 4087155963303) ≤ (2100996547 / 1000000000) := by
  have h := checkLog_sound (w := (87155963303 / 8087155963303)) (n := 12)
    (lo := (21555003 / 1000000000)) (hi := (5388751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4087155963303 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4087155963303 / 4000000000000) = 1/(500000000000 / 4087155963303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13866 : Bounds (2100996543 / 1000000000) (2100996547 / 1000000000) (Real.log (4087155963303 / 500000000000)) := by
  have h := reflection_log_13866_neg
  have he : Real.log (4087155963303 / 500000000000) = -Real.log (500000000000 / 4087155963303) := by
    rw [show ((4087155963303 / 500000000000) : ℝ) = ((500000000000 / 4087155963303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13867_neg : (115883683 / 200000000) ≤ -Real.log (200 / 357) ∧
    -Real.log (200 / 357) ≤ (36213651 / 62500000) := by
  have h := checkLog_sound (w := (157 / 557)) (n := 12)
    (lo := (115883683 / 200000000)) (hi := (36213651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 200) = 1/(200 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13867 : Bounds (115883683 / 200000000) (36213651 / 62500000) (Real.log (357 / 200)) := by
  have h := reflection_log_13867_neg
  have he : Real.log (357 / 200) = -Real.log (200 / 357) := by
    rw [show ((357 / 200) : ℝ) = ((200 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13868_neg : (1537117249 / 1000000000) ≤ -Real.log (43 / 200) ∧
    -Real.log (43 / 200) ≤ (384279313 / 250000000) := by
  have h := checkLog_sound (w := (7 / 93)) (n := 12)
    (lo := (150822889 / 1000000000)) (hi := (15082289 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 43) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 43) = 1/(43 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13868 : Bounds (-384279313 / 250000000) (-1537117249 / 1000000000) (Real.log (43 / 200)) := by
  have h := reflection_log_13868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13869_neg : (196173 / 250000000) ≤ -Real.log (200000 / 200157) ∧
    -Real.log (200000 / 200157) ≤ (784693 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 400157)) (n := 12)
    (lo := (196173 / 250000000)) (hi := (784693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200157 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200157 / 200000) = 1/(200000 / 200157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13869 : Bounds (196173 / 250000000) (784693 / 1000000000) (Real.log (200157 / 200000)) := by
  have h := reflection_log_13869_neg
  have he : Real.log (200157 / 200000) = -Real.log (200000 / 200157) := by
    rw [show ((200157 / 200000) : ℝ) = ((200000 / 200157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13870_neg : (196327 / 250000000) ≤ -Real.log (199843 / 200000) ∧
    -Real.log (199843 / 200000) ≤ (785309 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 399843)) (n := 12)
    (lo := (196327 / 250000000)) (hi := (785309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199843) = 1/(199843 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13870 : Bounds (-785309 / 1000000000) (-196327 / 250000000) (Real.log (199843 / 200000)) := by
  have h := reflection_log_13870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13871_neg : (91984593 / 250000000) ≤ -Real.log (1000000 / 1444753) ∧
    -Real.log (1000000 / 1444753) ≤ (367938373 / 1000000000) := by
  have h := checkLog_sound (w := (444753 / 2444753)) (n := 12)
    (lo := (91984593 / 250000000)) (hi := (367938373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1444753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1444753 / 1000000) = 1/(1000000 / 1444753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13871 : Bounds (91984593 / 250000000) (367938373 / 1000000000) (Real.log (1444753 / 1000000)) := by
  have h := reflection_log_13871_neg
  have he : Real.log (1444753 / 1000000) = -Real.log (1000000 / 1444753) := by
    rw [show ((1444753 / 1000000) : ℝ) = ((1000000 / 1444753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13872_neg : (588342219 / 1000000000) ≤ -Real.log (555247 / 1000000) ∧
    -Real.log (555247 / 1000000) ≤ (29417111 / 50000000) := by
  have h := checkLog_sound (w := (444753 / 1555247)) (n := 12)
    (lo := (588342219 / 1000000000)) (hi := (29417111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 555247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 555247) = 1/(555247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13872 : Bounds (-29417111 / 50000000) (-588342219 / 1000000000) (Real.log (555247 / 1000000)) := by
  have h := reflection_log_13872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13873_neg : (369949841 / 1000000000) ≤ -Real.log (500000 / 723831) ∧
    -Real.log (500000 / 723831) ≤ (184974921 / 500000000) := by
  have h := checkLog_sound (w := (223831 / 1223831)) (n := 12)
    (lo := (369949841 / 1000000000)) (hi := (184974921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723831 / 500000) = 1/(500000 / 723831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13873 : Bounds (369949841 / 1000000000) (184974921 / 500000000) (Real.log (723831 / 500000)) := by
  have h := reflection_log_13873_neg
  have he : Real.log (723831 / 500000) = -Real.log (500000 / 723831) := by
    rw [show ((723831 / 500000) : ℝ) = ((500000 / 723831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13874_neg : (593595101 / 1000000000) ≤ -Real.log (276169 / 500000) ∧
    -Real.log (276169 / 500000) ≤ (296797551 / 500000000) := by
  have h := checkLog_sound (w := (223831 / 776169)) (n := 12)
    (lo := (593595101 / 1000000000)) (hi := (296797551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 276169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 276169) = 1/(276169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13874 : Bounds (-296797551 / 500000000) (-593595101 / 1000000000) (Real.log (276169 / 500000)) := by
  have h := reflection_log_13874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13875_neg : (223645259 / 1000000000) ≤ -Real.log (199899683439 / 250000000000) ∧
    -Real.log (199899683439 / 250000000000) ≤ (11182263 / 50000000) := by
  have h := checkLog_sound (w := (50100316561 / 449899683439)) (n := 12)
    (lo := (223645259 / 1000000000)) (hi := (11182263 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 199899683439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 199899683439) = 1/(199899683439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13875 : Bounds (-11182263 / 50000000) (-223645259 / 1000000000) (Real.log (199899683439 / 250000000000)) := by
  have h := reflection_log_13875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13876_neg : (110201923 / 500000000) ≤ -Real.log (802194768991 / 1000000000000) ∧
    -Real.log (802194768991 / 1000000000000) ≤ (220403847 / 1000000000) := by
  have h := checkLog_sound (w := (197805231009 / 1802194768991)) (n := 12)
    (lo := (110201923 / 500000000)) (hi := (220403847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 802194768991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 802194768991) = 1/(802194768991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13876 : Bounds (-220403847 / 1000000000) (-110201923 / 500000000) (Real.log (802194768991 / 1000000000000)) := by
  have h := reflection_log_13876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13877_neg : (956280591 / 1000000000) ≤ -Real.log (500000000000 / 1301000275553) ∧
    -Real.log (500000000000 / 1301000275553) ≤ (956280593 / 1000000000) := by
  have h := checkLog_sound (w := (301000275553 / 2301000275553)) (n := 12)
    (lo := (263133411 / 1000000000)) (hi := (65783353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301000275553 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1301000275553 / 1000000000000) = 1/(500000000000 / 1301000275553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13877 : Bounds (956280591 / 1000000000) (956280593 / 1000000000) (Real.log (1301000275553 / 500000000000)) := by
  have h := reflection_log_13877_neg
  have he : Real.log (1301000275553 / 500000000000) = -Real.log (500000000000 / 1301000275553) := by
    rw [show ((1301000275553 / 500000000000) : ℝ) = ((500000000000 / 1301000275553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13878_neg : (963544941 / 1000000000) ≤ -Real.log (10000000000 / 26209712169) ∧
    -Real.log (10000000000 / 26209712169) ≤ (963544943 / 1000000000) := by
  have h := checkLog_sound (w := (6209712169 / 46209712169)) (n := 12)
    (lo := (270397761 / 1000000000)) (hi := (135198881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26209712169 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(26209712169 / 20000000000) = 1/(10000000000 / 26209712169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13878 : Bounds (963544941 / 1000000000) (963544943 / 1000000000) (Real.log (26209712169 / 10000000000)) := by
  have h := reflection_log_13878_neg
  have he : Real.log (26209712169 / 10000000000) = -Real.log (10000000000 / 26209712169) := by
    rw [show ((26209712169 / 10000000000) : ℝ) = ((10000000000 / 26209712169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13879_neg : (2100996543 / 1000000000) ≤ -Real.log (250000000000 / 2043577981651) ∧
    -Real.log (250000000000 / 2043577981651) ≤ (2100996547 / 1000000000) := by
  have h := checkLog_sound (w := (43577981651 / 4043577981651)) (n := 12)
    (lo := (21555003 / 1000000000)) (hi := (5388751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2043577981651 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2043577981651 / 2000000000000) = 1/(250000000000 / 2043577981651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13879 : Bounds (2100996543 / 1000000000) (2100996547 / 1000000000) (Real.log (2043577981651 / 250000000000)) := by
  have h := reflection_log_13879_neg
  have he : Real.log (2043577981651 / 250000000000) = -Real.log (250000000000 / 2043577981651) := by
    rw [show ((2043577981651 / 250000000000) : ℝ) = ((250000000000 / 2043577981651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13880_neg : (132283479 / 62500000) ≤ -Real.log (250000000000 / 2075581395349) ∧
    -Real.log (250000000000 / 2075581395349) ≤ (529133917 / 250000000) := by
  have h := checkLog_sound (w := (75581395349 / 4075581395349)) (n := 12)
    (lo := (9273531 / 250000000)) (hi := (296753 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2075581395349 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2075581395349 / 2000000000000) = 1/(250000000000 / 2075581395349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13880 : Bounds (132283479 / 62500000) (529133917 / 250000000) (Real.log (2075581395349 / 250000000000)) := by
  have h := reflection_log_13880_neg
  have he : Real.log (2075581395349 / 250000000000) = -Real.log (250000000000 / 2075581395349) := by
    rw [show ((2075581395349 / 250000000000) : ℝ) = ((250000000000 / 2075581395349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13881_neg : (145274419 / 250000000) ≤ -Real.log (250 / 447) ∧
    -Real.log (250 / 447) ≤ (581097677 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 697)) (n := 12)
    (lo := (145274419 / 250000000)) (hi := (581097677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447 / 250) = 1/(250 / 447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13881 : Bounds (145274419 / 250000000) (581097677 / 1000000000) (Real.log (447 / 250)) := by
  have h := reflection_log_13881_neg
  have he : Real.log (447 / 250) = -Real.log (250 / 447) := by
    rw [show ((447 / 250) : ℝ) = ((250 / 447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13882_neg : (1551169003 / 1000000000) ≤ -Real.log (53 / 250) ∧
    -Real.log (53 / 250) ≤ (775584503 / 500000000) := by
  have h := checkLog_sound (w := (19 / 231)) (n := 12)
    (lo := (164874643 / 1000000000)) (hi := (41218661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 106) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 106) = 1/(53 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13882 : Bounds (-775584503 / 500000000) (-1551169003 / 1000000000) (Real.log (53 / 250)) := by
  have h := reflection_log_13882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13883_neg : (787689 / 1000000000) ≤ -Real.log (250000 / 250197) ∧
    -Real.log (250000 / 250197) ≤ (78769 / 100000000) := by
  have h := checkLog_sound (w := (197 / 500197)) (n := 12)
    (lo := (787689 / 1000000000)) (hi := (78769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250197 / 250000) = 1/(250000 / 250197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13883 : Bounds (787689 / 1000000000) (78769 / 100000000) (Real.log (250197 / 250000)) := by
  have h := reflection_log_13883_neg
  have he : Real.log (250197 / 250000) = -Real.log (250000 / 250197) := by
    rw [show ((250197 / 250000) : ℝ) = ((250000 / 250197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13884_neg : (78831 / 100000000) ≤ -Real.log (249803 / 250000) ∧
    -Real.log (249803 / 250000) ≤ (788311 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 499803)) (n := 12)
    (lo := (78831 / 100000000)) (hi := (788311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249803) = 1/(249803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13884 : Bounds (-788311 / 1000000000) (-78831 / 100000000) (Real.log (249803 / 250000)) := by
  have h := reflection_log_13884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13885_neg : (369495903 / 1000000000) ≤ -Real.log (200000 / 289401) ∧
    -Real.log (200000 / 289401) ≤ (11546747 / 31250000) := by
  have h := checkLog_sound (w := (89401 / 489401)) (n := 12)
    (lo := (369495903 / 1000000000)) (hi := (11546747 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289401 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289401 / 200000) = 1/(200000 / 289401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13885 : Bounds (369495903 / 1000000000) (11546747 / 31250000) (Real.log (289401 / 200000)) := by
  have h := reflection_log_13885_neg
  have he : Real.log (289401 / 200000) = -Real.log (200000 / 289401) := by
    rw [show ((289401 / 200000) : ℝ) = ((200000 / 289401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13886_neg : (592406319 / 1000000000) ≤ -Real.log (110599 / 200000) ∧
    -Real.log (110599 / 200000) ≤ (7405079 / 12500000) := by
  have h := checkLog_sound (w := (89401 / 310599)) (n := 12)
    (lo := (592406319 / 1000000000)) (hi := (7405079 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 110599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 110599) = 1/(110599 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13886 : Bounds (-7405079 / 12500000) (-592406319 / 1000000000) (Real.log (110599 / 200000)) := by
  have h := reflection_log_13886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13887_neg : (37151183 / 100000000) ≤ -Real.log (40000 / 57997) ∧
    -Real.log (40000 / 57997) ≤ (371511831 / 1000000000) := by
  have h := checkLog_sound (w := (17997 / 97997)) (n := 12)
    (lo := (37151183 / 100000000)) (hi := (371511831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57997 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57997 / 40000) = 1/(40000 / 57997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13887 : Bounds (37151183 / 100000000) (371511831 / 1000000000) (Real.log (57997 / 40000)) := by
  have h := reflection_log_13887_neg
  have he : Real.log (57997 / 40000) = -Real.log (40000 / 57997) := by
    rw [show ((57997 / 40000) : ℝ) = ((40000 / 57997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


