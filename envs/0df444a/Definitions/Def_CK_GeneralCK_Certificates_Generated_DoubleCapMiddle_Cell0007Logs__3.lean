-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0007Logs__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0007Logs__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:36:36.945064+00:00
-- url     : https://prove2.me/theorems/f35a9696-874c-4435-88eb-ba992972af63
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0007Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0008Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0007Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0008Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0007Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0008Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0007Logs (+2 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0008Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0007Logs (+2 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0008Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0009Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0007Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0007
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (104471907 / 250000000) ≤ -Real.log (160 / 243) ∧
    -Real.log (160 / 243) ≤ (417887629 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 403)) (n := 12)
    (lo := (104471907 / 250000000)) (hi := (417887629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243 / 160) = 1/(160 / 243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104471907 / 250000000) (417887629 / 1000000000) (Real.log (243 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (243 / 160) = -Real.log (160 / 243) := by
    rw [show ((243 / 160) : ℝ) = ((160 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (91421049 / 125000000) ≤ -Real.log (77 / 160) ∧
    -Real.log (77 / 160) ≤ (365684197 / 500000000) := by
  have h := checkLog_sound (w := (3 / 157)) (n := 12)
    (lo := (9555303 / 250000000)) (hi := (38221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 77) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 77) = 1/(77 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-365684197 / 500000000) (-91421049 / 125000000) (Real.log (77 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (36813973 / 1000000000) ≤ -Real.log (80 / 83) ∧
    -Real.log (80 / 83) ≤ (18406987 / 500000000) := by
  have h := checkLog_sound (w := (3 / 163)) (n := 12)
    (lo := (36813973 / 1000000000)) (hi := (18406987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 80) = 1/(80 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (36813973 / 1000000000) (18406987 / 500000000) (Real.log (83 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (83 / 80) = -Real.log (80 / 83) := by
    rw [show ((83 / 80) : ℝ) = ((80 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9555303 / 250000000) ≤ -Real.log (77 / 80) ∧
    -Real.log (77 / 80) ≤ (38221213 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 157)) (n := 12)
    (lo := (9555303 / 250000000)) (hi := (38221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 77) = 1/(77 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38221213 / 1000000000) (-9555303 / 250000000) (Real.log (77 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (6173153 / 250000000) ≤ -Real.log (40 / 41) ∧
    -Real.log (40 / 41) ≤ (24692613 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 81)) (n := 12)
    (lo := (6173153 / 250000000)) (hi := (24692613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41 / 40) = 1/(40 / 41) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (6173153 / 250000000) (24692613 / 1000000000) (Real.log (41 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (41 / 40) = -Real.log (40 / 41) := by
    rw [show ((41 / 40) : ℝ) = ((40 / 41) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25317807 / 1000000000) ≤ -Real.log (39 / 40) ∧
    -Real.log (39 / 40) ≤ (1582363 / 62500000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 39) = 1/(39 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1582363 / 62500000) (-25317807 / 1000000000) (Real.log (39 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57666561 / 100000000) ≤ -Real.log (1000000 / 1780093) ∧
    -Real.log (1000000 / 1780093) ≤ (576665611 / 1000000000) := by
  have h := checkLog_sound (w := (780093 / 2780093)) (n := 12)
    (lo := (57666561 / 100000000)) (hi := (576665611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780093 / 1000000) = 1/(1000000 / 1780093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57666561 / 100000000) (576665611 / 1000000000) (Real.log (1780093 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1780093 / 1000000) = -Real.log (1000000 / 1780093) := by
    rw [show ((1780093 / 1000000) : ℝ) = ((1000000 / 1780093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (378637637 / 250000000) ≤ -Real.log (219907 / 1000000) ∧
    -Real.log (219907 / 1000000) ≤ (1514550551 / 1000000000) := by
  have h := checkLog_sound (w := (30093 / 469907)) (n := 12)
    (lo := (32064047 / 250000000)) (hi := (128256189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219907) = 1/(219907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1514550551 / 1000000000) (-378637637 / 250000000) (Real.log (219907 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576771217 / 1000000000) ≤ -Real.log (1000000 / 1780281) ∧
    -Real.log (1000000 / 1780281) ≤ (288385609 / 500000000) := by
  have h := checkLog_sound (w := (780281 / 2780281)) (n := 12)
    (lo := (576771217 / 1000000000)) (hi := (288385609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780281 / 1000000) = 1/(1000000 / 1780281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576771217 / 1000000000) (288385609 / 500000000) (Real.log (1780281 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1780281 / 1000000) = -Real.log (1000000 / 1780281) := by
    rw [show ((1780281 / 1000000) : ℝ) = ((1000000 / 1780281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75770291 / 50000000) ≤ -Real.log (219719 / 1000000) ∧
    -Real.log (219719 / 1000000) ≤ (1515405823 / 1000000000) := by
  have h := checkLog_sound (w := (30281 / 469719)) (n := 12)
    (lo := (6455573 / 50000000)) (hi := (129111461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219719) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219719) = 1/(219719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1515405823 / 1000000000) (-75770291 / 50000000) (Real.log (219719 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (510800023 / 1000000000) ≤ -Real.log (15625 / 26041) ∧
    -Real.log (15625 / 26041) ≤ (63850003 / 125000000) := by
  have h := checkLog_sound (w := (5208 / 20833)) (n := 12)
    (lo := (510800023 / 1000000000)) (hi := (63850003 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26041 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26041 / 15625) = 1/(15625 / 26041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (510800023 / 1000000000) (63850003 / 125000000) (Real.log (26041 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (26041 / 15625) = -Real.log (15625 / 26041) := by
    rw [show ((26041 / 15625) : ℝ) = ((15625 / 26041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (137310537 / 125000000) ≤ -Real.log (5209 / 15625) ∧
    -Real.log (5209 / 15625) ≤ (549242149 / 500000000) := by
  have h := checkLog_sound (w := (5207 / 26043)) (n := 12)
    (lo := (101334279 / 250000000)) (hi := (405337117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10418) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 10418) = 1/(5209 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-549242149 / 500000000) (-137310537 / 125000000) (Real.log (5209 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (256553709 / 500000000) ≤ -Real.log (500000 / 835237) ∧
    -Real.log (500000 / 835237) ≤ (513107419 / 1000000000) := by
  have h := checkLog_sound (w := (335237 / 1335237)) (n := 12)
    (lo := (256553709 / 500000000)) (hi := (513107419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835237 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835237 / 500000) = 1/(500000 / 835237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (256553709 / 500000000) (513107419 / 1000000000) (Real.log (835237 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (835237 / 500000) = -Real.log (500000 / 835237) := by
    rw [show ((835237 / 500000) : ℝ) = ((500000 / 835237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55505001 / 50000000) ≤ -Real.log (164763 / 500000) ∧
    -Real.log (164763 / 500000) ≤ (555050011 / 500000000) := by
  have h := checkLog_sound (w := (85237 / 414763)) (n := 12)
    (lo := (10423821 / 25000000)) (hi := (416952841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164763) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 164763) = 1/(164763 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-555050011 / 500000000) (-55505001 / 50000000) (Real.log (164763 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2091216157 / 1000000000) ≤ -Real.log (250000000000 / 2023688422833) ∧
    -Real.log (250000000000 / 2023688422833) ≤ (2091216161 / 1000000000) := by
  have h := checkLog_sound (w := (23688422833 / 4023688422833)) (n := 12)
    (lo := (11774617 / 1000000000)) (hi := (5887309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2023688422833 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2023688422833 / 2000000000000) = 1/(250000000000 / 2023688422833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2091216157 / 1000000000) (2091216161 / 1000000000) (Real.log (2023688422833 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2023688422833 / 250000000000) = -Real.log (250000000000 / 2023688422833) := by
    rw [show ((2023688422833 / 250000000000) : ℝ) = ((250000000000 / 2023688422833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2092177037 / 1000000000) ≤ -Real.log (250000000000 / 2025633877817) ∧
    -Real.log (250000000000 / 2025633877817) ≤ (2092177041 / 1000000000) := by
  have h := checkLog_sound (w := (25633877817 / 4025633877817)) (n := 12)
    (lo := (12735497 / 1000000000)) (hi := (6367749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2025633877817 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2025633877817 / 2000000000000) = 1/(250000000000 / 2025633877817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2092177037 / 1000000000) (2092177041 / 1000000000) (Real.log (2025633877817 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2025633877817 / 250000000000) = -Real.log (250000000000 / 2025633877817) := by
    rw [show ((2025633877817 / 250000000000) : ℝ) = ((250000000000 / 2025633877817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1609284319 / 1000000000) ≤ -Real.log (100000000000 / 499923209829) ∧
    -Real.log (100000000000 / 499923209829) ≤ (804642161 / 500000000) := by
  have h := checkLog_sound (w := (99923209829 / 899923209829)) (n := 12)
    (lo := (222989959 / 1000000000)) (hi := (5574749 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499923209829 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(499923209829 / 400000000000) = 1/(100000000000 / 499923209829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1609284319 / 1000000000) (804642161 / 500000000) (Real.log (499923209829 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (499923209829 / 100000000000) = -Real.log (100000000000 / 499923209829) := by
    rw [show ((499923209829 / 100000000000) : ℝ) = ((100000000000 / 499923209829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (811603719 / 500000000) ≤ -Real.log (500000000000 / 2534661908317) ∧
    -Real.log (500000000000 / 2534661908317) ≤ (1623207441 / 1000000000) := by
  have h := checkLog_sound (w := (534661908317 / 4534661908317)) (n := 12)
    (lo := (118456539 / 500000000)) (hi := (236913079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2534661908317 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2534661908317 / 2000000000000) = 1/(500000000000 / 2534661908317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (811603719 / 500000000) (1623207441 / 1000000000) (Real.log (2534661908317 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2534661908317 / 500000000000) = -Real.log (500000000000 / 2534661908317) := by
    rw [show ((2534661908317 / 500000000000) : ℝ) = ((500000000000 / 2534661908317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0007

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0008Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0008
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (204811559 / 500000000) ≤ -Real.log (160 / 241) ∧
    -Real.log (160 / 241) ≤ (409623119 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 401)) (n := 12)
    (lo := (204811559 / 500000000)) (hi := (409623119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 160) = 1/(160 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (204811559 / 500000000) (409623119 / 1000000000) (Real.log (241 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (241 / 160) = -Real.log (160 / 241) := by
    rw [show ((241 / 160) : ℝ) = ((160 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (352862981 / 500000000) ≤ -Real.log (79 / 160) ∧
    -Real.log (79 / 160) ≤ (176431491 / 250000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 79) = 1/(79 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-176431491 / 250000000) (-352862981 / 500000000) (Real.log (79 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (6173153 / 250000000) ≤ -Real.log (40 / 41) ∧
    -Real.log (40 / 41) ≤ (24692613 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 81)) (n := 12)
    (lo := (6173153 / 250000000)) (hi := (24692613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41 / 40) = 1/(40 / 41) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (6173153 / 250000000) (24692613 / 1000000000) (Real.log (41 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (41 / 40) = -Real.log (40 / 41) := by
    rw [show ((41 / 40) : ℝ) = ((40 / 41) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (25317807 / 1000000000) ≤ -Real.log (39 / 40) ∧
    -Real.log (39 / 40) ≤ (1582363 / 62500000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 39) = 1/(39 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1582363 / 62500000) (-25317807 / 1000000000) (Real.log (39 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (12422519 / 1000000000) ≤ -Real.log (80 / 81) ∧
    -Real.log (80 / 81) ≤ (310563 / 25000000) := by
  have h := checkLog_sound (w := (1 / 161)) (n := 12)
    (lo := (12422519 / 1000000000)) (hi := (310563 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 80) = 1/(80 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (12422519 / 1000000000) (310563 / 25000000) (Real.log (81 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (81 / 80) = -Real.log (80 / 81) := by
    rw [show ((81 / 80) : ℝ) = ((80 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6289391 / 500000000) ≤ -Real.log (79 / 80) ∧
    -Real.log (79 / 80) ≤ (12578783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 79) = 1/(79 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12578783 / 1000000000) (-6289391 / 500000000) (Real.log (79 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57660269 / 100000000) ≤ -Real.log (1000000 / 1779981) ∧
    -Real.log (1000000 / 1779981) ≤ (576602691 / 1000000000) := by
  have h := checkLog_sound (w := (779981 / 2779981)) (n := 12)
    (lo := (57660269 / 100000000)) (hi := (576602691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779981 / 1000000) = 1/(1000000 / 1779981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57660269 / 100000000) (576602691 / 1000000000) (Real.log (1779981 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1779981 / 1000000) = -Real.log (1000000 / 1779981) := by
    rw [show ((1779981 / 1000000) : ℝ) = ((1000000 / 1779981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1514041371 / 1000000000) ≤ -Real.log (220019 / 1000000) ∧
    -Real.log (220019 / 1000000) ≤ (757020687 / 500000000) := by
  have h := checkLog_sound (w := (29981 / 470019)) (n := 12)
    (lo := (127747011 / 1000000000)) (hi := (31936753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220019) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 220019) = 1/(220019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-757020687 / 500000000) (-1514041371 / 1000000000) (Real.log (220019 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576666171 / 1000000000) ≤ -Real.log (500000 / 890047) ∧
    -Real.log (500000 / 890047) ≤ (144166543 / 250000000) := by
  have h := checkLog_sound (w := (390047 / 1390047)) (n := 12)
    (lo := (576666171 / 1000000000)) (hi := (144166543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890047 / 500000) = 1/(500000 / 890047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576666171 / 1000000000) (144166543 / 250000000) (Real.log (890047 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (890047 / 500000) = -Real.log (500000 / 890047) := by
    rw [show ((890047 / 500000) : ℝ) = ((500000 / 890047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (302911019 / 200000000) ≤ -Real.log (109953 / 500000) ∧
    -Real.log (109953 / 500000) ≤ (757277549 / 500000000) := by
  have h := checkLog_sound (w := (15047 / 234953)) (n := 12)
    (lo := (25652147 / 200000000)) (hi := (1002037 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109953) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 109953) = 1/(109953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-757277549 / 500000000) (-302911019 / 200000000) (Real.log (109953 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (508487893 / 1000000000) ≤ -Real.log (40000 / 66511) ∧
    -Real.log (40000 / 66511) ≤ (254243947 / 500000000) := by
  have h := checkLog_sound (w := (26511 / 106511)) (n := 12)
    (lo := (508487893 / 1000000000)) (hi := (254243947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66511 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66511 / 40000) = 1/(40000 / 66511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (508487893 / 1000000000) (254243947 / 500000000) (Real.log (66511 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (66511 / 40000) = -Real.log (40000 / 66511) := by
    rw [show ((66511 / 40000) : ℝ) = ((40000 / 66511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (217400983 / 200000000) ≤ -Real.log (13489 / 40000) ∧
    -Real.log (13489 / 40000) ≤ (1087004917 / 1000000000) := by
  have h := checkLog_sound (w := (6511 / 33489)) (n := 12)
    (lo := (78771547 / 200000000)) (hi := (49232217 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13489) = 1/(13489 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1087004917 / 1000000000) (-217400983 / 200000000) (Real.log (13489 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (510800623 / 1000000000) ≤ -Real.log (8000 / 13333) ∧
    -Real.log (8000 / 13333) ≤ (31925039 / 62500000) := by
  have h := checkLog_sound (w := (5333 / 21333)) (n := 12)
    (lo := (510800623 / 1000000000)) (hi := (31925039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13333 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13333 / 8000) = 1/(8000 / 13333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (510800623 / 1000000000) (31925039 / 62500000) (Real.log (13333 / 8000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (13333 / 8000) = -Real.log (8000 / 13333) := by
    rw [show ((13333 / 8000) : ℝ) = ((8000 / 13333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (219697459 / 200000000) ≤ -Real.log (2667 / 8000) ∧
    -Real.log (2667 / 8000) ≤ (1098487297 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 6667)) (n := 12)
    (lo := (81068023 / 200000000)) (hi := (101335029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2667) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4000 / 2667) = 1/(2667 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1098487297 / 1000000000) (-219697459 / 200000000) (Real.log (2667 / 8000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2090644061 / 1000000000) ≤ -Real.log (500000000000 / 4045062017371) ∧
    -Real.log (500000000000 / 4045062017371) ≤ (418128813 / 200000000) := by
  have h := checkLog_sound (w := (45062017371 / 8045062017371)) (n := 12)
    (lo := (11202521 / 1000000000)) (hi := (5601261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4045062017371 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4045062017371 / 4000000000000) = 1/(500000000000 / 4045062017371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2090644061 / 1000000000) (418128813 / 200000000) (Real.log (4045062017371 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4045062017371 / 500000000000) = -Real.log (500000000000 / 4045062017371) := by
    rw [show ((4045062017371 / 500000000000) : ℝ) = ((500000000000 / 4045062017371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1045610633 / 500000000) ≤ -Real.log (500000000000 / 4047397524397) ∧
    -Real.log (500000000000 / 4047397524397) ≤ (209122127 / 100000000) := by
  have h := checkLog_sound (w := (47397524397 / 8047397524397)) (n := 12)
    (lo := (5889863 / 500000000)) (hi := (11779727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4047397524397 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4047397524397 / 4000000000000) = 1/(500000000000 / 4047397524397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1045610633 / 500000000) (209122127 / 100000000) (Real.log (4047397524397 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4047397524397 / 500000000000) = -Real.log (500000000000 / 4047397524397) := by
    rw [show ((4047397524397 / 500000000000) : ℝ) = ((500000000000 / 4047397524397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1595492807 / 1000000000) ≤ -Real.log (62500000000 / 308172399733) ∧
    -Real.log (62500000000 / 308172399733) ≤ (159549281 / 100000000) := by
  have h := checkLog_sound (w := (58172399733 / 558172399733)) (n := 12)
    (lo := (209198447 / 1000000000)) (hi := (13074903 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308172399733 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(308172399733 / 250000000000) = 1/(62500000000 / 308172399733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1595492807 / 1000000000) (159549281 / 100000000) (Real.log (308172399733 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (308172399733 / 62500000000) = -Real.log (62500000000 / 308172399733) := by
    rw [show ((308172399733 / 62500000000) : ℝ) = ((62500000000 / 308172399733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (804643959 / 500000000) ≤ -Real.log (50000000000 / 249962504687) ∧
    -Real.log (50000000000 / 249962504687) ≤ (1609287921 / 1000000000) := by
  have h := checkLog_sound (w := (49962504687 / 449962504687)) (n := 12)
    (lo := (111496779 / 500000000)) (hi := (222993559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249962504687 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(249962504687 / 200000000000) = 1/(50000000000 / 249962504687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (804643959 / 500000000) (1609287921 / 1000000000) (Real.log (249962504687 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (249962504687 / 50000000000) = -Real.log (50000000000 / 249962504687) := by
    rw [show ((249962504687 / 50000000000) : ℝ) = ((50000000000 / 249962504687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0008

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0009Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0009
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (204811559 / 500000000) ≤ -Real.log (160 / 241) ∧
    -Real.log (160 / 241) ≤ (409623119 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 401)) (n := 12)
    (lo := (204811559 / 500000000)) (hi := (409623119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 160) = 1/(160 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (204811559 / 500000000) (409623119 / 1000000000) (Real.log (241 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (241 / 160) = -Real.log (160 / 241) := by
    rw [show ((241 / 160) : ℝ) = ((160 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (352862981 / 500000000) ≤ -Real.log (79 / 160) ∧
    -Real.log (79 / 160) ≤ (176431491 / 250000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 79) = 1/(79 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-176431491 / 250000000) (-352862981 / 500000000) (Real.log (79 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (101366277 / 250000000) (405465109 / 1000000000) (Real.log (3 / 2)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show ((3 / 2) : ℝ) = ((2 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) (Real.log (1 / 2)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (12422519 / 1000000000) ≤ -Real.log (80 / 81) ∧
    -Real.log (80 / 81) ≤ (310563 / 25000000) := by
  have h := checkLog_sound (w := (1 / 161)) (n := 12)
    (lo := (12422519 / 1000000000)) (hi := (310563 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 80) = 1/(80 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (12422519 / 1000000000) (310563 / 25000000) (Real.log (81 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (81 / 80) = -Real.log (80 / 81) := by
    rw [show ((81 / 80) : ℝ) = ((80 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6289391 / 500000000) ≤ -Real.log (79 / 80) ∧
    -Real.log (79 / 80) ≤ (12578783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 79) = 1/(79 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12578783 / 1000000000) (-6289391 / 500000000) (Real.log (79 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7 : Bounds 0 0 (Real.log 1) := by norm_num [Bounds]

theorem reflection_log_8_neg : (576581903 / 1000000000) ≤ -Real.log (125000 / 222493) ∧
    -Real.log (125000 / 222493) ≤ (36036369 / 62500000) := by
  have h := checkLog_sound (w := (97493 / 347493)) (n := 12)
    (lo := (576581903 / 1000000000)) (hi := (36036369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222493 / 125000) = 1/(125000 / 222493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (576581903 / 1000000000) (36036369 / 62500000) (Real.log (222493 / 125000)) := by
  have h := reflection_log_8_neg
  have he : Real.log (222493 / 125000) = -Real.log (125000 / 222493) := by
    rw [show ((222493 / 125000) : ℝ) = ((125000 / 222493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9_neg : (756936609 / 500000000) ≤ -Real.log (27507 / 125000) ∧
    -Real.log (27507 / 125000) ≤ (1513873221 / 1000000000) := by
  have h := checkLog_sound (w := (3743 / 58757)) (n := 12)
    (lo := (63789429 / 500000000)) (hi := (127578859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27507) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 27507) = 1/(27507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (-1513873221 / 1000000000) (-756936609 / 500000000) (Real.log (27507 / 125000)) := by
  have h := reflection_log_9_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10_neg : (576603251 / 1000000000) ≤ -Real.log (500000 / 889991) ∧
    -Real.log (500000 / 889991) ≤ (144150813 / 250000000) := by
  have h := checkLog_sound (w := (389991 / 1389991)) (n := 12)
    (lo := (576603251 / 1000000000)) (hi := (144150813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889991 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889991 / 500000) = 1/(500000 / 889991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (576603251 / 1000000000) (144150813 / 250000000) (Real.log (889991 / 500000)) := by
  have h := reflection_log_10_neg
  have he : Real.log (889991 / 500000) = -Real.log (500000 / 889991) := by
    rw [show ((889991 / 500000) : ℝ) = ((500000 / 889991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11_neg : (378511479 / 250000000) ≤ -Real.log (110009 / 500000) ∧
    -Real.log (110009 / 500000) ≤ (1514045919 / 1000000000) := by
  have h := checkLog_sound (w := (14991 / 235009)) (n := 12)
    (lo := (31937889 / 250000000)) (hi := (127751557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110009) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 110009) = 1/(110009 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (-1514045919 / 1000000000) (-378511479 / 250000000) (Real.log (110009 / 500000)) := by
  have h := reflection_log_11_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12_neg : (50617161 / 100000000) ≤ -Real.log (62500 / 103683) ∧
    -Real.log (62500 / 103683) ≤ (506171611 / 1000000000) := by
  have h := checkLog_sound (w := (41183 / 166183)) (n := 12)
    (lo := (50617161 / 100000000)) (hi := (506171611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103683 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103683 / 62500) = 1/(62500 / 103683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (50617161 / 100000000) (506171611 / 1000000000) (Real.log (103683 / 62500)) := by
  have h := reflection_log_12_neg
  have he : Real.log (103683 / 62500) = -Real.log (62500 / 103683) := by
    rw [show ((103683 / 62500) : ℝ) = ((62500 / 103683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13_neg : (1075661679 / 1000000000) ≤ -Real.log (21317 / 62500) ∧
    -Real.log (21317 / 62500) ≤ (1075661681 / 1000000000) := by
  have h := checkLog_sound (w := (9933 / 52567)) (n := 12)
    (lo := (382514499 / 1000000000)) (hi := (765029 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 21317) = 1/(21317 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (-1075661681 / 1000000000) (-1075661679 / 1000000000) (Real.log (21317 / 62500)) := by
  have h := reflection_log_13_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14_neg : (254244247 / 500000000) ≤ -Real.log (125000 / 207847) ∧
    -Real.log (125000 / 207847) ≤ (101697699 / 200000000) := by
  have h := checkLog_sound (w := (82847 / 332847)) (n := 12)
    (lo := (254244247 / 500000000)) (hi := (101697699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207847 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207847 / 125000) = 1/(125000 / 207847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (254244247 / 500000000) (101697699 / 200000000) (Real.log (207847 / 125000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (207847 / 125000) = -Real.log (125000 / 207847) := by
    rw [show ((207847 / 125000) : ℝ) = ((125000 / 207847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (27175197 / 25000000) ≤ -Real.log (42153 / 125000) ∧
    -Real.log (42153 / 125000) ≤ (543503941 / 500000000) := by
  have h := checkLog_sound (w := (20347 / 104653)) (n := 12)
    (lo := (3938607 / 10000000)) (hi := (393860701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 42153) = 1/(42153 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (-543503941 / 500000000) (-27175197 / 25000000) (Real.log (42153 / 125000)) := by
  have h := reflection_log_15_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_16_neg : (2090455121 / 1000000000) ≤ -Real.log (500000000000 / 4044297815101) ∧
    -Real.log (500000000000 / 4044297815101) ≤ (16723641 / 8000000) := by
  have h := checkLog_sound (w := (44297815101 / 8044297815101)) (n := 12)
    (lo := (11013581 / 1000000000)) (hi := (5506791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4044297815101 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4044297815101 / 4000000000000) = 1/(500000000000 / 4044297815101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (2090455121 / 1000000000) (16723641 / 8000000) (Real.log (4044297815101 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (4044297815101 / 500000000000) = -Real.log (500000000000 / 4044297815101) := by
    rw [show ((4044297815101 / 500000000000) : ℝ) = ((500000000000 / 4044297815101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (130665573 / 62500000) ≤ -Real.log (250000000000 / 2022541337527) ∧
    -Real.log (250000000000 / 2022541337527) ≤ (522662293 / 250000000) := by
  have h := checkLog_sound (w := (22541337527 / 4022541337527)) (n := 12)
    (lo := (2801907 / 250000000)) (hi := (11207629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2022541337527 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2022541337527 / 2000000000000) = 1/(250000000000 / 2022541337527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (130665573 / 62500000) (522662293 / 250000000) (Real.log (2022541337527 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2022541337527 / 250000000000) = -Real.log (250000000000 / 2022541337527) := by
    rw [show ((2022541337527 / 250000000000) : ℝ) = ((250000000000 / 2022541337527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1581833289 / 1000000000) ≤ -Real.log (500000000000 / 2431932260637) ∧
    -Real.log (500000000000 / 2431932260637) ≤ (395458323 / 250000000) := by
  have h := checkLog_sound (w := (431932260637 / 4431932260637)) (n := 12)
    (lo := (195538929 / 1000000000)) (hi := (19553893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431932260637 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2431932260637 / 2000000000000) = 1/(500000000000 / 2431932260637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1581833289 / 1000000000) (395458323 / 250000000) (Real.log (2431932260637 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2431932260637 / 500000000000) = -Real.log (500000000000 / 2431932260637) := by
    rw [show ((2431932260637 / 500000000000) : ℝ) = ((500000000000 / 2431932260637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (797748187 / 500000000) ≤ -Real.log (100000000000 / 493077598273) ∧
    -Real.log (100000000000 / 493077598273) ≤ (1595496377 / 1000000000) := by
  have h := checkLog_sound (w := (93077598273 / 893077598273)) (n := 12)
    (lo := (104601007 / 500000000)) (hi := (41840403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493077598273 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(493077598273 / 400000000000) = 1/(100000000000 / 493077598273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (797748187 / 500000000) (1595496377 / 1000000000) (Real.log (493077598273 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (493077598273 / 100000000000) = -Real.log (100000000000 / 493077598273) := by
    rw [show ((493077598273 / 100000000000) : ℝ) = ((100000000000 / 493077598273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0009

end


