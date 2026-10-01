-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0330Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0330Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:52:25.438986+00:00
-- url     : https://prove2.me/theorems/082c36c5-57a8-4727-b3b3-ec493e830d5a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0330Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0331Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0330Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0331Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0332Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0333Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0334Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0335Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0336Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0330Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0331Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0332Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0333Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0334Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0335Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0336Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0330Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0331Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0332Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0333Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0334Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0335Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0336Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0330Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0331Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0332Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0333Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0334Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0335Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0336Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0330Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0330
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

theorem reflection_log_1_neg : (108436969 / 500000000) ≤ -Real.log (128 / 159) ∧
    -Real.log (128 / 159) ≤ (216873939 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 287)) (n := 12)
    (lo := (108436969 / 500000000)) (hi := (216873939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 128) = 1/(128 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (108436969 / 500000000) (216873939 / 1000000000) (Real.log (159 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (159 / 128) = -Real.log (128 / 159) := by
    rw [show ((159 / 128) : ℝ) = ((128 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (55463857 / 200000000) ≤ -Real.log (97 / 128) ∧
    -Real.log (97 / 128) ≤ (138659643 / 500000000) := by
  have h := checkLog_sound (w := (31 / 225)) (n := 12)
    (lo := (55463857 / 200000000)) (hi := (138659643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 97) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 97) = 1/(97 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-138659643 / 500000000) (-55463857 / 200000000) (Real.log (97 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (216638061 / 1000000000) ≤ -Real.log (10240 / 12717) ∧
    -Real.log (10240 / 12717) ≤ (108319031 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 22957)) (n := 12)
    (lo := (216638061 / 1000000000)) (hi := (108319031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12717 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12717 / 10240) = 1/(10240 / 12717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (216638061 / 1000000000) (108319031 / 500000000) (Real.log (12717 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12717 / 10240) = -Real.log (10240 / 12717) := by
    rw [show ((12717 / 10240) : ℝ) = ((10240 / 12717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (138466381 / 500000000) ≤ -Real.log (7763 / 10240) ∧
    -Real.log (7763 / 10240) ≤ (276932763 / 1000000000) := by
  have h := checkLog_sound (w := (2477 / 18003)) (n := 12)
    (lo := (138466381 / 500000000)) (hi := (276932763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7763) = 1/(7763 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-276932763 / 1000000000) (-138466381 / 500000000) (Real.log (7763 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24687113 / 62500000) ≤ -Real.log (64 / 95) ∧
    -Real.log (64 / 95) ≤ (394993809 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 159)) (n := 12)
    (lo := (24687113 / 62500000)) (hi := (394993809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95 / 64) = 1/(64 / 95) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24687113 / 62500000) (394993809 / 1000000000) (Real.log (95 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (95 / 64) = -Real.log (64 / 95) := by
    rw [show ((95 / 64) : ℝ) = ((64 / 95) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (662375521 / 1000000000) ≤ -Real.log (33 / 64) ∧
    -Real.log (33 / 64) ≤ (331187761 / 500000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 33) = 1/(33 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-331187761 / 500000000) (-662375521 / 1000000000) (Real.log (33 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (394598993 / 1000000000) ≤ -Real.log (5120 / 7597) ∧
    -Real.log (5120 / 7597) ≤ (197299497 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 12717)) (n := 12)
    (lo := (394598993 / 1000000000)) (hi := (197299497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7597 / 5120) = 1/(5120 / 7597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (394598993 / 1000000000) (197299497 / 500000000) (Real.log (7597 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7597 / 5120) = -Real.log (5120 / 7597) := by
    rw [show ((7597 / 5120) : ℝ) = ((5120 / 7597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (661239803 / 1000000000) ≤ -Real.log (2643 / 5120) ∧
    -Real.log (2643 / 5120) ≤ (165309951 / 250000000) := by
  have h := checkLog_sound (w := (2477 / 7763)) (n := 12)
    (lo := (661239803 / 1000000000)) (hi := (165309951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2643) = 1/(2643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-165309951 / 250000000) (-661239803 / 1000000000) (Real.log (2643 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148493201 / 500000000) ≤ -Real.log (1000000 / 1345797) ∧
    -Real.log (1000000 / 1345797) ≤ (296986403 / 1000000000) := by
  have h := checkLog_sound (w := (345797 / 2345797)) (n := 12)
    (lo := (148493201 / 500000000)) (hi := (296986403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1345797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1345797 / 1000000) = 1/(1000000 / 1345797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148493201 / 500000000) (296986403 / 1000000000) (Real.log (1345797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1345797 / 1000000) = -Real.log (1000000 / 1345797) := by
    rw [show ((1345797 / 1000000) : ℝ) = ((1000000 / 1345797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (212168789 / 500000000) ≤ -Real.log (654203 / 1000000) ∧
    -Real.log (654203 / 1000000) ≤ (424337579 / 1000000000) := by
  have h := checkLog_sound (w := (345797 / 1654203)) (n := 12)
    (lo := (212168789 / 500000000)) (hi := (424337579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 654203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 654203) = 1/(654203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-424337579 / 1000000000) (-212168789 / 500000000) (Real.log (654203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37163233 / 125000000) ≤ -Real.log (1000000 / 1346227) ∧
    -Real.log (1000000 / 1346227) ≤ (59461173 / 200000000) := by
  have h := checkLog_sound (w := (346227 / 2346227)) (n := 12)
    (lo := (37163233 / 125000000)) (hi := (59461173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1346227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1346227 / 1000000) = 1/(1000000 / 1346227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37163233 / 125000000) (59461173 / 200000000) (Real.log (1346227 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1346227 / 1000000) = -Real.log (1000000 / 1346227) := by
    rw [show ((1346227 / 1000000) : ℝ) = ((1000000 / 1346227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (212497541 / 500000000) ≤ -Real.log (653773 / 1000000) ∧
    -Real.log (653773 / 1000000) ≤ (424995083 / 1000000000) := by
  have h := checkLog_sound (w := (346227 / 1653773)) (n := 12)
    (lo := (212497541 / 500000000)) (hi := (424995083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 653773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 653773) = 1/(653773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-424995083 / 1000000000) (-212497541 / 500000000) (Real.log (653773 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45089459 / 200000000) ≤ -Real.log (1000000 / 1252883) ∧
    -Real.log (1000000 / 1252883) ≤ (1761307 / 7812500) := by
  have h := checkLog_sound (w := (252883 / 2252883)) (n := 12)
    (lo := (45089459 / 200000000)) (hi := (1761307 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252883 / 1000000) = 1/(1000000 / 1252883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45089459 / 200000000) (1761307 / 7812500) (Real.log (1252883 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1252883 / 1000000) = -Real.log (1000000 / 1252883) := by
    rw [show ((1252883 / 1000000) : ℝ) = ((1000000 / 1252883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291533479 / 1000000000) ≤ -Real.log (747117 / 1000000) ∧
    -Real.log (747117 / 1000000) ≤ (7288337 / 25000000) := by
  have h := checkLog_sound (w := (252883 / 1747117)) (n := 12)
    (lo := (291533479 / 1000000000)) (hi := (7288337 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747117) = 1/(747117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7288337 / 25000000) (-291533479 / 1000000000) (Real.log (747117 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (225715441 / 1000000000) ≤ -Real.log (1000000 / 1253219) ∧
    -Real.log (1000000 / 1253219) ≤ (112857721 / 500000000) := by
  have h := checkLog_sound (w := (253219 / 2253219)) (n := 12)
    (lo := (225715441 / 1000000000)) (hi := (112857721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253219 / 1000000) = 1/(1000000 / 1253219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (225715441 / 1000000000) (112857721 / 500000000) (Real.log (1253219 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1253219 / 1000000) = -Real.log (1000000 / 1253219) := by
    rw [show ((1253219 / 1000000) : ℝ) = ((1000000 / 1253219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (291983309 / 1000000000) ≤ -Real.log (746781 / 1000000) ∧
    -Real.log (746781 / 1000000) ≤ (29198331 / 100000000) := by
  have h := checkLog_sound (w := (253219 / 1746781)) (n := 12)
    (lo := (291983309 / 1000000000)) (hi := (29198331 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746781) = 1/(746781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-29198331 / 100000000) (-291983309 / 1000000000) (Real.log (746781 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (36066199 / 50000000) ≤ -Real.log (125000000000 / 257144380261) ∧
    -Real.log (125000000000 / 257144380261) ≤ (360661991 / 500000000) := by
  have h := checkLog_sound (w := (7144380261 / 507144380261)) (n := 12)
    (lo := (35221 / 1250000)) (hi := (28176801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257144380261 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(257144380261 / 250000000000) = 1/(125000000000 / 257144380261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36066199 / 50000000) (360661991 / 500000000) (Real.log (257144380261 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (257144380261 / 125000000000) = -Real.log (125000000000 / 257144380261) := by
    rw [show ((257144380261 / 125000000000) : ℝ) = ((125000000000 / 257144380261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (361150473 / 500000000) ≤ -Real.log (12500000000 / 25739572451) ∧
    -Real.log (12500000000 / 25739572451) ≤ (180575237 / 250000000) := by
  have h := checkLog_sound (w := (739572451 / 50739572451)) (n := 12)
    (lo := (14576883 / 500000000)) (hi := (29153767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25739572451 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25739572451 / 25000000000) = 1/(12500000000 / 25739572451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (361150473 / 500000000) (180575237 / 250000000) (Real.log (25739572451 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25739572451 / 12500000000) = -Real.log (12500000000 / 25739572451) := by
    rw [show ((25739572451 / 12500000000) : ℝ) = ((12500000000 / 25739572451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20679231 / 40000000) ≤ -Real.log (500000000000 / 838478444473) ∧
    -Real.log (500000000000 / 838478444473) ≤ (64622597 / 125000000) := by
  have h := checkLog_sound (w := (338478444473 / 1338478444473)) (n := 12)
    (lo := (20679231 / 40000000)) (hi := (64622597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838478444473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838478444473 / 500000000000) = 1/(500000000000 / 838478444473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (20679231 / 40000000) (64622597 / 125000000) (Real.log (838478444473 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (838478444473 / 500000000000) = -Real.log (500000000000 / 838478444473) := by
    rw [show ((838478444473 / 500000000000) : ℝ) = ((500000000000 / 838478444473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (414159 / 800000) ≤ -Real.log (500000000000 / 839080667559) ∧
    -Real.log (500000000000 / 839080667559) ≤ (517698751 / 1000000000) := by
  have h := checkLog_sound (w := (339080667559 / 1339080667559)) (n := 12)
    (lo := (414159 / 800000)) (hi := (517698751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839080667559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839080667559 / 500000000000) = 1/(500000000000 / 839080667559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (414159 / 800000) (517698751 / 1000000000) (Real.log (839080667559 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (839080667559 / 500000000000) = -Real.log (500000000000 / 839080667559) := by
    rw [show ((839080667559 / 500000000000) : ℝ) = ((500000000000 / 839080667559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0330

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0331Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0331
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

theorem reflection_log_1_neg : (216638061 / 1000000000) ≤ -Real.log (10240 / 12717) ∧
    -Real.log (10240 / 12717) ≤ (108319031 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 22957)) (n := 12)
    (lo := (216638061 / 1000000000)) (hi := (108319031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12717 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12717 / 10240) = 1/(10240 / 12717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (216638061 / 1000000000) (108319031 / 500000000) (Real.log (12717 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12717 / 10240) = -Real.log (10240 / 12717) := by
    rw [show ((12717 / 10240) : ℝ) = ((10240 / 12717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (138466381 / 500000000) ≤ -Real.log (7763 / 10240) ∧
    -Real.log (7763 / 10240) ≤ (276932763 / 1000000000) := by
  have h := checkLog_sound (w := (2477 / 18003)) (n := 12)
    (lo := (138466381 / 500000000)) (hi := (276932763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7763) = 1/(7763 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-276932763 / 1000000000) (-138466381 / 500000000) (Real.log (7763 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13525133 / 62500000) ≤ -Real.log (5120 / 6357) ∧
    -Real.log (5120 / 6357) ≤ (216402129 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 11477)) (n := 12)
    (lo := (13525133 / 62500000)) (hi := (216402129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6357 / 5120) = 1/(5120 / 6357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13525133 / 62500000) (216402129 / 1000000000) (Real.log (6357 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6357 / 5120) = -Real.log (5120 / 6357) := by
    rw [show ((6357 / 5120) : ℝ) = ((5120 / 6357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (69136597 / 250000000) ≤ -Real.log (3883 / 5120) ∧
    -Real.log (3883 / 5120) ≤ (276546389 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 9003)) (n := 12)
    (lo := (69136597 / 250000000)) (hi := (276546389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3883) = 1/(3883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-276546389 / 1000000000) (-69136597 / 250000000) (Real.log (3883 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (394598993 / 1000000000) ≤ -Real.log (5120 / 7597) ∧
    -Real.log (5120 / 7597) ≤ (197299497 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 12717)) (n := 12)
    (lo := (394598993 / 1000000000)) (hi := (197299497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7597 / 5120) = 1/(5120 / 7597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (394598993 / 1000000000) (197299497 / 500000000) (Real.log (7597 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7597 / 5120) = -Real.log (5120 / 7597) := by
    rw [show ((7597 / 5120) : ℝ) = ((5120 / 7597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (661239803 / 1000000000) ≤ -Real.log (2643 / 5120) ∧
    -Real.log (2643 / 5120) ≤ (165309951 / 250000000) := by
  have h := checkLog_sound (w := (2477 / 7763)) (n := 12)
    (lo := (661239803 / 1000000000)) (hi := (165309951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2643) = 1/(2643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-165309951 / 250000000) (-661239803 / 1000000000) (Real.log (2643 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197102011 / 500000000) ≤ -Real.log (2560 / 3797) ∧
    -Real.log (2560 / 3797) ≤ (394204023 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 6357)) (n := 12)
    (lo := (197102011 / 500000000)) (hi := (394204023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3797 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3797 / 2560) = 1/(2560 / 3797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197102011 / 500000000) (394204023 / 1000000000) (Real.log (3797 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3797 / 2560) = -Real.log (2560 / 3797) := by
    rw [show ((3797 / 2560) : ℝ) = ((2560 / 3797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (660105373 / 1000000000) ≤ -Real.log (1323 / 2560) ∧
    -Real.log (1323 / 2560) ≤ (330052687 / 500000000) := by
  have h := checkLog_sound (w := (1237 / 3883)) (n := 12)
    (lo := (660105373 / 1000000000)) (hi := (330052687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1323) = 1/(1323 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-330052687 / 500000000) (-660105373 / 1000000000) (Real.log (1323 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74167081 / 250000000) ≤ -Real.log (1000000 / 1345369) ∧
    -Real.log (1000000 / 1345369) ≤ (11866733 / 40000000) := by
  have h := checkLog_sound (w := (345369 / 2345369)) (n := 12)
    (lo := (74167081 / 250000000)) (hi := (11866733 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1345369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1345369 / 1000000) = 1/(1000000 / 1345369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74167081 / 250000000) (11866733 / 40000000) (Real.log (1345369 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1345369 / 1000000) = -Real.log (1000000 / 1345369) := by
    rw [show ((1345369 / 1000000) : ℝ) = ((1000000 / 1345369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10592089 / 25000000) ≤ -Real.log (654631 / 1000000) ∧
    -Real.log (654631 / 1000000) ≤ (423683561 / 1000000000) := by
  have h := checkLog_sound (w := (345369 / 1654631)) (n := 12)
    (lo := (10592089 / 25000000)) (hi := (423683561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 654631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 654631) = 1/(654631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-423683561 / 1000000000) (-10592089 / 25000000) (Real.log (654631 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18561743 / 62500000) ≤ -Real.log (1000000 / 1345799) ∧
    -Real.log (1000000 / 1345799) ≤ (296987889 / 1000000000) := by
  have h := checkLog_sound (w := (345799 / 2345799)) (n := 12)
    (lo := (18561743 / 62500000)) (hi := (296987889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1345799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1345799 / 1000000) = 1/(1000000 / 1345799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18561743 / 62500000) (296987889 / 1000000000) (Real.log (1345799 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1345799 / 1000000) = -Real.log (1000000 / 1345799) := by
    rw [show ((1345799 / 1000000) : ℝ) = ((1000000 / 1345799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84868127 / 200000000) ≤ -Real.log (654201 / 1000000) ∧
    -Real.log (654201 / 1000000) ≤ (106085159 / 250000000) := by
  have h := checkLog_sound (w := (345799 / 1654201)) (n := 12)
    (lo := (84868127 / 200000000)) (hi := (106085159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 654201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 654201) = 1/(654201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-106085159 / 250000000) (-84868127 / 200000000) (Real.log (654201 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (56294969 / 250000000) ≤ -Real.log (250000 / 313137) ∧
    -Real.log (250000 / 313137) ≤ (225179877 / 1000000000) := by
  have h := checkLog_sound (w := (63137 / 563137)) (n := 12)
    (lo := (56294969 / 250000000)) (hi := (225179877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313137 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313137 / 250000) = 1/(250000 / 313137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (56294969 / 250000000) (225179877 / 1000000000) (Real.log (313137 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (313137 / 250000) = -Real.log (250000 / 313137) := by
    rw [show ((313137 / 250000) : ℝ) = ((250000 / 313137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291085189 / 1000000000) ≤ -Real.log (186863 / 250000) ∧
    -Real.log (186863 / 250000) ≤ (29108519 / 100000000) := by
  have h := checkLog_sound (w := (63137 / 436863)) (n := 12)
    (lo := (291085189 / 1000000000)) (hi := (29108519 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 186863) = 1/(186863 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-29108519 / 100000000) (-291085189 / 1000000000) (Real.log (186863 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (225448093 / 1000000000) ≤ -Real.log (250000 / 313221) ∧
    -Real.log (250000 / 313221) ≤ (112724047 / 500000000) := by
  have h := checkLog_sound (w := (63221 / 563221)) (n := 12)
    (lo := (225448093 / 1000000000)) (hi := (112724047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313221 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313221 / 250000) = 1/(250000 / 313221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (225448093 / 1000000000) (112724047 / 500000000) (Real.log (313221 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (313221 / 250000) = -Real.log (250000 / 313221) := by
    rw [show ((313221 / 250000) : ℝ) = ((250000 / 313221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (145767409 / 500000000) ≤ -Real.log (186779 / 250000) ∧
    -Real.log (186779 / 250000) ≤ (291534819 / 1000000000) := by
  have h := checkLog_sound (w := (63221 / 436779)) (n := 12)
    (lo := (145767409 / 500000000)) (hi := (291534819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 186779) = 1/(186779 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-291534819 / 1000000000) (-145767409 / 500000000) (Real.log (186779 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (144070377 / 200000000) ≤ -Real.log (250000000000 / 513789065901) ∧
    -Real.log (250000000000 / 513789065901) ≤ (720351887 / 1000000000) := by
  have h := checkLog_sound (w := (13789065901 / 1013789065901)) (n := 12)
    (lo := (5440941 / 200000000)) (hi := (13602353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513789065901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(513789065901 / 500000000000) = 1/(250000000000 / 513789065901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (144070377 / 200000000) (720351887 / 1000000000) (Real.log (513789065901 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (513789065901 / 250000000000) = -Real.log (250000000000 / 513789065901) := by
    rw [show ((513789065901 / 250000000000) : ℝ) = ((250000000000 / 513789065901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (721328523 / 1000000000) ≤ -Real.log (250000000000 / 514291097079) ∧
    -Real.log (250000000000 / 514291097079) ≤ (28853141 / 40000000) := by
  have h := checkLog_sound (w := (14291097079 / 1014291097079)) (n := 12)
    (lo := (28181343 / 1000000000)) (hi := (880667 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514291097079 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(514291097079 / 500000000000) = 1/(250000000000 / 514291097079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (721328523 / 1000000000) (28853141 / 40000000) (Real.log (514291097079 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (514291097079 / 250000000000) = -Real.log (250000000000 / 514291097079) := by
    rw [show ((514291097079 / 250000000000) : ℝ) = ((250000000000 / 514291097079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (258132533 / 500000000) ≤ -Real.log (15625000000 / 26183704773) ∧
    -Real.log (15625000000 / 26183704773) ≤ (516265067 / 1000000000) := by
  have h := checkLog_sound (w := (10558704773 / 41808704773)) (n := 12)
    (lo := (258132533 / 500000000)) (hi := (516265067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26183704773 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26183704773 / 15625000000) = 1/(15625000000 / 26183704773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (258132533 / 500000000) (516265067 / 1000000000) (Real.log (26183704773 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26183704773 / 15625000000) = -Real.log (15625000000 / 26183704773) := by
    rw [show ((26183704773 / 15625000000) : ℝ) = ((15625000000 / 26183704773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (516982911 / 1000000000) ≤ -Real.log (500000000000 / 838480236001) ∧
    -Real.log (500000000000 / 838480236001) ≤ (4038929 / 7812500) := by
  have h := checkLog_sound (w := (338480236001 / 1338480236001)) (n := 12)
    (lo := (516982911 / 1000000000)) (hi := (4038929 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838480236001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838480236001 / 500000000000) = 1/(500000000000 / 838480236001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (516982911 / 1000000000) (4038929 / 7812500) (Real.log (838480236001 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (838480236001 / 500000000000) = -Real.log (500000000000 / 838480236001) := by
    rw [show ((838480236001 / 500000000000) : ℝ) = ((500000000000 / 838480236001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0331

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0332Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0332
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

theorem reflection_log_1_neg : (13525133 / 62500000) ≤ -Real.log (5120 / 6357) ∧
    -Real.log (5120 / 6357) ≤ (216402129 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 11477)) (n := 12)
    (lo := (13525133 / 62500000)) (hi := (216402129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6357 / 5120) = 1/(5120 / 6357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13525133 / 62500000) (216402129 / 1000000000) (Real.log (6357 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6357 / 5120) = -Real.log (5120 / 6357) := by
    rw [show ((6357 / 5120) : ℝ) = ((5120 / 6357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (69136597 / 250000000) ≤ -Real.log (3883 / 5120) ∧
    -Real.log (3883 / 5120) ≤ (276546389 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 9003)) (n := 12)
    (lo := (69136597 / 250000000)) (hi := (276546389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3883) = 1/(3883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-276546389 / 1000000000) (-69136597 / 250000000) (Real.log (3883 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10808307 / 50000000) ≤ -Real.log (10240 / 12711) ∧
    -Real.log (10240 / 12711) ≤ (216166141 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 22951)) (n := 12)
    (lo := (10808307 / 50000000)) (hi := (216166141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12711 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12711 / 10240) = 1/(10240 / 12711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10808307 / 50000000) (216166141 / 1000000000) (Real.log (12711 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12711 / 10240) = -Real.log (10240 / 12711) := by
    rw [show ((12711 / 10240) : ℝ) = ((10240 / 12711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (276160163 / 1000000000) ≤ -Real.log (7769 / 10240) ∧
    -Real.log (7769 / 10240) ≤ (69040041 / 250000000) := by
  have h := checkLog_sound (w := (2471 / 18009)) (n := 12)
    (lo := (276160163 / 1000000000)) (hi := (69040041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7769) = 1/(7769 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69040041 / 250000000) (-276160163 / 1000000000) (Real.log (7769 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (197102011 / 500000000) ≤ -Real.log (2560 / 3797) ∧
    -Real.log (2560 / 3797) ≤ (394204023 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 6357)) (n := 12)
    (lo := (197102011 / 500000000)) (hi := (394204023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3797 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3797 / 2560) = 1/(2560 / 3797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (197102011 / 500000000) (394204023 / 1000000000) (Real.log (3797 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3797 / 2560) = -Real.log (2560 / 3797) := by
    rw [show ((3797 / 2560) : ℝ) = ((2560 / 3797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (660105373 / 1000000000) ≤ -Real.log (1323 / 2560) ∧
    -Real.log (1323 / 2560) ≤ (330052687 / 500000000) := by
  have h := checkLog_sound (w := (1237 / 3883)) (n := 12)
    (lo := (660105373 / 1000000000)) (hi := (330052687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1323) = 1/(1323 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-330052687 / 500000000) (-660105373 / 1000000000) (Real.log (1323 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (78761779 / 200000000) ≤ -Real.log (5120 / 7591) ∧
    -Real.log (5120 / 7591) ≤ (769158 / 1953125) := by
  have h := checkLog_sound (w := (2471 / 12711)) (n := 12)
    (lo := (78761779 / 200000000)) (hi := (769158 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7591 / 5120) = 1/(5120 / 7591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (78761779 / 200000000) (769158 / 1953125) (Real.log (7591 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7591 / 5120) = -Real.log (5120 / 7591) := by
    rw [show ((7591 / 5120) : ℝ) = ((5120 / 7591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (164743057 / 250000000) ≤ -Real.log (2649 / 5120) ∧
    -Real.log (2649 / 5120) ≤ (658972229 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 7769)) (n := 12)
    (lo := (164743057 / 250000000)) (hi := (658972229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2649) = 1/(2649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-658972229 / 1000000000) (-164743057 / 250000000) (Real.log (2649 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148174701 / 500000000) ≤ -Real.log (50000 / 67247) ∧
    -Real.log (50000 / 67247) ≤ (296349403 / 1000000000) := by
  have h := checkLog_sound (w := (17247 / 117247)) (n := 12)
    (lo := (148174701 / 500000000)) (hi := (296349403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67247 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67247 / 50000) = 1/(50000 / 67247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148174701 / 500000000) (296349403 / 1000000000) (Real.log (67247 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (67247 / 50000) = -Real.log (50000 / 67247) := by
    rw [show ((67247 / 50000) : ℝ) = ((50000 / 67247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (105757111 / 250000000) ≤ -Real.log (32753 / 50000) ∧
    -Real.log (32753 / 50000) ≤ (84605689 / 200000000) := by
  have h := checkLog_sound (w := (17247 / 82753)) (n := 12)
    (lo := (105757111 / 250000000)) (hi := (84605689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32753) = 1/(32753 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-84605689 / 200000000) (-105757111 / 250000000) (Real.log (32753 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (74167267 / 250000000) ≤ -Real.log (100000 / 134537) ∧
    -Real.log (100000 / 134537) ≤ (296669069 / 1000000000) := by
  have h := checkLog_sound (w := (34537 / 234537)) (n := 12)
    (lo := (74167267 / 250000000)) (hi := (296669069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134537 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134537 / 100000) = 1/(100000 / 134537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (74167267 / 250000000) (296669069 / 1000000000) (Real.log (134537 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (134537 / 100000) = -Real.log (100000 / 134537) := by
    rw [show ((134537 / 100000) : ℝ) = ((100000 / 134537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13240159 / 31250000) ≤ -Real.log (65463 / 100000) ∧
    -Real.log (65463 / 100000) ≤ (423685089 / 1000000000) := by
  have h := checkLog_sound (w := (34537 / 165463)) (n := 12)
    (lo := (13240159 / 31250000)) (hi := (423685089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 65463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 65463) = 1/(65463 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-423685089 / 1000000000) (-13240159 / 31250000) (Real.log (65463 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (112456193 / 500000000) ≤ -Real.log (1000000 / 1252213) ∧
    -Real.log (1000000 / 1252213) ≤ (224912387 / 1000000000) := by
  have h := checkLog_sound (w := (252213 / 2252213)) (n := 12)
    (lo := (112456193 / 500000000)) (hi := (224912387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252213 / 1000000) = 1/(1000000 / 1252213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (112456193 / 500000000) (224912387 / 1000000000) (Real.log (1252213 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1252213 / 1000000) = -Real.log (1000000 / 1252213) := by
    rw [show ((1252213 / 1000000) : ℝ) = ((1000000 / 1252213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2906371 / 10000000) ≤ -Real.log (747787 / 1000000) ∧
    -Real.log (747787 / 1000000) ≤ (290637101 / 1000000000) := by
  have h := checkLog_sound (w := (252213 / 1747787)) (n := 12)
    (lo := (2906371 / 10000000)) (hi := (290637101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747787) = 1/(747787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-290637101 / 1000000000) (-2906371 / 10000000) (Real.log (747787 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (112590337 / 500000000) ≤ -Real.log (1000000 / 1252549) ∧
    -Real.log (1000000 / 1252549) ≤ (9007227 / 40000000) := by
  have h := checkLog_sound (w := (252549 / 2252549)) (n := 12)
    (lo := (112590337 / 500000000)) (hi := (9007227 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252549 / 1000000) = 1/(1000000 / 1252549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (112590337 / 500000000) (9007227 / 40000000) (Real.log (1252549 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1252549 / 1000000) = -Real.log (1000000 / 1252549) := by
    rw [show ((1252549 / 1000000) : ℝ) = ((1000000 / 1252549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (291086527 / 1000000000) ≤ -Real.log (747451 / 1000000) ∧
    -Real.log (747451 / 1000000) ≤ (4548227 / 15625000) := by
  have h := checkLog_sound (w := (252549 / 1747451)) (n := 12)
    (lo := (291086527 / 1000000000)) (hi := (4548227 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747451) = 1/(747451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4548227 / 15625000) (-291086527 / 1000000000) (Real.log (747451 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (359688923 / 500000000) ≤ -Real.log (500000000000 / 1026577718071) ∧
    -Real.log (500000000000 / 1026577718071) ≤ (89922231 / 125000000) := by
  have h := checkLog_sound (w := (26577718071 / 2026577718071)) (n := 12)
    (lo := (13115333 / 500000000)) (hi := (26230667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026577718071 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026577718071 / 1000000000000) = 1/(500000000000 / 1026577718071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (359688923 / 500000000) (89922231 / 125000000) (Real.log (1026577718071 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1026577718071 / 500000000000) = -Real.log (500000000000 / 1026577718071) := by
    rw [show ((1026577718071 / 500000000000) : ℝ) = ((500000000000 / 1026577718071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (180088539 / 250000000) ≤ -Real.log (250000000000 / 513790232651) ∧
    -Real.log (250000000000 / 513790232651) ≤ (360177079 / 500000000) := by
  have h := checkLog_sound (w := (13790232651 / 1013790232651)) (n := 12)
    (lo := (425109 / 15625000)) (hi := (27206977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513790232651 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(513790232651 / 500000000000) = 1/(250000000000 / 513790232651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (180088539 / 250000000) (360177079 / 500000000) (Real.log (513790232651 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (513790232651 / 250000000000) = -Real.log (250000000000 / 513790232651) := by
    rw [show ((513790232651 / 250000000000) : ℝ) = ((250000000000 / 513790232651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (257774743 / 500000000) ≤ -Real.log (62500000000 / 104659899811) ∧
    -Real.log (62500000000 / 104659899811) ≤ (515549487 / 1000000000) := by
  have h := checkLog_sound (w := (42159899811 / 167159899811)) (n := 12)
    (lo := (257774743 / 500000000)) (hi := (515549487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104659899811 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104659899811 / 62500000000) = 1/(62500000000 / 104659899811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (257774743 / 500000000) (515549487 / 1000000000) (Real.log (104659899811 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (104659899811 / 62500000000) = -Real.log (62500000000 / 104659899811) := by
    rw [show ((104659899811 / 62500000000) : ℝ) = ((62500000000 / 104659899811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (258133601 / 500000000) ≤ -Real.log (250000000000 / 418940171329) ∧
    -Real.log (250000000000 / 418940171329) ≤ (516267203 / 1000000000) := by
  have h := checkLog_sound (w := (168940171329 / 668940171329)) (n := 12)
    (lo := (258133601 / 500000000)) (hi := (516267203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418940171329 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418940171329 / 250000000000) = 1/(250000000000 / 418940171329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (258133601 / 500000000) (516267203 / 1000000000) (Real.log (418940171329 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (418940171329 / 250000000000) = -Real.log (250000000000 / 418940171329) := by
    rw [show ((418940171329 / 250000000000) : ℝ) = ((250000000000 / 418940171329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0332

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0333Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0333
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

theorem reflection_log_1_neg : (10808307 / 50000000) ≤ -Real.log (10240 / 12711) ∧
    -Real.log (10240 / 12711) ≤ (216166141 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 22951)) (n := 12)
    (lo := (10808307 / 50000000)) (hi := (216166141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12711 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12711 / 10240) = 1/(10240 / 12711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10808307 / 50000000) (216166141 / 1000000000) (Real.log (12711 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12711 / 10240) = -Real.log (10240 / 12711) := by
    rw [show ((12711 / 10240) : ℝ) = ((10240 / 12711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (276160163 / 1000000000) ≤ -Real.log (7769 / 10240) ∧
    -Real.log (7769 / 10240) ≤ (69040041 / 250000000) := by
  have h := checkLog_sound (w := (2471 / 18009)) (n := 12)
    (lo := (276160163 / 1000000000)) (hi := (69040041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7769) = 1/(7769 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69040041 / 250000000) (-276160163 / 1000000000) (Real.log (7769 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13495631 / 62500000) ≤ -Real.log (2560 / 3177) ∧
    -Real.log (2560 / 3177) ≤ (215930097 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 5737)) (n := 12)
    (lo := (13495631 / 62500000)) (hi := (215930097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3177 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3177 / 2560) = 1/(2560 / 3177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13495631 / 62500000) (215930097 / 1000000000) (Real.log (3177 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3177 / 2560) = -Real.log (2560 / 3177) := by
    rw [show ((3177 / 2560) : ℝ) = ((2560 / 3177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34471761 / 125000000) ≤ -Real.log (1943 / 2560) ∧
    -Real.log (1943 / 2560) ≤ (275774089 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 4503)) (n := 12)
    (lo := (34471761 / 125000000)) (hi := (275774089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1943) = 1/(1943 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-275774089 / 1000000000) (-34471761 / 125000000) (Real.log (1943 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (78761779 / 200000000) ≤ -Real.log (5120 / 7591) ∧
    -Real.log (5120 / 7591) ≤ (769158 / 1953125) := by
  have h := checkLog_sound (w := (2471 / 12711)) (n := 12)
    (lo := (78761779 / 200000000)) (hi := (769158 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7591 / 5120) = 1/(5120 / 7591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (78761779 / 200000000) (769158 / 1953125) (Real.log (7591 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7591 / 5120) = -Real.log (5120 / 7591) := by
    rw [show ((7591 / 5120) : ℝ) = ((5120 / 7591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (164743057 / 250000000) ≤ -Real.log (2649 / 5120) ∧
    -Real.log (2649 / 5120) ≤ (658972229 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 7769)) (n := 12)
    (lo := (164743057 / 250000000)) (hi := (658972229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2649) = 1/(2649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-658972229 / 1000000000) (-164743057 / 250000000) (Real.log (2649 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (393413613 / 1000000000) ≤ -Real.log (1280 / 1897) ∧
    -Real.log (1280 / 1897) ≤ (196706807 / 500000000) := by
  have h := checkLog_sound (w := (617 / 3177)) (n := 12)
    (lo := (393413613 / 1000000000)) (hi := (196706807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1897 / 1280) = 1/(1280 / 1897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (393413613 / 1000000000) (196706807 / 500000000) (Real.log (1897 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1897 / 1280) = -Real.log (1280 / 1897) := by
    rw [show ((1897 / 1280) : ℝ) = ((1280 / 1897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (328920183 / 500000000) ≤ -Real.log (663 / 1280) ∧
    -Real.log (663 / 1280) ≤ (657840367 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 1943)) (n := 12)
    (lo := (328920183 / 500000000)) (hi := (657840367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 663) = 1/(663 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-657840367 / 1000000000) (-328920183 / 500000000) (Real.log (663 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148015189 / 500000000) ≤ -Real.log (1000000 / 1344511) ∧
    -Real.log (1000000 / 1344511) ≤ (296030379 / 1000000000) := by
  have h := checkLog_sound (w := (344511 / 2344511)) (n := 12)
    (lo := (148015189 / 500000000)) (hi := (296030379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1344511 / 1000000) = 1/(1000000 / 1344511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148015189 / 500000000) (296030379 / 1000000000) (Real.log (1344511 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1344511 / 1000000) = -Real.log (1000000 / 1344511) := by
    rw [show ((1344511 / 1000000) : ℝ) = ((1000000 / 1344511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (422373757 / 1000000000) ≤ -Real.log (655489 / 1000000) ∧
    -Real.log (655489 / 1000000) ≤ (211186879 / 500000000) := by
  have h := checkLog_sound (w := (344511 / 1655489)) (n := 12)
    (lo := (422373757 / 1000000000)) (hi := (211186879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 655489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 655489) = 1/(655489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-211186879 / 500000000) (-422373757 / 1000000000) (Real.log (655489 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (59270029 / 200000000) ≤ -Real.log (1000000 / 1344941) ∧
    -Real.log (1000000 / 1344941) ≤ (148175073 / 500000000) := by
  have h := checkLog_sound (w := (344941 / 2344941)) (n := 12)
    (lo := (59270029 / 200000000)) (hi := (148175073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1344941 / 1000000) = 1/(1000000 / 1344941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (59270029 / 200000000) (148175073 / 500000000) (Real.log (1344941 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1344941 / 1000000) = -Real.log (1000000 / 1344941) := by
    rw [show ((1344941 / 1000000) : ℝ) = ((1000000 / 1344941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (423029971 / 1000000000) ≤ -Real.log (655059 / 1000000) ∧
    -Real.log (655059 / 1000000) ≤ (105757493 / 250000000) := by
  have h := checkLog_sound (w := (344941 / 1655059)) (n := 12)
    (lo := (423029971 / 1000000000)) (hi := (105757493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 655059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 655059) = 1/(655059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105757493 / 250000000) (-423029971 / 1000000000) (Real.log (655059 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (224644823 / 1000000000) ≤ -Real.log (500000 / 625939) ∧
    -Real.log (500000 / 625939) ≤ (28080603 / 125000000) := by
  have h := checkLog_sound (w := (125939 / 1125939)) (n := 12)
    (lo := (224644823 / 1000000000)) (hi := (28080603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625939 / 500000) = 1/(500000 / 625939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (224644823 / 1000000000) (28080603 / 125000000) (Real.log (625939 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (625939 / 500000) = -Real.log (500000 / 625939) := by
    rw [show ((625939 / 500000) : ℝ) = ((500000 / 625939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (72547303 / 250000000) ≤ -Real.log (374061 / 500000) ∧
    -Real.log (374061 / 500000) ≤ (290189213 / 1000000000) := by
  have h := checkLog_sound (w := (125939 / 874061)) (n := 12)
    (lo := (72547303 / 250000000)) (hi := (290189213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374061) = 1/(374061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-290189213 / 1000000000) (-72547303 / 250000000) (Real.log (374061 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (7028537 / 31250000) ≤ -Real.log (500000 / 626107) ∧
    -Real.log (500000 / 626107) ≤ (44982637 / 200000000) := by
  have h := checkLog_sound (w := (126107 / 1126107)) (n := 12)
    (lo := (7028537 / 31250000)) (hi := (44982637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626107 / 500000) = 1/(500000 / 626107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7028537 / 31250000) (44982637 / 200000000) (Real.log (626107 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (626107 / 500000) = -Real.log (500000 / 626107) := by
    rw [show ((626107 / 500000) : ℝ) = ((500000 / 626107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (145319219 / 500000000) ≤ -Real.log (373893 / 500000) ∧
    -Real.log (373893 / 500000) ≤ (290638439 / 1000000000) := by
  have h := checkLog_sound (w := (126107 / 873893)) (n := 12)
    (lo := (145319219 / 500000000)) (hi := (290638439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373893) = 1/(373893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-290638439 / 1000000000) (-145319219 / 500000000) (Real.log (373893 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (359202067 / 500000000) ≤ -Real.log (125000000000 / 256394653457) ∧
    -Real.log (125000000000 / 256394653457) ≤ (89800517 / 125000000) := by
  have h := checkLog_sound (w := (6394653457 / 506394653457)) (n := 12)
    (lo := (12628477 / 500000000)) (hi := (5051391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256394653457 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256394653457 / 250000000000) = 1/(125000000000 / 256394653457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (359202067 / 500000000) (89800517 / 125000000) (Real.log (256394653457 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (256394653457 / 125000000000) = -Real.log (125000000000 / 256394653457) := by
    rw [show ((256394653457 / 125000000000) : ℝ) = ((125000000000 / 256394653457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (179845029 / 250000000) ≤ -Real.log (100000000000 / 205316009703) ∧
    -Real.log (100000000000 / 205316009703) ≤ (359690059 / 500000000) := by
  have h := checkLog_sound (w := (5316009703 / 405316009703)) (n := 12)
    (lo := (3279117 / 125000000)) (hi := (26232937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205316009703 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(205316009703 / 200000000000) = 1/(100000000000 / 205316009703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (179845029 / 250000000) (359690059 / 500000000) (Real.log (205316009703 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (205316009703 / 100000000000) = -Real.log (100000000000 / 205316009703) := by
    rw [show ((205316009703 / 100000000000) : ℝ) = ((100000000000 / 205316009703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (128708509 / 250000000) ≤ -Real.log (500000000000 / 836680381007) ∧
    -Real.log (500000000000 / 836680381007) ≤ (514834037 / 1000000000) := by
  have h := checkLog_sound (w := (336680381007 / 1336680381007)) (n := 12)
    (lo := (128708509 / 250000000)) (hi := (514834037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836680381007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836680381007 / 500000000000) = 1/(500000000000 / 836680381007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (128708509 / 250000000) (514834037 / 1000000000) (Real.log (836680381007 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (836680381007 / 500000000000) = -Real.log (500000000000 / 836680381007) := by
    rw [show ((836680381007 / 500000000000) : ℝ) = ((500000000000 / 836680381007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (257775811 / 500000000) ≤ -Real.log (500000000000 / 837280986807) ∧
    -Real.log (500000000000 / 837280986807) ≤ (515551623 / 1000000000) := by
  have h := checkLog_sound (w := (337280986807 / 1337280986807)) (n := 12)
    (lo := (257775811 / 500000000)) (hi := (515551623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837280986807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837280986807 / 500000000000) = 1/(500000000000 / 837280986807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (257775811 / 500000000) (515551623 / 1000000000) (Real.log (837280986807 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (837280986807 / 500000000000) = -Real.log (500000000000 / 837280986807) := by
    rw [show ((837280986807 / 500000000000) : ℝ) = ((500000000000 / 837280986807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0333

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0334Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0334
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

theorem reflection_log_1_neg : (13495631 / 62500000) ≤ -Real.log (2560 / 3177) ∧
    -Real.log (2560 / 3177) ≤ (215930097 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 5737)) (n := 12)
    (lo := (13495631 / 62500000)) (hi := (215930097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3177 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3177 / 2560) = 1/(2560 / 3177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13495631 / 62500000) (215930097 / 1000000000) (Real.log (3177 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3177 / 2560) = -Real.log (2560 / 3177) := by
    rw [show ((3177 / 2560) : ℝ) = ((2560 / 3177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34471761 / 125000000) ≤ -Real.log (1943 / 2560) ∧
    -Real.log (1943 / 2560) ≤ (275774089 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 4503)) (n := 12)
    (lo := (34471761 / 125000000)) (hi := (275774089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1943) = 1/(1943 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-275774089 / 1000000000) (-34471761 / 125000000) (Real.log (1943 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (215693997 / 1000000000) ≤ -Real.log (2048 / 2541) ∧
    -Real.log (2048 / 2541) ≤ (107846999 / 500000000) := by
  have h := checkLog_sound (w := (493 / 4589)) (n := 12)
    (lo := (215693997 / 1000000000)) (hi := (107846999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2541 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2541 / 2048) = 1/(2048 / 2541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (215693997 / 1000000000) (107846999 / 500000000) (Real.log (2541 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2541 / 2048) = -Real.log (2048 / 2541) := by
    rw [show ((2541 / 2048) : ℝ) = ((2048 / 2541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (275388161 / 1000000000) ≤ -Real.log (1555 / 2048) ∧
    -Real.log (1555 / 2048) ≤ (137694081 / 500000000) := by
  have h := checkLog_sound (w := (493 / 3603)) (n := 12)
    (lo := (275388161 / 1000000000)) (hi := (137694081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1555) = 1/(1555 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-137694081 / 500000000) (-275388161 / 1000000000) (Real.log (1555 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (393413613 / 1000000000) ≤ -Real.log (1280 / 1897) ∧
    -Real.log (1280 / 1897) ≤ (196706807 / 500000000) := by
  have h := checkLog_sound (w := (617 / 3177)) (n := 12)
    (lo := (393413613 / 1000000000)) (hi := (196706807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1897 / 1280) = 1/(1280 / 1897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (393413613 / 1000000000) (196706807 / 500000000) (Real.log (1897 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1897 / 1280) = -Real.log (1280 / 1897) := by
    rw [show ((1897 / 1280) : ℝ) = ((1280 / 1897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (328920183 / 500000000) ≤ -Real.log (663 / 1280) ∧
    -Real.log (663 / 1280) ≤ (657840367 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 1943)) (n := 12)
    (lo := (328920183 / 500000000)) (hi := (657840367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 663) = 1/(663 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-657840367 / 1000000000) (-328920183 / 500000000) (Real.log (663 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (393018173 / 1000000000) ≤ -Real.log (1024 / 1517) ∧
    -Real.log (1024 / 1517) ≤ (196509087 / 500000000) := by
  have h := checkLog_sound (w := (493 / 2541)) (n := 12)
    (lo := (393018173 / 1000000000)) (hi := (196509087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1517 / 1024) = 1/(1024 / 1517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (393018173 / 1000000000) (196509087 / 500000000) (Real.log (1517 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1517 / 1024) = -Real.log (1024 / 1517) := by
    rw [show ((1517 / 1024) : ℝ) = ((1024 / 1517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (82088723 / 125000000) ≤ -Real.log (531 / 1024) ∧
    -Real.log (531 / 1024) ≤ (131341957 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1555)) (n := 12)
    (lo := (82088723 / 125000000)) (hi := (131341957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 531) = 1/(531 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-131341957 / 200000000) (-82088723 / 125000000) (Real.log (531 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (73927999 / 250000000) ≤ -Real.log (1000000 / 1344083) ∧
    -Real.log (1000000 / 1344083) ≤ (295711997 / 1000000000) := by
  have h := checkLog_sound (w := (344083 / 2344083)) (n := 12)
    (lo := (73927999 / 250000000)) (hi := (295711997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344083 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1344083 / 1000000) = 1/(1000000 / 1344083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (73927999 / 250000000) (295711997 / 1000000000) (Real.log (1344083 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1344083 / 1000000) = -Real.log (1000000 / 1344083) := by
    rw [show ((1344083 / 1000000) : ℝ) = ((1000000 / 1344083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (210860511 / 500000000) ≤ -Real.log (655917 / 1000000) ∧
    -Real.log (655917 / 1000000) ≤ (421721023 / 1000000000) := by
  have h := checkLog_sound (w := (344083 / 1655917)) (n := 12)
    (lo := (210860511 / 500000000)) (hi := (421721023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 655917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 655917) = 1/(655917 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-421721023 / 1000000000) (-210860511 / 500000000) (Real.log (655917 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (296031121 / 1000000000) ≤ -Real.log (15625 / 21008) ∧
    -Real.log (15625 / 21008) ≤ (148015561 / 500000000) := by
  have h := checkLog_sound (w := (5383 / 36633)) (n := 12)
    (lo := (296031121 / 1000000000)) (hi := (148015561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21008 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21008 / 15625) = 1/(15625 / 21008) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (296031121 / 1000000000) (148015561 / 500000000) (Real.log (21008 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (21008 / 15625) = -Real.log (15625 / 21008) := by
    rw [show ((21008 / 15625) : ℝ) = ((15625 / 21008) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (211187641 / 500000000) ≤ -Real.log (10242 / 15625) ∧
    -Real.log (10242 / 15625) ≤ (422375283 / 1000000000) := by
  have h := checkLog_sound (w := (5383 / 25867)) (n := 12)
    (lo := (211187641 / 500000000)) (hi := (422375283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10242) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10242) = 1/(10242 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-422375283 / 1000000000) (-211187641 / 500000000) (Real.log (10242 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (224377989 / 1000000000) ≤ -Real.log (125000 / 156443) ∧
    -Real.log (125000 / 156443) ≤ (22437799 / 100000000) := by
  have h := checkLog_sound (w := (31443 / 281443)) (n := 12)
    (lo := (224377989 / 1000000000)) (hi := (22437799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156443 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156443 / 125000) = 1/(125000 / 156443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (224377989 / 1000000000) (22437799 / 100000000) (Real.log (156443 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (156443 / 125000) = -Real.log (125000 / 156443) := by
    rw [show ((156443 / 125000) : ℝ) = ((125000 / 156443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (289742861 / 1000000000) ≤ -Real.log (93557 / 125000) ∧
    -Real.log (93557 / 125000) ≤ (144871431 / 500000000) := by
  have h := checkLog_sound (w := (31443 / 218557)) (n := 12)
    (lo := (289742861 / 1000000000)) (hi := (144871431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 93557) = 1/(93557 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144871431 / 500000000) (-289742861 / 1000000000) (Real.log (93557 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (112322811 / 500000000) ≤ -Real.log (1000000 / 1251879) ∧
    -Real.log (1000000 / 1251879) ≤ (224645623 / 1000000000) := by
  have h := checkLog_sound (w := (251879 / 2251879)) (n := 12)
    (lo := (112322811 / 500000000)) (hi := (224645623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251879 / 1000000) = 1/(1000000 / 1251879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (112322811 / 500000000) (224645623 / 1000000000) (Real.log (1251879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1251879 / 1000000) = -Real.log (1000000 / 1251879) := by
    rw [show ((1251879 / 1000000) : ℝ) = ((1000000 / 1251879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (290190549 / 1000000000) ≤ -Real.log (748121 / 1000000) ∧
    -Real.log (748121 / 1000000) ≤ (5803811 / 20000000) := by
  have h := checkLog_sound (w := (251879 / 1748121)) (n := 12)
    (lo := (290190549 / 1000000000)) (hi := (5803811 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748121) = 1/(748121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-5803811 / 20000000) (-290190549 / 1000000000) (Real.log (748121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (358716509 / 500000000) ≤ -Real.log (250000000000 / 512291570427) ∧
    -Real.log (250000000000 / 512291570427) ≤ (35871651 / 50000000) := by
  have h := checkLog_sound (w := (12291570427 / 1012291570427)) (n := 12)
    (lo := (12142919 / 500000000)) (hi := (24285839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512291570427 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512291570427 / 500000000000) = 1/(250000000000 / 512291570427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (358716509 / 500000000) (35871651 / 50000000) (Real.log (512291570427 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (512291570427 / 250000000000) = -Real.log (250000000000 / 512291570427) := by
    rw [show ((512291570427 / 250000000000) : ℝ) = ((250000000000 / 512291570427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (718406403 / 1000000000) ≤ -Real.log (500000000000 / 1025580941223) ∧
    -Real.log (500000000000 / 1025580941223) ≤ (143681281 / 200000000) := by
  have h := checkLog_sound (w := (25580941223 / 2025580941223)) (n := 12)
    (lo := (25259223 / 1000000000)) (hi := (3157403 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1025580941223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1025580941223 / 1000000000000) = 1/(500000000000 / 1025580941223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (718406403 / 1000000000) (143681281 / 200000000) (Real.log (1025580941223 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1025580941223 / 500000000000) = -Real.log (500000000000 / 1025580941223) := by
    rw [show ((1025580941223 / 500000000000) : ℝ) = ((500000000000 / 1025580941223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10282417 / 20000000) ≤ -Real.log (50000000000 / 83608388469) ∧
    -Real.log (50000000000 / 83608388469) ≤ (514120851 / 1000000000) := by
  have h := checkLog_sound (w := (33608388469 / 133608388469)) (n := 12)
    (lo := (10282417 / 20000000)) (hi := (514120851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83608388469 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83608388469 / 50000000000) = 1/(50000000000 / 83608388469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (10282417 / 20000000) (514120851 / 1000000000) (Real.log (83608388469 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (83608388469 / 50000000000) = -Real.log (50000000000 / 83608388469) := by
    rw [show ((83608388469 / 50000000000) : ℝ) = ((50000000000 / 83608388469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (128709043 / 250000000) ≤ -Real.log (20000000000 / 33467286709) ∧
    -Real.log (20000000000 / 33467286709) ≤ (514836173 / 1000000000) := by
  have h := checkLog_sound (w := (13467286709 / 53467286709)) (n := 12)
    (lo := (128709043 / 250000000)) (hi := (514836173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33467286709 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33467286709 / 20000000000) = 1/(20000000000 / 33467286709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (128709043 / 250000000) (514836173 / 1000000000) (Real.log (33467286709 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (33467286709 / 20000000000) = -Real.log (20000000000 / 33467286709) := by
    rw [show ((33467286709 / 20000000000) : ℝ) = ((20000000000 / 33467286709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0334

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0335Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0335
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

theorem reflection_log_1_neg : (215693997 / 1000000000) ≤ -Real.log (2048 / 2541) ∧
    -Real.log (2048 / 2541) ≤ (107846999 / 500000000) := by
  have h := checkLog_sound (w := (493 / 4589)) (n := 12)
    (lo := (215693997 / 1000000000)) (hi := (107846999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2541 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2541 / 2048) = 1/(2048 / 2541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (215693997 / 1000000000) (107846999 / 500000000) (Real.log (2541 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2541 / 2048) = -Real.log (2048 / 2541) := by
    rw [show ((2541 / 2048) : ℝ) = ((2048 / 2541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (275388161 / 1000000000) ≤ -Real.log (1555 / 2048) ∧
    -Real.log (1555 / 2048) ≤ (137694081 / 500000000) := by
  have h := checkLog_sound (w := (493 / 3603)) (n := 12)
    (lo := (275388161 / 1000000000)) (hi := (137694081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1555) = 1/(1555 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-137694081 / 500000000) (-275388161 / 1000000000) (Real.log (1555 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (215457841 / 1000000000) ≤ -Real.log (5120 / 6351) ∧
    -Real.log (5120 / 6351) ≤ (107728921 / 500000000) := by
  have h := checkLog_sound (w := (1231 / 11471)) (n := 12)
    (lo := (215457841 / 1000000000)) (hi := (107728921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6351 / 5120) = 1/(5120 / 6351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (215457841 / 1000000000) (107728921 / 500000000) (Real.log (6351 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6351 / 5120) = -Real.log (5120 / 6351) := by
    rw [show ((6351 / 5120) : ℝ) = ((5120 / 6351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (275002383 / 1000000000) ≤ -Real.log (3889 / 5120) ∧
    -Real.log (3889 / 5120) ≤ (17187649 / 62500000) := by
  have h := checkLog_sound (w := (1231 / 9009)) (n := 12)
    (lo := (275002383 / 1000000000)) (hi := (17187649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3889) = 1/(3889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-17187649 / 62500000) (-275002383 / 1000000000) (Real.log (3889 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (393018173 / 1000000000) ≤ -Real.log (1024 / 1517) ∧
    -Real.log (1024 / 1517) ≤ (196509087 / 500000000) := by
  have h := checkLog_sound (w := (493 / 2541)) (n := 12)
    (lo := (393018173 / 1000000000)) (hi := (196509087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1517 / 1024) = 1/(1024 / 1517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (393018173 / 1000000000) (196509087 / 500000000) (Real.log (1517 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1517 / 1024) = -Real.log (1024 / 1517) := by
    rw [show ((1517 / 1024) : ℝ) = ((1024 / 1517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (82088723 / 125000000) ≤ -Real.log (531 / 1024) ∧
    -Real.log (531 / 1024) ≤ (131341957 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1555)) (n := 12)
    (lo := (82088723 / 125000000)) (hi := (131341957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 531) = 1/(531 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-131341957 / 200000000) (-82088723 / 125000000) (Real.log (531 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (196311289 / 500000000) ≤ -Real.log (2560 / 3791) ∧
    -Real.log (2560 / 3791) ≤ (392622579 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 6351)) (n := 12)
    (lo := (196311289 / 500000000)) (hi := (392622579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3791 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3791 / 2560) = 1/(2560 / 3791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (196311289 / 500000000) (392622579 / 1000000000) (Real.log (3791 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3791 / 2560) = -Real.log (2560 / 3791) := by
    rw [show ((3791 / 2560) : ℝ) = ((2560 / 3791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (327790239 / 500000000) ≤ -Real.log (1329 / 2560) ∧
    -Real.log (1329 / 2560) ≤ (655580479 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 3889)) (n := 12)
    (lo := (327790239 / 500000000)) (hi := (655580479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1329) = 1/(1329 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-655580479 / 1000000000) (-327790239 / 500000000) (Real.log (1329 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (576939 / 1953125) ≤ -Real.log (500000 / 671827) ∧
    -Real.log (500000 / 671827) ≤ (295392769 / 1000000000) := by
  have h := checkLog_sound (w := (171827 / 1171827)) (n := 12)
    (lo := (576939 / 1953125)) (hi := (295392769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671827 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671827 / 500000) = 1/(500000 / 671827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (576939 / 1953125) (295392769 / 1000000000) (Real.log (671827 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (671827 / 500000) = -Real.log (500000 / 671827) := by
    rw [show ((671827 / 500000) : ℝ) = ((500000 / 671827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42106719 / 100000000) ≤ -Real.log (328173 / 500000) ∧
    -Real.log (328173 / 500000) ≤ (421067191 / 1000000000) := by
  have h := checkLog_sound (w := (171827 / 828173)) (n := 12)
    (lo := (42106719 / 100000000)) (hi := (421067191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328173) = 1/(328173 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-421067191 / 1000000000) (-42106719 / 100000000) (Real.log (328173 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (14785637 / 50000000) ≤ -Real.log (250000 / 336021) ∧
    -Real.log (250000 / 336021) ≤ (295712741 / 1000000000) := by
  have h := checkLog_sound (w := (86021 / 586021)) (n := 12)
    (lo := (14785637 / 50000000)) (hi := (295712741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336021 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336021 / 250000) = 1/(250000 / 336021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (14785637 / 50000000) (295712741 / 1000000000) (Real.log (336021 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (336021 / 250000) = -Real.log (250000 / 336021) := by
    rw [show ((336021 / 250000) : ℝ) = ((250000 / 336021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (421722547 / 1000000000) ≤ -Real.log (163979 / 250000) ∧
    -Real.log (163979 / 250000) ≤ (105430637 / 250000000) := by
  have h := checkLog_sound (w := (86021 / 413979)) (n := 12)
    (lo := (421722547 / 1000000000)) (hi := (105430637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163979) = 1/(163979 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105430637 / 250000000) (-421722547 / 1000000000) (Real.log (163979 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (224110283 / 1000000000) ≤ -Real.log (1000000 / 1251209) ∧
    -Real.log (1000000 / 1251209) ≤ (56027571 / 250000000) := by
  have h := checkLog_sound (w := (251209 / 2251209)) (n := 12)
    (lo := (224110283 / 1000000000)) (hi := (56027571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251209 / 1000000) = 1/(1000000 / 1251209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (224110283 / 1000000000) (56027571 / 250000000) (Real.log (1251209 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1251209 / 1000000) = -Real.log (1000000 / 1251209) := by
    rw [show ((1251209 / 1000000) : ℝ) = ((1000000 / 1251209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (289295373 / 1000000000) ≤ -Real.log (748791 / 1000000) ∧
    -Real.log (748791 / 1000000) ≤ (144647687 / 500000000) := by
  have h := checkLog_sound (w := (251209 / 1748791)) (n := 12)
    (lo := (289295373 / 1000000000)) (hi := (144647687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748791) = 1/(748791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144647687 / 500000000) (-289295373 / 1000000000) (Real.log (748791 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (56094697 / 250000000) ≤ -Real.log (200000 / 250309) ∧
    -Real.log (200000 / 250309) ≤ (224378789 / 1000000000) := by
  have h := checkLog_sound (w := (50309 / 450309)) (n := 12)
    (lo := (56094697 / 250000000)) (hi := (224378789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250309 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250309 / 200000) = 1/(200000 / 250309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56094697 / 250000000) (224378789 / 1000000000) (Real.log (250309 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (250309 / 200000) = -Real.log (200000 / 250309) := by
    rw [show ((250309 / 200000) : ℝ) = ((200000 / 250309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (289744197 / 1000000000) ≤ -Real.log (149691 / 200000) ∧
    -Real.log (149691 / 200000) ≤ (144872099 / 500000000) := by
  have h := checkLog_sound (w := (50309 / 349691)) (n := 12)
    (lo := (289744197 / 1000000000)) (hi := (144872099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149691) = 1/(149691 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-144872099 / 500000000) (-289744197 / 1000000000) (Real.log (149691 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (716459957 / 1000000000) ≤ -Real.log (31250000000 / 63974165303) ∧
    -Real.log (31250000000 / 63974165303) ≤ (716459959 / 1000000000) := by
  have h := checkLog_sound (w := (1474165303 / 126474165303)) (n := 12)
    (lo := (23312777 / 1000000000)) (hi := (11656389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63974165303 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63974165303 / 62500000000) = 1/(31250000000 / 63974165303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (716459957 / 1000000000) (716459959 / 1000000000) (Real.log (63974165303 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (63974165303 / 31250000000) = -Real.log (31250000000 / 63974165303) := by
    rw [show ((63974165303 / 31250000000) : ℝ) = ((31250000000 / 63974165303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (358717643 / 500000000) ≤ -Real.log (500000000000 / 1024585465213) ∧
    -Real.log (500000000000 / 1024585465213) ≤ (89679411 / 125000000) := by
  have h := checkLog_sound (w := (24585465213 / 2024585465213)) (n := 12)
    (lo := (12144053 / 500000000)) (hi := (24288107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024585465213 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1024585465213 / 1000000000000) = 1/(500000000000 / 1024585465213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (358717643 / 500000000) (89679411 / 125000000) (Real.log (1024585465213 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1024585465213 / 500000000000) = -Real.log (500000000000 / 1024585465213) := by
    rw [show ((1024585465213 / 500000000000) : ℝ) = ((500000000000 / 1024585465213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (64175707 / 125000000) ≤ -Real.log (250000000000 / 417743068493) ∧
    -Real.log (250000000000 / 417743068493) ≤ (513405657 / 1000000000) := by
  have h := checkLog_sound (w := (167743068493 / 667743068493)) (n := 12)
    (lo := (64175707 / 125000000)) (hi := (513405657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417743068493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417743068493 / 250000000000) = 1/(250000000000 / 417743068493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (64175707 / 125000000) (513405657 / 1000000000) (Real.log (417743068493 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (417743068493 / 250000000000) = -Real.log (250000000000 / 417743068493) := by
    rw [show ((417743068493 / 250000000000) : ℝ) = ((250000000000 / 417743068493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (102824597 / 200000000) ≤ -Real.log (250000000000 / 418042834907) ∧
    -Real.log (250000000000 / 418042834907) ≤ (257061493 / 500000000) := by
  have h := checkLog_sound (w := (168042834907 / 668042834907)) (n := 12)
    (lo := (102824597 / 200000000)) (hi := (257061493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418042834907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418042834907 / 250000000000) = 1/(250000000000 / 418042834907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (102824597 / 200000000) (257061493 / 500000000) (Real.log (418042834907 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (418042834907 / 250000000000) = -Real.log (250000000000 / 418042834907) := by
    rw [show ((418042834907 / 250000000000) : ℝ) = ((250000000000 / 418042834907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0335

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0336Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0336
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

theorem reflection_log_1_neg : (215457841 / 1000000000) ≤ -Real.log (5120 / 6351) ∧
    -Real.log (5120 / 6351) ≤ (107728921 / 500000000) := by
  have h := checkLog_sound (w := (1231 / 11471)) (n := 12)
    (lo := (215457841 / 1000000000)) (hi := (107728921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6351 / 5120) = 1/(5120 / 6351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (215457841 / 1000000000) (107728921 / 500000000) (Real.log (6351 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6351 / 5120) = -Real.log (5120 / 6351) := by
    rw [show ((6351 / 5120) : ℝ) = ((5120 / 6351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (275002383 / 1000000000) ≤ -Real.log (3889 / 5120) ∧
    -Real.log (3889 / 5120) ≤ (17187649 / 62500000) := by
  have h := checkLog_sound (w := (1231 / 9009)) (n := 12)
    (lo := (275002383 / 1000000000)) (hi := (17187649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3889) = 1/(3889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-17187649 / 62500000) (-275002383 / 1000000000) (Real.log (3889 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21522163 / 100000000) ≤ -Real.log (10240 / 12699) ∧
    -Real.log (10240 / 12699) ≤ (215221631 / 1000000000) := by
  have h := checkLog_sound (w := (2459 / 22939)) (n := 12)
    (lo := (21522163 / 100000000)) (hi := (215221631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12699 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12699 / 10240) = 1/(10240 / 12699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21522163 / 100000000) (215221631 / 1000000000) (Real.log (12699 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12699 / 10240) = -Real.log (10240 / 12699) := by
    rw [show ((12699 / 10240) : ℝ) = ((10240 / 12699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (137308377 / 500000000) ≤ -Real.log (7781 / 10240) ∧
    -Real.log (7781 / 10240) ≤ (54923351 / 200000000) := by
  have h := checkLog_sound (w := (2459 / 18021)) (n := 12)
    (lo := (137308377 / 500000000)) (hi := (54923351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7781) = 1/(7781 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-54923351 / 200000000) (-137308377 / 500000000) (Real.log (7781 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (196311289 / 500000000) ≤ -Real.log (2560 / 3791) ∧
    -Real.log (2560 / 3791) ≤ (392622579 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 6351)) (n := 12)
    (lo := (196311289 / 500000000)) (hi := (392622579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3791 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3791 / 2560) = 1/(2560 / 3791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (196311289 / 500000000) (392622579 / 1000000000) (Real.log (3791 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3791 / 2560) = -Real.log (2560 / 3791) := by
    rw [show ((3791 / 2560) : ℝ) = ((2560 / 3791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (327790239 / 500000000) ≤ -Real.log (1329 / 2560) ∧
    -Real.log (1329 / 2560) ≤ (655580479 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 3889)) (n := 12)
    (lo := (327790239 / 500000000)) (hi := (655580479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1329) = 1/(1329 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-655580479 / 1000000000) (-327790239 / 500000000) (Real.log (1329 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15689073 / 40000000) ≤ -Real.log (5120 / 7579) ∧
    -Real.log (5120 / 7579) ≤ (196113413 / 500000000) := by
  have h := checkLog_sound (w := (2459 / 12699)) (n := 12)
    (lo := (15689073 / 40000000)) (hi := (196113413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7579 / 5120) = 1/(5120 / 7579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15689073 / 40000000) (196113413 / 500000000) (Real.log (7579 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7579 / 5120) = -Real.log (5120 / 7579) := by
    rw [show ((7579 / 5120) : ℝ) = ((5120 / 7579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (654452447 / 1000000000) ≤ -Real.log (2661 / 5120) ∧
    -Real.log (2661 / 5120) ≤ (20451639 / 31250000) := by
  have h := checkLog_sound (w := (2459 / 7781)) (n := 12)
    (lo := (654452447 / 1000000000)) (hi := (20451639 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2661) = 1/(2661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20451639 / 31250000) (-654452447 / 1000000000) (Real.log (2661 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (147536719 / 500000000) ≤ -Real.log (40000 / 53729) ∧
    -Real.log (40000 / 53729) ≤ (295073439 / 1000000000) := by
  have h := checkLog_sound (w := (13729 / 93729)) (n := 12)
    (lo := (147536719 / 500000000)) (hi := (295073439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53729 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53729 / 40000) = 1/(40000 / 53729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (147536719 / 500000000) (295073439 / 1000000000) (Real.log (53729 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (53729 / 40000) = -Real.log (40000 / 53729) := by
    rw [show ((53729 / 40000) : ℝ) = ((40000 / 53729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52551723 / 125000000) ≤ -Real.log (26271 / 40000) ∧
    -Real.log (26271 / 40000) ≤ (84082757 / 200000000) := by
  have h := checkLog_sound (w := (13729 / 66271)) (n := 12)
    (lo := (52551723 / 125000000)) (hi := (84082757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26271) = 1/(26271 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-84082757 / 200000000) (-52551723 / 125000000) (Real.log (26271 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36924189 / 125000000) ≤ -Real.log (200000 / 268731) ∧
    -Real.log (200000 / 268731) ≤ (295393513 / 1000000000) := by
  have h := checkLog_sound (w := (68731 / 468731)) (n := 12)
    (lo := (36924189 / 125000000)) (hi := (295393513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268731 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268731 / 200000) = 1/(200000 / 268731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36924189 / 125000000) (295393513 / 1000000000) (Real.log (268731 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (268731 / 200000) = -Real.log (200000 / 268731) := by
    rw [show ((268731 / 200000) : ℝ) = ((200000 / 268731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (421068713 / 1000000000) ≤ -Real.log (131269 / 200000) ∧
    -Real.log (131269 / 200000) ≤ (210534357 / 500000000) := by
  have h := checkLog_sound (w := (68731 / 331269)) (n := 12)
    (lo := (421068713 / 1000000000)) (hi := (210534357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 131269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 131269) = 1/(131269 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210534357 / 500000000) (-421068713 / 1000000000) (Real.log (131269 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (111921653 / 500000000) ≤ -Real.log (8000 / 10007) ∧
    -Real.log (8000 / 10007) ≤ (223843307 / 1000000000) := by
  have h := checkLog_sound (w := (2007 / 18007)) (n := 12)
    (lo := (111921653 / 500000000)) (hi := (223843307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10007 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10007 / 8000) = 1/(8000 / 10007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (111921653 / 500000000) (223843307 / 1000000000) (Real.log (10007 / 8000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (10007 / 8000) = -Real.log (8000 / 10007) := by
    rw [show ((10007 / 8000) : ℝ) = ((8000 / 10007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (14442471 / 50000000) ≤ -Real.log (5993 / 8000) ∧
    -Real.log (5993 / 8000) ≤ (288849421 / 1000000000) := by
  have h := checkLog_sound (w := (2007 / 13993)) (n := 12)
    (lo := (14442471 / 50000000)) (hi := (288849421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5993) = 1/(5993 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-288849421 / 1000000000) (-14442471 / 50000000) (Real.log (5993 / 8000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (224111083 / 1000000000) ≤ -Real.log (100000 / 125121) ∧
    -Real.log (100000 / 125121) ≤ (56027771 / 250000000) := by
  have h := checkLog_sound (w := (25121 / 225121)) (n := 12)
    (lo := (224111083 / 1000000000)) (hi := (56027771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125121 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125121 / 100000) = 1/(100000 / 125121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (224111083 / 1000000000) (56027771 / 250000000) (Real.log (125121 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (125121 / 100000) = -Real.log (100000 / 125121) := by
    rw [show ((125121 / 100000) : ℝ) = ((100000 / 125121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (72324177 / 250000000) ≤ -Real.log (74879 / 100000) ∧
    -Real.log (74879 / 100000) ≤ (289296709 / 1000000000) := by
  have h := checkLog_sound (w := (25121 / 174879)) (n := 12)
    (lo := (72324177 / 250000000)) (hi := (289296709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74879) = 1/(74879 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-289296709 / 1000000000) (-72324177 / 250000000) (Real.log (74879 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (715487223 / 1000000000) ≤ -Real.log (500000000000 / 1022591450649) ∧
    -Real.log (500000000000 / 1022591450649) ≤ (28619489 / 40000000) := by
  have h := checkLog_sound (w := (22591450649 / 2022591450649)) (n := 12)
    (lo := (22340043 / 1000000000)) (hi := (5585011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022591450649 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1022591450649 / 1000000000000) = 1/(500000000000 / 1022591450649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (715487223 / 1000000000) (28619489 / 40000000) (Real.log (1022591450649 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1022591450649 / 500000000000) = -Real.log (500000000000 / 1022591450649) := by
    rw [show ((1022591450649 / 500000000000) : ℝ) = ((500000000000 / 1022591450649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (28658489 / 40000000) ≤ -Real.log (500000000000 / 1023588966169) ∧
    -Real.log (500000000000 / 1023588966169) ≤ (716462227 / 1000000000) := by
  have h := checkLog_sound (w := (23588966169 / 2023588966169)) (n := 12)
    (lo := (4663009 / 200000000)) (hi := (11657523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1023588966169 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1023588966169 / 1000000000000) = 1/(500000000000 / 1023588966169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (28658489 / 40000000) (716462227 / 1000000000) (Real.log (1023588966169 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1023588966169 / 500000000000) = -Real.log (500000000000 / 1023588966169) := by
    rw [show ((1023588966169 / 500000000000) : ℝ) = ((500000000000 / 1023588966169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (256346363 / 500000000) ≤ -Real.log (500000000000 / 834890705823) ∧
    -Real.log (500000000000 / 834890705823) ≤ (512692727 / 1000000000) := by
  have h := checkLog_sound (w := (334890705823 / 1334890705823)) (n := 12)
    (lo := (256346363 / 500000000)) (hi := (512692727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834890705823 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834890705823 / 500000000000) = 1/(500000000000 / 834890705823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (256346363 / 500000000) (512692727 / 1000000000) (Real.log (834890705823 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (834890705823 / 500000000000) = -Real.log (500000000000 / 834890705823) := by
    rw [show ((834890705823 / 500000000000) : ℝ) = ((500000000000 / 834890705823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (513407791 / 1000000000) ≤ -Real.log (3906250000 / 6527249379) ∧
    -Real.log (3906250000 / 6527249379) ≤ (32087987 / 62500000) := by
  have h := checkLog_sound (w := (2620999379 / 10433499379)) (n := 12)
    (lo := (513407791 / 1000000000)) (hi := (32087987 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6527249379 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6527249379 / 3906250000) = 1/(3906250000 / 6527249379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (513407791 / 1000000000) (32087987 / 62500000) (Real.log (6527249379 / 3906250000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6527249379 / 3906250000) = -Real.log (3906250000 / 6527249379) := by
    rw [show ((6527249379 / 3906250000) : ℝ) = ((3906250000 / 6527249379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0336

end


