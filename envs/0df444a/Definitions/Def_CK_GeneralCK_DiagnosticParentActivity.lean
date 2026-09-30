-- Prove2me | Definitions.Def_CK_GeneralCK_DiagnosticParentActivity
-- name    : CK_GeneralCK_DiagnosticParentActivity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:18:21.364755+00:00
-- url     : https://prove2.me/theorems/0490fcc0-cb91-4602-88e0-ba0363f62280
-- title:
--   Courtade–Kumar proof module `GeneralCK.DiagnosticParentActivity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.DiagnosticParentActivity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.DiagnosticParentActivity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.DiagnosticParentActivity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/DiagnosticParentActivity.lean)

import Definitions.Def_CK_GeneralCK_LeftStationaryHybridReplacement
import Definitions.Def_CK_GeneralCK_PureGapZeroCapRightRadialTangentBound
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy2048

-- ===== source module GeneralCK.DiagnosticParentActivity =====
section

/-!
# Uniform hybrid-parent activity on the negative pure-gap diagnostic interval

Only rational anchors and integer-power logarithm comparisons are used. The
actual parent satisfies phi <= 4e-12 and psi >= 5e-12 throughout the interval.
No external numerical receipt is a premise.
-/

namespace GeneralCK.LeftStationaryDiagnosticActivity

open Set Certificates.Mixed

noncomputable def leftAnchor : ℝ := 1 / 500000000000000
noncomputable def contactAnchor : ℝ := 11 / 1000000000000000
noncomputable def meanLower : ℝ := 1 / 25000000000000
noncomputable def meanUpper : ℝ := 51 / 1000000000000000
noncomputable def parentEntropy : ℝ := 11 / 20000000000000

private theorem log_two_bounds : (69 / 100 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (7 / 10 : ℝ) := by
  have h := Certificates.PilotData.log_two
  norm_num at h
  constructor <;> linarith

private theorem entropy_times_log_lower {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) :
    p * (-Real.log p) + p * (1 - p) ≤ H p * Real.log 2 := by
  have hc : 0 < 1 - p := by linarith
  have hl : p ≤ -Real.log (1 - p) := by
    linarith [Real.log_le_sub_one_of_pos hc]
  have hm := mul_le_mul_of_nonneg_left hl hc.le
  have hid : H p * Real.log 2 =
      p * (-Real.log p) + (1 - p) * (-Real.log (1 - p)) := by
    rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy,
      Real.log_inv, Real.log_inv]
  rw [hid]
  nlinarith only [hm]

theorem entropy_leftAnchor_lower :
    (1 / 10000000000000 : ℝ) ≤ H leftAnchor := by
  have hpow : (2 : ℝ) ^ (195 : ℕ) ≤ (500000000000000 : ℝ) ^ (4 : ℕ) := by
    norm_num
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (195 : ℕ)) hpow
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have hlog : (195 / 4 : ℝ) * Real.log 2 ≤ -Real.log leftAnchor := by
    rw [leftAnchor, show (1 / 500000000000000 : ℝ) =
      (500000000000000 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith only [hl]
  have hm := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ leftAnchor by norm_num [leftAnchor])
  have hb := entropy_times_log_lower
    (p := leftAnchor) (by norm_num [leftAnchor]) (by norm_num [leftAnchor])
  apply (mul_le_mul_iff_right₀ log_two_pos).mp
  dsimp [leftAnchor] at hm hb ⊢
  nlinarith only [hm, hb, log_two_bounds.2]

theorem inverse_left_upper : entropyInverse (1 / 10000000000000) ≤ leftAnchor := by
  have hm := entropyInverse_mono (by norm_num : (0 : ℝ) ≤ 1 / 10000000000000)
    (H_le_one leftAnchor) entropy_leftAnchor_lower
  rwa [entropyInverse_H_lower (by norm_num [leftAnchor])
    (by norm_num [leftAnchor])] at hm

private theorem contactAnchor_log_upper :
    Real.log contactAnchor⁻¹ ≤ 47 * Real.log 2 := by
  have hm := Real.log_le_log (by norm_num [contactAnchor] : (0 : ℝ) < contactAnchor⁻¹)
    (show contactAnchor⁻¹ ≤ (2 : ℝ) ^ (47 : ℕ) by norm_num [contactAnchor])
  rw [Real.log_pow] at hm
  norm_num at hm
  simpa only [Real.log_inv] using hm

theorem entropy_contactAnchor_upper : H contactAnchor ≤ parentEntropy := by
  have h := PsiOuterEntropy2048.entropy_logit_upper
    (p := contactAnchor) (n := 47) (by norm_num [contactAnchor])
    (by norm_num [contactAnchor]) contactAnchor_log_upper
  dsimp [contactAnchor, parentEntropy] at h ⊢
  linarith only [h.1]

theorem inverse_parent_lower : contactAnchor ≤ entropyInverse parentEntropy := by
  have hm := entropyInverse_mono
    (H_nonneg (by norm_num [contactAnchor]) (by norm_num [contactAnchor]))
    (by norm_num [parentEntropy] : parentEntropy ≤ 1) entropy_contactAnchor_upper
  rwa [entropyInverse_H_lower (by norm_num [contactAnchor])
    (by norm_num [contactAnchor])] at hm

private theorem kap_contactAnchor_lower : (15 : ℝ) ≤ kap contactAnchor := by
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (44 : ℕ))
    (show (2 : ℝ) ^ (44 : ℕ) ≤ contactAnchor⁻¹ by norm_num [contactAnchor])
  rw [Real.log_pow, Real.log_inv] at hm
  norm_num at hm
  have hc : 0 < 1 - contactAnchor := by norm_num [contactAnchor]
  have hl : 0 ≤ -Real.log (1 - contactAnchor) := by
    have h := Real.log_le_sub_one_of_pos hc
    norm_num [contactAnchor] at h ⊢
    linarith
  have hid : kap contactAnchor =
      (-Real.log contactAnchor - Real.log (1 - contactAnchor)) / 2 := by
    rw [kap, Real.log_mul (by norm_num [contactAnchor]) hc.ne']
    ring
  rw [hid]
  linarith only [hm, hl, log_two_bounds.1]

private theorem radialSlope_formula {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    radialSlope v = J v + (1 - 2 * v) * H v / (2 * v * (1 - v) * kap v) := by
  unfold radialSlope
  rw [hn_eq_H_mul_log]
  field_simp [log_two_pos.ne', hv.ne', (show 1 - v ≠ 0 by linarith),
    (kap_pos hv hv').ne']

theorem radialSlope_contactAnchor_upper : radialSlope contactAnchor ≤ (50 : ℝ) := by
  have hv : 0 < contactAnchor := by norm_num [contactAnchor]
  have hv' : contactAnchor < 1 / 2 := by norm_num [contactAnchor]
  have hJ := (PsiOuterEntropy2048.entropy_logit_upper hv (by linarith)
    contactAnchor_log_upper).2
  have hd : 0 < 2 * contactAnchor * (1 - contactAnchor) * kap contactAnchor := by
    have hk := kap_pos hv hv'
    have hc : 0 < 1 - contactAnchor := by linarith
    positivity
  have hpart : (1 - 2 * contactAnchor) * H contactAnchor /
      (2 * contactAnchor * (1 - contactAnchor) * kap contactAnchor) ≤ 3 := by
    apply (div_le_iff₀ hd).mpr
    have hH := entropy_contactAnchor_upper
    have hk := kap_contactAnchor_lower
    dsimp [contactAnchor, parentEntropy] at hH hk ⊢
    nlinarith only [hH, hk]
  rw [radialSlope_formula hv hv']
  linarith only [hJ, hpart]

theorem entropy_meanLower_lower : (9 / 5000000000000 : ℝ) ≤ H meanLower := by
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (44 : ℕ))
    (show (2 : ℝ) ^ (44 : ℕ) ≤ meanLower⁻¹ by norm_num [meanLower])
  rw [Real.log_pow, Real.log_inv] at hm
  norm_num at hm
  have hmul := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ meanLower by norm_num [meanLower])
  have hb := entropy_times_log_lower
    (p := meanLower) (by norm_num [meanLower]) (by norm_num [meanLower])
  apply (mul_le_mul_iff_right₀ log_two_pos).mp
  dsimp [meanLower] at hmul hb ⊢
  nlinarith only [hmul, hb, log_two_bounds.2]

theorem parent_phi_upper {m : ℝ} (hm : meanLower ≤ m) (hm' : m ≤ meanUpper) :
    phi m parentEntropy ≤ (1 / 250000000000 : ℝ) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num [meanLower]) hm
  have hmhalf : m < 1 / 2 := lt_of_le_of_lt hm' (by norm_num [meanUpper])
  have hE : 0 < parentEntropy := by norm_num [parentEntropy]
  have hE1 : parentEntropy < 1 := by norm_num [parentEntropy]
  have hHlo : (9 / 5000000000000 : ℝ) ≤ H m := entropy_meanLower_lower.trans
    (H_strictMonoOn.monotoneOn ⟨by norm_num [meanLower], by norm_num [meanLower]⟩
      ⟨hm0.le, hmhalf.le⟩ hm)
  have hcap : parentEntropy ≤ H m := by dsimp [parentEntropy]; linarith
  let q := entropyInverse parentEntropy
  have hq : 0 < q := entropyInverse_pos hE hE1.le
  have hqhalf : q < 1 / 2 := entropyInverse_lt_half hE.le hE1
  have hqH : H q = parentEntropy := (entropyInverse_spec hE.le hE1.le).2.2
  have hqm : q ≤ m := by
    have h := entropyInverse_mono hE.le (H_le_one m) hcap
    rwa [entropyInverse_H_lower hm0.le hmhalf.le] at h
  have hqlo : contactAnchor ≤ q := inverse_parent_lower
  have hslope : radialSlope q ≤ 50 :=
    (ZeroCapLeftStationaryThetaBracket.radialSlope_antitone
      ⟨by norm_num [contactAnchor], by norm_num [contactAnchor]⟩
      ⟨hq, hqhalf⟩ hqlo).trans radialSlope_contactAnchor_upper
  have hs : 0 < 1 - 2 * q := by linarith
  have hcontact : radialContact (1 - 2 * q) parentEntropy = q := by
    rw [← hqH]
    exact radialContact_H_lower hq hqhalf
  have hFcap : F (1 - 2 * q) parentEntropy = eta parentEntropy := by
    rw [F, if_neg hs.ne', hcontact, eta_eq_profile hE.le hE1.le]
  have ht := rightCap_F_supporting_tangent
    (r := 1 - 2 * m) (s := 1 - 2 * q) (h := parentEntropy)
    (by linarith) hs hE
  rw [hFcap, hcontact] at ht
  have hmul := mul_le_mul_of_nonneg_left hslope
    (show 0 ≤ (1 - 2 * q) - (1 - 2 * m) by linarith)
  unfold phi
  rw [abs_of_pos (by linarith : 0 < 1 - 2 * m)]
  dsimp [contactAnchor] at hqlo
  dsimp [meanUpper] at hm'
  nlinarith only [ht, hmul, hqlo, hm']

theorem parent_psi_lower {m : ℝ} (hm : meanLower ≤ m) (hm' : m ≤ meanUpper) :
    (1 / 200000000000 : ℝ) ≤ psi m parentEntropy := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num [meanLower]) hm
  have hmhalf : m < 1 / 2 := lt_of_le_of_lt hm' (by norm_num [meanUpper])
  have hHlo : (9 / 5000000000000 : ℝ) ≤ H m := entropy_meanLower_lower.trans
    (H_strictMonoOn.monotoneOn ⟨by norm_num [meanLower], by norm_num [meanLower]⟩
      ⟨hm0.le, hmhalf.le⟩ hm)
  have hI : 0 ≤ H m - parentEntropy := by dsimp [parentEntropy]; linarith
  have hI1 : H m - parentEntropy < 1 := by
    have h := H_le_one m
    dsimp [parentEntropy]
    linarith
  have h := Scalar.four_mul_le_P hI hI1
  rw [← psi_eq_P m parentEntropy] at h
  dsimp [parentEntropy] at h ⊢
  linarith only [h, hHlo]

theorem parent_activity_margin {m : ℝ} (hm : meanLower ≤ m) (hm' : m ≤ meanUpper) :
    phi m parentEntropy + 1 / 1000000000000 ≤ psi m parentEntropy := by
  linarith only [parent_phi_upper hm hm', parent_psi_lower hm hm']

theorem diagnosticParentActivity : LeftStationaryHybridReplacement.DiagnosticParentActivity := by
  intro c hc
  have ha0 : 0 ≤ entropyInverse (1 / 10000000000000) :=
    (entropyInverse_spec (by norm_num) (by norm_num)).1
  have ha1 := inverse_left_upper
  have hm : meanLower ≤ (entropyInverse (1 / 10000000000000) + c) / 2 := by
    dsimp [meanLower]
    linarith only [hc.1, ha0]
  have hm' : (entropyInverse (1 / 10000000000000) + c) / 2 ≤ meanUpper := by
    dsimp [meanUpper, leftAnchor] at *
    linarith only [hc.2, ha1]
  have h := parent_activity_margin hm hm'
  change phi _ parentEntropy ≤ psi _ parentEntropy
  linarith only [h]

/-- Unconditional hybrid Bellman inequality for every realizing finite law
on the complete interval containing the negative stationary pure-gap point. -/
theorem diagnosticHybridOwner : LeftStationaryHybridReplacement.DiagnosticHybridOwner :=
  LeftStationaryHybridReplacement.diagnosticHybridOwner_of_parentActivity diagnosticParentActivity

#print axioms entropy_leftAnchor_lower
#print axioms inverse_left_upper
#print axioms entropy_contactAnchor_upper
#print axioms inverse_parent_lower
#print axioms radialSlope_contactAnchor_upper
#print axioms entropy_meanLower_lower
#print axioms parent_phi_upper
#print axioms parent_psi_lower
#print axioms parent_activity_margin
#print axioms diagnosticParentActivity
#print axioms diagnosticHybridOwner

end GeneralCK.LeftStationaryDiagnosticActivity

end


