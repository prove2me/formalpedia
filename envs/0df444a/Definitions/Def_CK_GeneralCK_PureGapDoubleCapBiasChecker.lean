-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker
-- name    : CK_GeneralCK_PureGapDoubleCapBiasChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:52:59.510804+00:00
-- url     : https://prove2.me/theorems/434c4dce-5d31-4fc7-a4c4-3ebcea7ece09
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapBiasChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapBiasChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapBiasChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapBiasChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapBiasChecker.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapSlopeCertificate
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanSlopeBounds
import Definitions.Def_CK_GeneralCK_Certificates_RegularContactBounds
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

-- ===== source module GeneralCK.PureGapDoubleCapBiasChecker =====
section

/-!
# Bias-coordinate checker bridge for the compact double-cap middle

The reflection certificate machinery already encloses `biasE`, `SmallMean.A`,
and `regularContact`.  This file supplies the missing enclosure theorem for
the bias of `entropyInverse`, and rewrites the exact cap residual into those
same reflection coordinates.
-/

namespace GeneralCK
open Set
open Certificates.Reflection

/-- Sound inverse-entropy bias bracket.  The hypotheses are precisely the
two endpoint entropy comparisons that a dyadic `biasE` witness can check. -/
theorem entropyInverseBias_bracket {h l u : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1)
    (hlo : biasE u ≤ Real.log 2 * h)
    (hhi : Real.log 2 * h ≤ biasE l) :
    Bounds l u (1 - 2 * entropyInverse h) := by
  have vl0 : 0 ≤ (1 - u) / 2 := by linarith
  have vlh : (1 - u) / 2 ≤ 1 / 2 := by linarith
  have vu0 : 0 ≤ (1 - l) / 2 := by linarith
  have vuh : (1 - l) / 2 ≤ 1 / 2 := by linarith
  have hEu : biasE u = Real.log 2 * H ((1 - u) / 2) := by
    rw [Reflection.biasE_eq_log_mul_E (by linarith) hu]
    rfl
  have hEl : biasE l = Real.log 2 * H ((1 - l) / 2) := by
    rw [Reflection.biasE_eq_log_mul_E (by linarith) (hlu.trans_lt hu)]
    rfl
  have hHlo : H ((1 - u) / 2) ≤ h := by
    rw [hEu] at hlo
    nlinarith [log_two_pos]
  have hHhi : h ≤ H ((1 - l) / 2) := by
    rw [hEl] at hhi
    nlinarith [log_two_pos]
  have hv := Certificates.SmallMean.inverse_bracket hh hh1 vl0 vlh vu0 vuh hHlo hHhi
  constructor <;> linarith [hv.1, hv.2]

/-- Exact reflection-coordinate form of the endpoint residual.  Here `x` is
the mean bias, `y` is the inverse-entropy bias, and `c` is the normalized
regular contact. -/
theorem doubleCapEndpointResidual_bias_identity {m h : ℝ}
    (hm : 0 < m) (hmh : m < 1 / 2) (hh : 0 < h) :
    let x := 1 - 2 * m
    let y := 1 - 2 * entropyInverse h
    let c := Reflection.regularContact (x / (Real.log 2 * h))
    (Real.log 2 / 2) * doubleCapEndpointResidual m h =
      2 * (biasE x - Real.log 2 * h) -
        y * SmallMean.A y + x * SmallMean.A c := by
  dsimp only
  have hz : 0 < 1 - 2 * m := by linarith
  have hEm := Correction.Natural.biasE_probability hm (by linarith : m < 1)
  rw [Certificates.Mixed.hn_eq_H_mul_log] at hEm
  have hAu := Correction.Natural.A_probability (entropyInverse h)
  have hF := HalfMeanAnalytic.evenRadial_eq_abs hh (1 - 2 * m)
  rw [abs_of_pos hz] at hF
  unfold HalfMeanAnalytic.evenRadial HalfMeanAnalytic.contactLog at hF
  unfold doubleCapEndpointResidual
  rw [show (1 - 2 * m) * J (radialContact (1 - 2 * m) h) =
      F (1 - 2 * m) h by simp [F, hz.ne']]
  rw [← hF]
  have hlog : Real.log (2 : ℝ) ≠ 0 := log_two_pos.ne'
  field_simp [hlog] at hAu hF ⊢
  have heta : (1 - 2 * entropyInverse h) * Real.log 2 * J (entropyInverse h) =
      2 * (1 - 2 * entropyInverse h) * SmallMean.A (1 - 2 * entropyInverse h) := by
    calc
      _ = (1 - 2 * entropyInverse h) *
          (Real.log 2 * J (entropyInverse h)) := by ring
      _ = (1 - 2 * entropyInverse h) *
          (2 * SmallMean.A (1 - 2 * entropyInverse h)) := by rw [← hAu]
      _ = _ := by ring
  rw [hEm, heta]
  ring

/-- A component-wise interval certificate for one compact-middle cell.  All
fields are ordinary closed real bounds, so existing dyadic log, entropy, and
contact witnesses can discharge them. -/
structure DoubleCapBiasCellCertificate
    (mLo mHi : ℝ) (floor : ℝ → ℝ) : Prop where
  domain : 0 < mLo ∧ mLo ≤ mHi ∧ mHi < 1 / 2
  sound : ∀ m, mLo ≤ m → m ≤ mHi →
    let h := floor m
    let x := 1 - 2 * m
    let y := 1 - 2 * entropyInverse h
    let c := Reflection.regularContact (x / (Real.log 2 * h))
    0 ≤ 2 * (biasE x - Real.log 2 * h) -
      y * SmallMean.A y + x * SmallMean.A c

theorem doubleCapEndpointResidual_nonneg_of_biasCell
    {mLo mHi : ℝ} {floor : ℝ → ℝ}
    (cert : DoubleCapBiasCellCertificate mLo mHi floor)
    {m : ℝ} (hmLo : mLo ≤ m) (hmHi : m ≤ mHi) (hh : 0 < floor m) :
    0 ≤ doubleCapEndpointResidual m (floor m) := by
  have hm : 0 < m := cert.domain.1.trans_le hmLo
  have hmh : m < 1 / 2 := hmHi.trans_lt cert.domain.2.2
  have hid := doubleCapEndpointResidual_bias_identity hm hmh hh
  have hs := cert.sound m hmLo hmHi
  dsimp only at hid hs
  have hp : 0 < Real.log 2 / 2 := div_pos log_two_pos two_pos
  nlinarith

/-- Conservative representative cell at the left edge of the compact
middle for the requested split `a = 1/5`. -/
def DoubleCapLowMiddlePilotCertificate : Prop :=
  DoubleCapBiasCellCertificate (1 / 5) (13 / 64)
    (fun m => H (2 * m) / 2)

theorem doubleCapLowResidual_nonneg_on_pilot
    (cert : DoubleCapLowMiddlePilotCertificate) :
    ∀ m, 1 / 5 ≤ m → m ≤ 13 / 64 → 0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  unfold doubleCapLowResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell cert hmLo hmHi
  exact div_pos (H_pos (by linarith) (by linarith)) two_pos

#print axioms entropyInverseBias_bracket
#print axioms doubleCapEndpointResidual_bias_identity
#print axioms doubleCapEndpointResidual_nonneg_of_biasCell
#print axioms doubleCapLowResidual_nonneg_on_pilot

end GeneralCK

end


