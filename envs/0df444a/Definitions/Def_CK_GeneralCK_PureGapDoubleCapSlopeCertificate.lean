-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapSlopeCertificate
-- name    : CK_GeneralCK_PureGapDoubleCapSlopeCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:08:13.81745+00:00
-- url     : https://prove2.me/theorems/f992fdfd-2499-442e-a44d-f4446642ef8d
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapSlopeCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapSlopeCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapSlopeCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapSlopeCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapSlopeCertificate.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapScalarContract
import Definitions.Def_CK_GeneralCK_PhiEntropyConvexity
import Definitions.Def_CK_GeneralCK_PureGapE8Bridge

-- ===== source module GeneralCK.PureGapDoubleCapSlopeCertificate =====
section

/-!
# Slope certificate for the zero-cutoff double-cap endpoint

The direct scalar residual has a severe cancellation at `m = 1/2`.  This
module replaces its sign by a sufficient first-derivative check at the lower
entropy endpoint.  Convexity of `phi m` then carries that tangent to the
exact cap value `phi m (H m) = 0`.
-/

namespace GeneralCK
open Set

/-- Both branches of the canonical entropy floor lie strictly below the
entropy cap in the open lower-half chamber. -/
theorem doubleCapLowFloor_lt_entropyCap {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    H (2 * m) / 2 < H m := by
  have h2m : 2 * m ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hne : (0 : ℝ) ≠ 2 * m := by linarith
  have hs := Real.strictConcave_binEntropy.2 h0 h2m hne
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero] at hs
  unfold H
  rw [show Real.binEntropy (2 * m) / Real.log 2 / 2 =
      (Real.binEntropy (2 * m) / 2) / Real.log 2 by
    field_simp [log_two_pos.ne']]
  apply (div_lt_div_iff_of_pos_right log_two_pos).2
  rw [show (1 / 2 : ℝ) * (2 * m) = m by ring] at hs
  nlinarith

theorem doubleCapHighFloor_lt_entropyCap {m : ℝ}
    (hmq : 1 / 4 < m) (hmh : m < 1 / 2) :
    (1 + H (2 * m - 1 / 2)) / 2 < H m := by
  have hx : 2 * m - 1 / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hne : (1 / 2 : ℝ) ≠ 2 * m - 1 / 2 := by linarith
  have hs := Real.strictConcave_binEntropy.2 hh hx hne
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hs
  have hmid : (1 / 2 : ℝ) * (1 / 2) +
      (1 / 2) * (2 * m - 1 / 2) = m := by ring
  rw [hmid] at hs
  have hhalfNat : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [hhalfNat] at hs
  unfold H
  rw [show (1 + Real.binEntropy (2 * m - 1 / 2) / Real.log 2) / 2 =
      ((Real.log 2 + Real.binEntropy (2 * m - 1 / 2)) / 2) / Real.log 2 by
    field_simp [log_two_pos.ne']]
  apply (div_lt_div_iff_of_pos_right log_two_pos).2
  nlinarith

/-- A lower bound `-4` for the entropy derivative at an interior floor is a
sufficient exact certificate for the endpoint residual. -/
theorem doubleCapEndpointResidual_nonneg_of_slope {m h : ℝ}
    (hm : 0 < m) (hmh : m < 1 / 2) (hh : 0 < h) (hhcap : h < H m)
    (hslope : -4 ≤ deriv (phi m) h) :
    0 ≤ doubleCapEndpointResidual m h := by
  have hHm0 : 0 < H m := H_pos hm (by linarith)
  have hHm1 : H m ≤ 1 := H_le_one m
  have hconv := phi_entropy_convexOn hm (by linarith : m < 1)
  have hdiff : DifferentiableAt ℝ (phi m) h := by
    have hz : 0 < 1 - 2 * m := by linarith
    have hh1 : h < 1 := hhcap.trans_le hHm1
    have hd := EntropyCurvature.hasDerivAt_radialPhi_entropy hz hh hh1
    have heq : phi m = radialPhi (1 - 2 * m) := by
      funext q
      simp only [phi, radialPhi, abs_of_pos hz]
    rw [heq]
    exact hd.differentiableAt
  have hsec := hconv.deriv_le_slope
    (show h ∈ Ioc (0 : ℝ) (H m) from ⟨hh, hhcap.le⟩)
    (show H m ∈ Ioc (0 : ℝ) (H m) from ⟨hHm0, le_rfl⟩)
    hhcap hdiff
  rw [slope_def_field, phi_at_entropy_cap hm hmh.le] at hsec
  have hden : 0 < H m - h := sub_pos.mpr hhcap
  have hmul := (le_div_iff₀ hden).mp hsec
  have hendpoint : phi m h ≤ 4 * (H m - h) := by
    nlinarith
  have hh1 : h ≤ 1 := hhcap.le.trans hHm1
  exact (doubleCap_endpoint_iff_residual_nonneg hm hmh hh hh1).1 hendpoint

noncomputable def doubleCapLowSlopeResidual (m : ℝ) : ℝ :=
  let h := H (2 * m) / 2
  let r := (1 - 2 * m) / h
  2 - (1 - 2 * entropyInverse h) /
      (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) -
    F r 1 + r * e8Theta (r / 2)

noncomputable def doubleCapHighSlopeResidual (m : ℝ) : ℝ :=
  let h := (1 + H (2 * m - 1 / 2)) / 2
  let r := (1 - 2 * m) / h
  2 - (1 - 2 * entropyInverse h) /
      (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) -
    F r 1 + r * e8Theta (r / 2)

/-- Exact derivative formula used by both slope residuals.  It uses only a
single entropy inverse and the normalized radial profile. -/
theorem four_add_deriv_phi_eq_slopeFormula {m h : ℝ}
    (hm : 0 < m) (hmh : m < 1 / 2) (hh : 0 < h) (hh1 : h < 1) :
    4 + deriv (phi m) h =
      2 - (1 - 2 * entropyInverse h) /
          (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) -
        F ((1 - 2 * m) / h) 1 +
          ((1 - 2 * m) / h) * e8Theta (((1 - 2 * m) / h) / 2) := by
  have hz : 0 < 1 - 2 * m := by linarith
  have hphi : phi m = radialPhi (1 - 2 * m) := by
    funext q
    simp only [phi, radialPhi, abs_of_pos hz]
  rw [hphi, (EntropyCurvature.hasDerivAt_radialPhi_entropy hz hh hh1).deriv,
    deriv_eta hh hh1, deriv_F_entropy hz hh,
    deriv_F_radius_eq_e8Theta (div_pos hz hh) (by norm_num)]
  ring

/-- Hybrid owner interface.  The slope formula is intended for the two
endpoint tails, while the original value residual remains available on the
compact middle where the sufficient slope inequality need not hold. -/
structure DoubleCapHybridSlopeCertificate (a b : ℝ) : Prop where
  a_pos : 0 < a
  a_le_quarter : a ≤ 1 / 4
  quarter_le_b : 1 / 4 ≤ b
  b_lt_half : b < 1 / 2
  lowSlope : ∀ m, 0 < m → m ≤ a → 0 ≤ doubleCapLowSlopeResidual m
  lowMiddle : ∀ m, a < m → m ≤ 1 / 4 → 0 ≤ doubleCapLowResidual m
  highMiddle : ∀ m, 1 / 4 < m → m < b → 0 ≤ doubleCapHighResidual m
  highSlope : ∀ m, b ≤ m → m < 1 / 2 → 0 ≤ doubleCapHighSlopeResidual m

theorem residualCertificate_of_hybridSlopeCertificate {a b : ℝ}
    (cert : DoubleCapHybridSlopeCertificate a b) :
    CanonicalDoubleCapResidualCertificate where
  low m hm hmq := by
    by_cases hma : m ≤ a
    · unfold doubleCapLowResidual
      apply doubleCapEndpointResidual_nonneg_of_slope hm (by linarith) (by
        exact div_pos (H_pos (by linarith) (by linarith)) two_pos)
        (doubleCapLowFloor_lt_entropyCap hm hmq)
      have hfloor1 : H (2 * m) / 2 < 1 :=
        (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
      have heq := four_add_deriv_phi_eq_slopeFormula hm (by linarith) (by
        exact div_pos (H_pos (by linarith) (by linarith)) two_pos) hfloor1
      have hcert := cert.lowSlope m hm hma
      unfold doubleCapLowSlopeResidual at hcert
      dsimp only at hcert
      linarith
    · exact cert.lowMiddle m (lt_of_not_ge hma) hmq
  high m hmq hmh := by
    by_cases hbm : b ≤ m
    · unfold doubleCapHighResidual
      have hx0 : 0 < 2 * m - 1 / 2 := by linarith
      have hx1 : 2 * m - 1 / 2 < 1 := by linarith
      apply doubleCapEndpointResidual_nonneg_of_slope (by linarith) hmh (by
        have := H_pos hx0 hx1
        linarith)
        (doubleCapHighFloor_lt_entropyCap hmq hmh)
      have hfloor1 : (1 + H (2 * m - 1 / 2)) / 2 < 1 :=
        (doubleCapHighFloor_lt_entropyCap hmq hmh).trans_le (H_le_one m)
      have heq := four_add_deriv_phi_eq_slopeFormula (by linarith) hmh (by
        have := H_pos hx0 hx1
        linarith) hfloor1
      have hcert := cert.highSlope m hbm hmh
      unfold doubleCapHighSlopeResidual at hcert
      dsimp only at hcert
      linarith
    · exact cert.highMiddle m hmq (lt_of_not_ge hbm)

theorem canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate {a b : ℝ}
    (cert : DoubleCapHybridSlopeCertificate a b) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_residual_certificate
    (residualCertificate_of_hybridSlopeCertificate cert)

#print axioms doubleCapLowFloor_lt_entropyCap
#print axioms doubleCapHighFloor_lt_entropyCap
#print axioms doubleCapEndpointResidual_nonneg_of_slope
#print axioms four_add_deriv_phi_eq_slopeFormula
#print axioms residualCertificate_of_hybridSlopeCertificate
#print axioms canonicalDoubleCapEntropyEndpoints_of_hybridSlopeCertificate

end GeneralCK

end


