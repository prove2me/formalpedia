-- Prove2me | Definitions.Def_CK_GeneralCK_ProfileIncreasingCurvature
-- name    : CK_GeneralCK_ProfileIncreasingCurvature
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:29:51.993562+00:00
-- url     : https://prove2.me/theorems/ee05abab-bb25-4674-aa18-c32491083495
-- title:
--   Courtade–Kumar proof module `GeneralCK.ProfileIncreasingCurvature` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ProfileIncreasingCurvature` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ProfileIncreasingCurvature` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ProfileIncreasingCurvature (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileIncreasingCurvature.lean)

import Definitions.Def_CK_GeneralCK_ProfileConvexity
import Definitions.Def_CK_GeneralCK_ProfileLowerBounds
import Definitions.Def_CK_GeneralCK_Certificates_PilotData
import Mathlib.Tactic.GCongr

namespace GeneralCK.Scalar
open Set
open scoped Topology

noncomputable def thirdNumerator (v : ℝ) : ℝ :=
  2*(1-2*v)*((1-2*v)^2+3)*(Real.log 2*J v/2)^2 -
    (5*(1-2*v)^2+3)*(Real.log 2*J v/2) + 3*(1-2*v)

/-- Factored derivative of the third-derivative numerator. This replaces
the manuscript's power-series sign argument by an elementary derivative. -/
theorem hasDerivAt_thirdNumerator {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt thirdNumerator
      (-4*curvatureNumerator v *
        (3*(Real.log 2*J v/2)*(4*v*(1-v))+4*(1-2*v))/(4*v*(1-v))) v := by
  have hR := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hA := ((hasDerivAt_J hv hv').const_mul (Real.log 2)).div_const 2
  have hfirst := ((hR.const_mul 2).mul ((hR.pow 2).add_const 3)).mul (hA.pow 2)
  have hsecond := (((hR.pow 2).const_mul 5).add_const 3).mul hA
  have hd := (hfirst.sub hsecond).add (hR.const_mul 3)
  convert! hd using 1
  dsimp [curvatureNumerator]
  field_simp [ne_of_gt log_two_pos, ne_of_gt hv, show 1-v ≠ 0 by linarith]
  ring

theorem thirdNumerator_nonneg {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/2) :
    0 ≤ thirdNumerator v := by
  have ha : AntitoneOn thirdNumerator (Ioc 0 (1/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc _ _)
      (f' := fun v => -4*curvatureNumerator v *
        (3*(Real.log 2*J v/2)*(4*v*(1-v))+4*(1-2*v))/(4*v*(1-v)))
    · intro x hx
      exact (hasDerivAt_thirdNumerator hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hasDerivAt_thirdNumerator hx'.1 (by linarith [hx'.2])).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have hx0 := hx'.1
      have hxc : 0 < 1-x := by linarith [hx'.2]
      have hr : 0 ≤ 1-2*x := by linarith [hx'.2]
      have hJ := J_nonneg hx0 hx'.2
      have hN := curvatureNumerator_nonneg hx0 hx'.2
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg
        · nlinarith
        · positivity
      · positivity
  have hh : thirdNumerator (1/2) = 0 := by norm_num [thirdNumerator, J]
  have h := ha ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rwa [hh] at h

noncomputable def curvatureProfile (v : ℝ) : ℝ :=
  curvatureNumerator v / ((Real.log 2*v*(1-v)*J v)^2*J v)

theorem hasDerivAt_curvatureProfile {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    HasDerivAt curvatureProfile
      (-thirdNumerator v / ((Real.log 2)^3*v^3*(1-v)^3*(J v)^4)) v := by
  have hvc : 0 < 1-v := by linarith
  have hJ := J_pos hv hv'
  have hD := (((hasDerivAt_id v).const_mul (Real.log 2)).mul
    ((hasDerivAt_id v).const_sub 1)).mul (hasDerivAt_J hv (by linarith))
  have hd := (hasDerivAt_curvatureNumerator hv (by linarith)).div
    ((hD.pow 2).mul (hasDerivAt_J hv (by linarith))) (by
      change (Real.log 2*v*(1-v)*J v)^2*J v ≠ 0
      exact ne_of_gt (by positivity))
  convert! hd using 1
  dsimp [thirdNumerator, curvatureNumerator]
  field_simp [ne_of_gt log_two_pos, ne_of_gt hv, ne_of_gt hvc, ne_of_gt hJ]
  ring

theorem curvatureProfile_antitoneOn : AntitoneOn curvatureProfile (Ioo 0 (1/2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _)
    (f' := fun v => -thirdNumerator v / ((Real.log 2)^3*v^3*(1-v)^3*(J v)^4))
  · intro v hv
    exact (hasDerivAt_curvatureProfile hv.1 hv.2).continuousAt.continuousWithinAt
  · intro v hv
    have hv' := interior_subset hv
    exact (hasDerivAt_curvatureProfile hv'.1 hv'.2).hasDerivWithinAt
  · intro v hv
    have hv' := interior_subset hv
    have hv0 := hv'.1
    have hvc : 0 < 1-v := by linarith [hv'.2]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (thirdNumerator_nonneg hv0 hv'.2.le)
    · positivity

theorem etaCurvature_antitoneOn : AntitoneOn etaCurvature (Ioo 0 1) := by
  intro a ha b hb hab
  exact curvatureProfile_antitoneOn
    ⟨entropyInverse_pos ha.1 ha.2.le, entropyInverse_lt_half ha.1.le ha.2⟩
    ⟨entropyInverse_pos hb.1 hb.2.le, entropyInverse_lt_half hb.1.le hb.2⟩
    (entropyInverse_mono ha.1.le hb.2.le hab)

theorem hasDerivAt_deriv_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    HasDerivAt (deriv P) (etaCurvature (1-I)) I := by
  have hd := ((hasDerivAt_etaSlope (by linarith : 0 < 1-I) (by linarith : 1-I < 1)).comp I
    ((hasDerivAt_id I).const_sub 1)).neg
  have heq : deriv P =ᶠ[𝓝 I] (fun t => -etaSlope (1-t)) := by
    filter_upwards [Ioo_mem_nhds hI hI'] with t ht
    rw [deriv_P ht.1 ht.2]
    unfold etaSlope
    ring
  simpa only [neg_neg, mul_neg, mul_one] using hd.congr_of_eventuallyEq heq

theorem deriv2_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    deriv (deriv P) I = etaCurvature (1-I) := (hasDerivAt_deriv_P hI hI').deriv

theorem deriv2_P_monotoneOn : MonotoneOn (deriv (deriv P)) (Ioo 0 1) := by
  intro a ha b hb hab
  rw [deriv2_P ha.1 ha.2, deriv2_P hb.1 hb.2]
  exact etaCurvature_antitoneOn
    ⟨by linarith [hb.2], by linarith [hb.1]⟩
    ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)

noncomputable def PThird (I : ℝ) : ℝ :=
  thirdNumerator (entropyInverse (1-I)) /
    ((Real.log 2)^3*(entropyInverse (1-I))^3*(1-entropyInverse (1-I))^3*
      (J (entropyInverse (1-I)))^5)

theorem hasDerivAt_deriv2_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    HasDerivAt (deriv (deriv P)) (PThird I) I := by
  have hi0 : 0 < 1-I := by linarith
  have hi1 : 1-I < 1 := by linarith
  have hv := entropyInverse_pos hi0 hi1.le
  have hv' := entropyInverse_lt_half hi0.le hi1
  have hJ := J_pos hv hv'
  have hi := (hasDerivAt_entropyInverse hi0 hi1).comp I ((hasDerivAt_id I).const_sub 1)
  have hd := (hasDerivAt_curvatureProfile hv hv').comp I hi
  have heq : deriv (deriv P) =ᶠ[𝓝 I] (fun t => curvatureProfile (entropyInverse (1-t))) := by
    filter_upwards [Ioo_mem_nhds hI hI'] with t ht
    exact deriv2_P ht.1 ht.2
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  dsimp [PThird]
  field_simp [ne_of_gt hJ]

theorem deriv3_P_nonneg {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    0 ≤ deriv (deriv (deriv P)) I := by
  rw [(hasDerivAt_deriv2_P hI hI').deriv]
  have hv := entropyInverse_pos (by linarith : 0 < 1-I) (by linarith : 1-I ≤ 1)
  have hv' := entropyInverse_lt_half (by linarith : 0 ≤ 1-I) (by linarith : 1-I < 1)
  have hvc : 0 < 1-entropyInverse (1-I) := by linarith
  have hJ := J_pos hv hv'
  apply div_nonneg (thirdNumerator_nonneg hv hv'.le)
  positivity

private theorem log_anchor_left :
    (826678573/1000000000:ℝ) ≤ Real.log (16/7) ∧
      Real.log (16/7) ≤ 826678574/1000000000 := by
  have h := Certificates.checkLog_sound (w := 9/23) (n := 12)
    (lo := 826678573/1000000000) (hi := 826678574/1000000000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_anchor_right :
    (575364144/1000000000:ℝ) ≤ Real.log (16/9) ∧
      Real.log (16/9) ≤ 575364145/1000000000 := by
  have h := Certificates.checkLog_sound (w := 7/25) (n := 12)
    (lo := 575364144/1000000000) (hi := 575364145/1000000000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_anchor_ratio :
    (251314428/1000000000:ℝ) ≤ Real.log (9/7) ∧
      Real.log (9/7) ≤ 251314429/1000000000 := by
  have h := Certificates.checkLog_sound (w := 1/8) (n := 8)
    (lo := 251314428/1000000000) (hi := 251314429/1000000000)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem anchor_entropy_lt : H (7/16) < 99/100 := by
  have ha := log_anchor_left.2
  have hb := log_anchor_right.2
  rw [show (16/7:ℝ) = (7/16)⁻¹ by norm_num, Real.log_inv] at ha
  rw [show (16/9:ℝ) = (9/16)⁻¹ by norm_num, Real.log_inv] at hb
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  unfold H
  apply (div_lt_iff₀ log_two_pos).2
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [Real.negMulLog]
  linarith

theorem curvatureProfile_anchor_le : curvatureProfile (7/16) ≤ 19/10 := by
  have he := log_anchor_ratio
  have hL := Certificates.PilotData.log_two.2
  norm_num only [div_one] at hL
  have he0 : 0 < Real.log (9/7:ℝ) := by linarith [he.1]
  have hnum : 0 ≤ (65/128:ℝ)*Real.log (9/7)-1/8 := by linarith [he.1]
  have heq : curvatureProfile (7/16) =
      Real.log 2*((65/128)*Real.log (9/7)-1/8)/((63/256)^2*(Real.log (9/7))^3) := by
    unfold curvatureProfile curvatureNumerator J
    norm_num
    field_simp [ne_of_gt log_two_pos, ne_of_gt he0]
    ring
  rw [heq]
  calc
    Real.log 2*((65/128)*Real.log (9/7)-1/8)/((63/256)^2*(Real.log (9/7))^3)
      ≤ (693147181/1000000000)*((65/128)*(251314429/1000000000)-1/8) /
        ((63/256)^2*(251314428/1000000000)^3) := by
      gcongr
      · exact he.2
      · exact he.1
    _ ≤ 19/10 := by norm_num

/-- Uniform curvature bound on the physical low-information interior.
The endpoint zero is deliberately excluded from this ordinary derivative. -/
theorem deriv2_P_le_nineteen_tenths {I : ℝ} (hI : 0 < I) (hI' : I ≤ 1/100) :
    deriv (deriv P) I ≤ 19/10 := by
  have hA : 0 < 1-H (7/16) := by linarith [anchor_entropy_lt]
  have hA' : 1-H (7/16) < 1 := by
    have hp : 0 < H (7/16) := H_pos (by norm_num) (by norm_num)
    linarith
  have heq : deriv (deriv P) (1-H (7/16)) = curvatureProfile (7/16) := by
    rw [deriv2_P hA hA']
    change curvatureProfile (entropyInverse (1-(1-H (7/16)))) = _
    rw [show 1-(1-H (7/16)) = H (7/16) by ring,
      entropyInverse_H_lower (by norm_num) (by norm_num)]
  have hh := deriv2_P_monotoneOn ⟨hI, by linarith⟩ ⟨hA, hA'⟩
    (show I ≤ 1-H (7/16) by linarith [anchor_entropy_lt])
  rw [heq] at hh
  exact hh.trans curvatureProfile_anchor_le

end GeneralCK.Scalar


