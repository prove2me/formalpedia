-- Prove2me | Definitions.Def_CK_GeneralCK_LowInformationProfile
-- name    : CK_GeneralCK_LowInformationProfile
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:34:48.958693+00:00
-- url     : https://prove2.me/theorems/72cf07df-a93f-42ab-9c49-a68ee2b8f512
-- title:
--   Courtade–Kumar proof module `GeneralCK.LowInformationProfile` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LowInformationProfile` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LowInformationProfile` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LowInformationProfile (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LowInformationProfile.lean)

import Definitions.Def_CK_GeneralCK_PhysicalSlope
import Definitions.Def_CK_GeneralCK_ScalarGap

namespace GeneralCK.Scalar
open Set

/-- A slope increment estimate including the physical endpoint at zero. -/
theorem P1_difference_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/100) :
    P1 y-P1 x ≤ (19/10)*(y-x) := by
  have ha : AntitoneOn (fun I => P1 I-(19/10)*I) (Icc 0 (1/100)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun I => etaCurvature (1-I)-19/10)
    · exact (P1_continuousOn.mono (by
        intro I hI
        exact ⟨hI.1, by linarith [hI.2]⟩)).sub
          (continuous_const.mul continuous_id).continuousOn
    · intro I hI
      rw [interior_Icc] at hI
      simpa using! ((hasDerivAt_P1 hI.1 (by linarith [hI.2])).sub
        ((hasDerivAt_id I).const_mul (19/10))).hasDerivWithinAt
    · intro I hI
      rw [interior_Icc] at hI
      have hh := deriv2_P_le_nineteen_tenths hI.1 hI.2.le
      rw [deriv2_P hI.1 (by linarith [hI.2])] at hh
      linarith
  have hh := ha ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
  linarith

theorem P1_low_information_upper {I : ℝ} (hI : 0 ≤ I) (hI' : I ≤ 1/100) :
    P1 I ≤ 4+(19/10)*I := by
  have hh := P1_difference_le (x := 0) le_rfl hI hI'
  rw [P1_zero] at hh
  linarith

theorem low_information_increment_linear {D s : ℝ}
    (hD : 0 ≤ D) (hs : 0 ≤ s) (hcap : D+s ≤ 1/100) :
    P (D+s)-P s ≤ (4019/1000)*D := by
  by_cases hzero : D+s = 0
  · have hD0 : D = 0 := by linarith
    subst D
    simp
  · have hp : 0 < D+s := lt_of_le_of_ne (add_nonneg hD hs) (Ne.symm hzero)
    have hh := P_increment_upper hs (by linarith : s ≤ D+s) hp (by linarith)
    have hu := P1_low_information_upper hp.le hcap
    rw [P1_eq_deriv hp] at hu
    have hu' : deriv P (D+s) ≤ 4019/1000 := by linarith
    have hm := mul_le_mul_of_nonneg_left hu' hD
    nlinarith

theorem low_information_increment_bilinear {D s : ℝ}
    (hD : 0 ≤ D) (hs : 0 ≤ s) (hcap : D+s ≤ 1/100) :
    P (D+s)-P s ≤ P D+(19/10)*D*s := by
  let f : ℝ → ℝ := fun t => P (D+t)-P t-(19/10)*D*t
  have ha : AntitoneOn f (Icc 0 s) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun t => deriv P (D+t)-deriv P t-(19/10)*D)
    · have hleft : ContinuousOn (fun t => P (D+t)) (Icc 0 s) := by
        apply P_continuousOn.comp (continuous_const.add continuous_id).continuousOn
        intro t ht
        change 0 ≤ D+t ∧ D+t < 1
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hright : ContinuousOn P (Icc 0 s) := P_continuousOn.mono (by
        intro t ht
        exact ⟨ht.1, by linarith [ht.2]⟩)
      exact (hleft.sub hright).sub (continuous_const.mul continuous_id).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      have hp : 0 < D+t := by linarith [ht.1]
      have hp' : D+t < 1 := by linarith [ht.2]
      have ht' : t < 1 := by linarith [ht.2]
      have hd := (((hasDerivAt_P hp hp').comp t ((hasDerivAt_id t).const_add D)).sub
        (hasDerivAt_P ht.1 ht')).sub ((hasDerivAt_id t).const_mul ((19/10)*D))
      rw [← deriv_P hp hp', ← deriv_P ht.1 ht'] at hd
      convert! hd.hasDerivWithinAt using 1
      simp
    · intro t ht
      rw [interior_Icc] at ht
      have hp : 0 < D+t := by linarith [ht.1]
      have hh := P1_difference_le ht.1.le (by linarith : t ≤ D+t)
        (show D+t ≤ 1/100 by linarith [ht.2])
      rw [P1_eq_deriv hp, P1_eq_deriv ht.1] at hh
      linarith
  have hh := ha (show (0:ℝ) ∈ Icc 0 s from ⟨le_rfl, hs⟩)
    (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩) hs
  dsimp [f] at hh
  rw [add_zero, P_zero, sub_zero, mul_zero, sub_zero] at hh
  linarith

end GeneralCK.Scalar


