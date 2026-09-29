-- Prove2me | Definitions.Def_CK_GeneralCK_ProfileConvexity
-- name    : CK_GeneralCK_ProfileConvexity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:26:13.51798+00:00
-- url     : https://prove2.me/theorems/f8f529e0-b803-47f8-b5ed-7770f84e09d4
-- title:
--   Courtade–Kumar proof module `GeneralCK.ProfileConvexity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ProfileConvexity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ProfileConvexity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ProfileConvexity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileConvexity.lean)

import Definitions.Def_CK_GeneralCK_ProfileDerivatives
import Mathlib.Analysis.Convex.Deriv

namespace GeneralCK.Scalar
open Set
open scoped Topology

noncomputable def curvatureNumerator (v : ℝ) : ℝ :=
  (v^2 + (1-v)^2) * Real.log 2 * J v - (1-2*v)

theorem hasDerivAt_curvatureNumerator {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt curvatureNumerator
      (-2*(1-2*v)*Real.log 2*J v - (1-2*v)^2/(v*(1-v))) v := by
  have hd := ((((hasDerivAt_id v).pow 2).add
    (((hasDerivAt_id v).const_sub 1).pow 2)).mul_const (Real.log 2)).mul
      (hasDerivAt_J hv hv')
  have hd' := hd.sub (((hasDerivAt_id v).const_mul 2).const_sub 1)
  convert! hd' using 1
  dsimp
  field_simp [ne_of_gt log_two_pos, ne_of_gt hv, show 1-v ≠ 0 by linarith]
  ring

theorem curvatureNumerator_nonneg {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) :
    0 ≤ curvatureNumerator v := by
  have ha : AntitoneOn curvatureNumerator (Ioc 0 (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (1 / 2))
      (f' := fun v => -2*(1-2*v)*Real.log 2*J v - (1-2*v)^2/(v*(1-v)))
    · intro x hx
      exact (hasDerivAt_curvatureNumerator hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hasDerivAt_curvatureNumerator hx'.1 (by linarith [hx'.2])).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have hJ := J_nonneg hx'.1 hx'.2
      have hx0 : 0 < x := hx'.1
      have hs : 0 ≤ 1 - 2*x := by linarith [hx'.2]
      have hx1 : 0 < 1-x := by linarith [hx'.2]
      have h₁ : 0 ≤ 2*(1-2*x)*Real.log 2*J x := by positivity
      have h₂ : 0 ≤ (1-2*x)^2/(x*(1-x)) := by positivity
      nlinarith
  have hh : curvatureNumerator (1 / 2) = 0 := by norm_num [curvatureNumerator, J]
  have h := ha ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rwa [hh] at h

noncomputable def etaSlope (h : ℝ) : ℝ :=
  -2 - (1 - 2 * entropyInverse h) /
    (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h))

noncomputable def etaCurvature (h : ℝ) : ℝ :=
  curvatureNumerator (entropyInverse h) /
    ((Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h))^2 *
      J (entropyInverse h))

theorem hasDerivAt_etaSlope {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt etaSlope (etaCurvature h) h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hJ := J_pos hv hv'
  have hv1 : 0 < 1 - entropyInverse h := by linarith
  have hi := hasDerivAt_entropyInverse h0 h1
  have hd := ((hi.const_mul 2).const_sub 1).div
    (((hi.const_mul (Real.log 2)).mul (hi.const_sub 1)).mul
      ((hasDerivAt_J hv (by linarith)).comp h hi)) (by
        change Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h) ≠ 0
        exact ne_of_gt (by positivity))
  have hd' := hd.const_sub (-2)
  convert! hd' using 1
  dsimp [etaCurvature, curvatureNumerator]
  field_simp [ne_of_gt log_two_pos, ne_of_gt hv, ne_of_gt hJ,
    show 1 - entropyInverse h ≠ 0 by linarith]
  ring

theorem etaCurvature_nonneg {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    0 ≤ etaCurvature h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  unfold etaCurvature
  exact div_nonneg (curvatureNumerator_nonneg hv hv'.le)
    (mul_nonneg (sq_nonneg _) (J_pos hv hv').le)

theorem hasDerivAt_deriv_eta {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt (deriv eta) (etaCurvature h) h := by
  apply (hasDerivAt_etaSlope h0 h1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds h0 h1] with y hy
  exact deriv_eta hy.1 hy.2

theorem deriv2_eta_nonneg {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    0 ≤ deriv (deriv eta) h := by
  rw [(hasDerivAt_deriv_eta h0 h1).deriv]
  exact etaCurvature_nonneg h0 h1

theorem eta_convexOn : ConvexOn ℝ (Ioo 0 1) eta := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 1) (f' := etaSlope) (f'' := etaCurvature)
  · intro h hh
    exact (hasDerivAt_eta hh.1 hh.2).continuousAt.continuousWithinAt
  · intro h hh
    have hh' := interior_subset hh
    exact (hasDerivAt_eta hh'.1 hh'.2).hasDerivWithinAt
  · intro h hh
    have hh' := interior_subset hh
    exact (hasDerivAt_etaSlope hh'.1 hh'.2).hasDerivWithinAt
  · intro h hh
    have hh' := interior_subset hh
    exact etaCurvature_nonneg hh'.1 hh'.2

theorem continuousWithinAt_eta_one : ContinuousWithinAt eta (Ioc 0 1) 1 := by
  have hv : entropyInverse 1 = 1 / 2 := by
    simpa only [H_half] using entropyInverse_H_lower (v := (1 / 2 : ℝ))
      (by norm_num) le_rfl
  have hi : ContinuousWithinAt entropyInverse (Iic 1) 1 := by
    apply entropyInverse_strictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin
      (Icc_mem_nhdsLE (by norm_num : (0 : ℝ) < 1))
    rw [entropyInverse_image, hv]
    exact Icc_mem_nhdsLE (by norm_num)
  have hi' : ContinuousWithinAt entropyInverse (Ioc 0 1) 1 :=
    hi.mono (fun _ hx => hx.2)
  have hj : ContinuousAt J (entropyInverse 1) := by
    rw [hv]
    exact (hasDerivAt_J (by norm_num) (by norm_num)).continuousAt
  have hc : ContinuousWithinAt
      (fun h => (1 - 2 * entropyInverse h) * J (entropyInverse h)) (Ioc 0 1) 1 :=
    (continuousWithinAt_const.sub (hi'.const_mul 2)).mul
      (hj.comp_continuousWithinAt hi')
  exact hc.congr (fun _ hh => eta_eq_profile hh.1.le hh.2)
    (eta_eq_profile (by norm_num) le_rfl)

theorem eta_continuousOn : ContinuousOn eta (Ioc 0 1) := by
  intro h hh
  by_cases he : h = 1
  · subst h
    exact continuousWithinAt_eta_one
  · exact (hasDerivAt_eta hh.1 (lt_of_le_of_ne hh.2 he)).continuousAt.continuousWithinAt

/-- Convexity includes the upper entropy endpoint; no value at entropy zero
is used, where the production profile has a divergent limit. -/
theorem eta_convexOn_Ioc : ConvexOn ℝ (Ioc 0 1) eta := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 1)
    eta_continuousOn (f' := etaSlope) (f'' := etaCurvature)
  · intro h hh
    rw [interior_Ioc] at hh
    exact (hasDerivAt_eta hh.1 hh.2).hasDerivWithinAt
  · intro h hh
    rw [interior_Ioc] at hh
    exact (hasDerivAt_etaSlope hh.1 hh.2).hasDerivWithinAt
  · intro h hh
    rw [interior_Ioc] at hh
    exact etaCurvature_nonneg hh.1 hh.2

noncomputable def P (t : ℝ) : ℝ := eta (1 - t)

theorem P_convexOn : ConvexOn ℝ (Ico 0 1) P := by
  refine ⟨convex_Ico 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := eta_convexOn_Ioc.2
    (show 1 - x ∈ Ioc 0 1 by constructor <;> linarith [hx.1, hx.2])
    (show 1 - y ∈ Ioc 0 1 by constructor <;> linarith [hy.1, hy.2]) ha hb hab
  simp only [smul_eq_mul, P] at hh ⊢
  convert hh using 1
  congr 1
  nlinarith

end GeneralCK.Scalar


