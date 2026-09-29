-- Prove2me | Definitions.Def_CK_GeneralCK_PhysicalSlope
-- name    : CK_GeneralCK_PhysicalSlope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:33:29.632338+00:00
-- url     : https://prove2.me/theorems/143c58fa-63fa-46e4-86ba-785ee3de1b18
-- title:
--   Courtade–Kumar proof module `GeneralCK.PhysicalSlope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PhysicalSlope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PhysicalSlope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PhysicalSlope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PhysicalSlope.lean)

import Definitions.Def_CK_GeneralCK_ProfileIncreasingCurvature

namespace GeneralCK.Scalar
open Set Filter
open scoped Topology

noncomputable def P1 (I : ℝ) : ℝ := if I = 0 then 4 else deriv P I

@[simp] theorem P1_zero : P1 0 = 4 := by simp [P1]

theorem P1_eq_deriv {I : ℝ} (hI : 0 < I) : P1 I = deriv P I := by simp [P1, hI.ne']

theorem logit_ge_twice_imbalance {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/2) :
    2*(1-2*v) ≤ Real.log 2*J v := by
  let g : ℝ → ℝ := fun x => Real.log 2*J x - 2*(1-2*x)
  have hd {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
      HasDerivAt g (-(1-2*x)^2/(x*(1-x))) x := by
    have hh := ((hasDerivAt_J hx hx').const_mul (Real.log 2)).sub
      ((((hasDerivAt_id x).const_mul 2).const_sub 1).const_mul 2)
    convert! hh using 1
    field_simp [log_two_pos.ne', hx.ne', show 1-x ≠ 0 by linarith]
    ring
  have ha : AntitoneOn g (Ioc 0 (1/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc _ _)
      (f' := fun x => -(1-2*x)^2/(x*(1-x)))
    · intro x hx
      exact (hd hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hd hx'.1 (by linarith [hx'.2])).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have hx0 := hx'.1
      have hxc : 0 < 1-x := by linarith [hx'.2]
      apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      positivity
  have hh : g (1/2) = 0 := by norm_num [g, J]
  have h := ha ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rw [hh] at h
  dsimp [g] at h
  linarith

theorem deriv_P_upper {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    deriv P I ≤ 2+1/(2*entropyInverse (1-I)*(1-entropyInverse (1-I))) := by
  have hv := entropyInverse_pos (by linarith : 0 < 1-I) (by linarith : 1-I ≤ 1)
  have hv' := entropyInverse_lt_half (by linarith : 0 ≤ 1-I) (by linarith : 1-I < 1)
  have hvc : 0 < 1-entropyInverse (1-I) := by linarith
  have hJ := J_pos hv hv'
  have hL := logit_ge_twice_imbalance hv hv'.le
  rw [deriv_P hI hI']
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hh := mul_le_mul_of_nonneg_right hL
    (mul_pos hv hvc).le
  nlinarith

theorem entropyInverse_one : entropyInverse 1 = 1/2 := by
  simpa only [H_half] using entropyInverse_H_lower (v := (1/2:ℝ)) (by norm_num) le_rfl

theorem entropyInverse_continuousWithinAt_one :
    ContinuousWithinAt entropyInverse (Iic 1) 1 := by
  apply entropyInverse_strictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin
    (Icc_mem_nhdsLE (by norm_num : (0:ℝ) < 1))
  rw [entropyInverse_image, entropyInverse_one]
  exact Icc_mem_nhdsLE (by norm_num)

theorem P1_continuousWithinAt_zero : ContinuousWithinAt P1 (Ico 0 1) 0 := by
  have hi : ContinuousWithinAt (fun I => entropyInverse (1-I)) (Ico 0 1) 0 := by
    exact entropyInverse_continuousWithinAt_one.comp_of_eq
      ((continuous_const.sub continuous_id).continuousWithinAt)
      (fun I hI => by change 1-I ≤ 1; linarith [hI.1]) (by norm_num)
  have hup : ContinuousWithinAt
      (fun I => 2+1/(2*entropyInverse (1-I)*(1-entropyInverse (1-I)))) (Ico 0 1) 0 := by
    apply ContinuousWithinAt.const_add
    apply ContinuousWithinAt.div continuousWithinAt_const
      ((hi.const_mul 2).mul (continuousWithinAt_const.sub hi))
    norm_num [entropyInverse_one]
  have ht : Tendsto
      (fun I => 2+1/(2*entropyInverse (1-I)*(1-entropyInverse (1-I))))
      (𝓝[Ico 0 1] 0) (𝓝 4) := by
    convert! hup.tendsto using 1
    norm_num [entropyInverse_one]
  change Tendsto P1 (𝓝[Ico 0 1] 0) (𝓝 (P1 0))
  rw [P1_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [self_mem_nhdsWithin] with I hI
    by_cases hzero : I = 0
    · subst I; simp
    · rw [P1_eq_deriv (lt_of_le_of_ne hI.1 (Ne.symm hzero))]
      exact four_le_deriv_P (lt_of_le_of_ne hI.1 (Ne.symm hzero)) hI.2
  · filter_upwards [self_mem_nhdsWithin] with I hI
    by_cases hzero : I = 0
    · subst I; norm_num [entropyInverse_one]
    · rw [P1_eq_deriv (lt_of_le_of_ne hI.1 (Ne.symm hzero))]
      exact deriv_P_upper (lt_of_le_of_ne hI.1 (Ne.symm hzero)) hI.2

theorem hasDerivAt_P1 {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    HasDerivAt P1 (etaCurvature (1-I)) I := by
  apply (hasDerivAt_deriv_P hI hI').congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hI] with t ht
  exact P1_eq_deriv ht

theorem P1_continuousOn : ContinuousOn P1 (Ico 0 1) := by
  intro I hI
  by_cases hzero : I = 0
  · subst I; exact P1_continuousWithinAt_zero
  · exact (hasDerivAt_P1 (lt_of_le_of_ne hI.1 (Ne.symm hzero)) hI.2).continuousAt.continuousWithinAt

theorem P1_convexOn : ConvexOn ℝ (Ico 0 1) P1 := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ico _ _) P1_continuousOn
  · intro I hI
    rw [interior_Ico] at hI
    exact (hasDerivAt_P1 hI.1 hI.2).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    rw [interior_Ico] at ha hb
    rw [(hasDerivAt_P1 ha.1 ha.2).deriv, (hasDerivAt_P1 hb.1 hb.2).deriv]
    exact etaCurvature_antitoneOn
      ⟨by linarith [hb.2], by linarith [hb.1]⟩
      ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)

theorem P1_le_secant {I a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hI : 0 ≤ I) (hI' : I ≤ a) :
    P1 I ≤ 4 + ((P1 a-4)/a)*I := by
  have hw : 0 ≤ I/a := div_nonneg hI ha.le
  have hw' : I/a ≤ 1 := (div_le_one ha).2 hI'
  have hh := P1_convexOn.2 (show (0:ℝ) ∈ Ico 0 1 by norm_num)
    (show a ∈ Ico 0 1 from ⟨ha.le, ha'⟩)
    (sub_nonneg.mpr hw') hw (show (1-I/a)+I/a=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ ha.ne', P1_zero] at hh
  convert! hh using 1
  ring

theorem deriv_P_le_secant {I a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hI : 0 < I) (hI' : I ≤ a) :
    deriv P I ≤ 4 + ((deriv P a-4)/a)*I := by
  simpa only [P1_eq_deriv hI, P1_eq_deriv ha] using P1_le_secant ha ha' hI.le hI'

theorem deriv_P_le_linear_of_secant {I a c : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hI : 0 < I) (hI' : I ≤ a) (hc : (deriv P a-4)/a ≤ c) :
    deriv P I ≤ 4+c*I :=
  (deriv_P_le_secant ha ha' hI hI').trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hc hI.le))

end GeneralCK.Scalar


