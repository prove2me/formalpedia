-- Prove2me | Definitions.Def_CK_GeneralCK_RadialConcavity
-- name    : CK_GeneralCK_RadialConcavity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:34:01.387017+00:00
-- url     : https://prove2.me/theorems/c40cf4e9-0356-4c00-ad41-5583d35e03f1
-- title:
--   Courtade–Kumar proof module `GeneralCK.RadialConcavity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.RadialConcavity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.RadialConcavity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.RadialConcavity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/RadialConcavity.lean)

import Definitions.Def_CK_GeneralCK_RadialConvexity
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace GeneralCK
open Set Filter
open scoped Topology
open Certificates.Mixed

private noncomputable def massEntropyGap (v : ℝ) : ℝ :=
  Real.negMulLog v - Real.negMulLog (1 - v)

private theorem hasDerivAt_massEntropyGap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt massEntropyGap (2 * kap v - 2) v := by
  have hd := (Real.hasDerivAt_negMulLog hv.ne').sub
    ((Real.hasDerivAt_negMulLog (show 1 - v ≠ 0 by linarith)).comp v
      ((hasDerivAt_id v).const_sub 1))
  convert! hd using 1
  dsimp [kap]
  rw [Real.log_mul hv.ne' (by linarith)]
  ring

theorem hn_le_four_mul_kap {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    hn v ≤ 4 * v * (1 - v) * kap v := by
  have hc : ConcaveOn ℝ (Icc 0 (1 / 2)) massEntropyGap := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (1 / 2))
      (f' := fun u => 2 * kap u - 2)
      (f'' := fun u => -(1 - 2 * u) / (u * (1 - u)))
    · exact (Real.continuous_negMulLog.sub
        (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))).continuousOn
    · intro u hu
      rw [interior_Icc] at hu
      exact (hasDerivAt_massEntropyGap hu.1 (by linarith [hu.2])).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hd := ((hasDerivAt_kap hu.1 (show u < 1 by linarith [hu.2])).const_mul 2).sub_const 2
      convert! hd.hasDerivWithinAt using 1
      field_simp
    · intro u hu
      rw [interior_Icc] at hu
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hu.2])
        (mul_nonneg hu.1.le (by linarith [hu.2]))
  have hg := hc.2 (show (0 : ℝ) ∈ Icc 0 (1 / 2) by constructor <;> norm_num)
    (show (1 / 2 : ℝ) ∈ Icc 0 (1 / 2) by constructor <;> norm_num)
    (show 0 ≤ 1 - 2 * v by linarith) (show 0 ≤ 2 * v by positivity)
    (show (1 - 2 * v) + 2 * v = 1 by ring)
  have hg0 : massEntropyGap 0 = 0 := by simp [massEntropyGap]
  have hg1 : massEntropyGap (1 / 2) = 0 := by norm_num [massEntropyGap]
  simp only [smul_eq_mul, hg0, hg1, mul_zero, zero_add, mul_one_div] at hg
  have hg' : 0 ≤ massEntropyGap v := by
    convert! hg using 2
    ring
  have he : 4 * v * (1 - v) * kap v - hn v = (1 - 2 * v) * massEntropyGap v := by
    unfold kap hn massEntropyGap Real.negMulLog
    rw [Real.log_mul hv.ne' (by linarith)]
    ring
  have hp := mul_nonneg (show 0 ≤ 1 - 2 * v by linarith) hg'
  linarith

theorem two_radius_le_logit {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) :
    2 * (1 - 2 * v) ≤ Real.log 2 * J v := by
  let g : ℝ → ℝ := fun u => Real.log 2 * J u - 2 * (1 - 2 * u)
  have hd : ∀ u ∈ Ioc (0 : ℝ) (1 / 2),
      HasDerivAt g (-((1 - 2 * u)^2) / (u * (1 - u))) u := by
    intro u hu
    have h := ((hasDerivAt_J hu.1 (show u < 1 by linarith [hu.2])).const_mul
      (Real.log 2)).sub ((((hasDerivAt_id u).const_mul 2).const_sub 1).const_mul 2)
    convert! h using 1
    field_simp [log_two_pos.ne', hu.1.ne', show 1 - u ≠ 0 by linarith [hu.2]]
    ring
  have hm : AntitoneOn g (Ioc 0 (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (1 / 2))
      (f' := fun u => -((1 - 2 * u)^2) / (u * (1 - u)))
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      have hu' := interior_subset hu
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
        (mul_nonneg hu'.1.le (by linarith [hu'.2]))
  have hh : g (1 / 2) = 0 := by norm_num [g, J]
  have h := hm ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rw [hh] at h
  dsimp [g] at h
  linarith

theorem mixed_profile_le_radialSlope {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    profile v ≤ radialSlope v := by
  have hk : 0 < kap v := kap_pos hv hv'
  have hc : 0 < 1 - v := by linarith
  have hn0 : 0 ≤ hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_nonneg (H_nonneg hv.le (by linarith)) log_two_pos.le
  let t := hn v / (2 * v * (1 - v) * kap v)
  have ht0 : 0 ≤ t := div_nonneg hn0 (by positivity)
  have ht2 : t ≤ 2 := (div_le_iff₀ (by positivity : 0 < 2 * v * (1 - v) * kap v)).2
    (by nlinarith [hn_le_four_mul_kap hv hv'])
  have htpoly : t^2 ≤ t + 2 := by
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht2)
      (show 0 ≤ t + 1 by linarith)
    nlinarith
  have hr : 0 ≤ 1 - 2 * v := by linarith
  have hp : profile v ≤ (1 - 2 * v) * t^2 / Real.log 2 := by
    have hfac : 2 * kap v - (1 - 2 * v)^2 ≤ 2 * kap v := by nlinarith [sq_nonneg (1 - 2 * v)]
    have hmul := mul_le_mul_of_nonneg_left hfac
      (show 0 ≤ 2 * (1 - 2 * v) * (hn v)^2 by positivity)
    have hden : 0 < Real.log 2 * (4 * v * (1 - v))^2 * (kap v)^3 := by positivity
    have hh := div_le_div_of_nonneg_right hmul hden.le
    unfold profile
    apply hh.trans_eq
    dsimp [t]
    field_simp
    ring
  have htbound := mul_le_mul_of_nonneg_left htpoly hr
  have hj := two_radius_le_logit hv hv'.le
  have he : radialSlope v = (Real.log 2 * J v + (1 - 2 * v) * t) / Real.log 2 := by
    unfold radialSlope
    dsimp [t]
    field_simp
  apply hp.trans
  rw [he]
  exact (div_le_div_iff_of_pos_right log_two_pos).2 (by nlinarith)

theorem radius_mul_deriv2_F_le_deriv {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z ≤ deriv (fun r => F r h) z := by
  rw [radius_mul_deriv2_F_eq_profile hz hh, deriv_F_radius_slope hz hh]
  exact mixed_profile_le_radialSlope (radialContact_pos hz hh) (radialContact_lt_half hz hh)

theorem hasDerivAt_F_radius_ratio {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => deriv (fun x => F x h) r / (2 * r))
      ((z * deriv (deriv (fun r => F r h)) z - deriv (fun r => F r h) z) / (2 * z^2)) z := by
  have hd := (hasDerivAt_deriv_F_radius hz hh).div ((hasDerivAt_id z).const_mul 2)
    (by positivity : (2 : ℝ) * z ≠ 0)
  rw [← (hasDerivAt_deriv_F_radius hz hh).deriv] at hd
  convert! hd using 1
  dsimp
  field_simp

theorem antitoneOn_F_radius_ratio {h : ℝ} (hh : 0 < h) :
    AntitoneOn (fun z => deriv (fun r => F r h) z / (2 * z)) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (f' := fun z => (z * deriv (deriv (fun r => F r h)) z - deriv (fun r => F r h) z) / (2 * z^2))
  · intro z hz
    exact (hasDerivAt_F_radius_ratio hz hh).continuousAt.continuousWithinAt
  · intro z hz
    exact (hasDerivAt_F_radius_ratio (by simpa using hz) hh).hasDerivWithinAt
  · intro z hz
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (radius_mul_deriv2_F_le_deriv (by simpa using hz) hh)) (by positivity)

theorem hasDerivAt_F_sqrt {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    HasDerivAt (fun x => F (Real.sqrt x) h)
      (deriv (fun r => F r h) (Real.sqrt w) / (2 * Real.sqrt w)) w := by
  have hd := (hasDerivAt_F_radius (Real.sqrt_pos.mpr hw) hh).comp w (Real.hasDerivAt_sqrt hw.ne')
  rw [← (hasDerivAt_F_radius (Real.sqrt_pos.mpr hw) hh).deriv] at hd
  convert! hd using 1
  ring

theorem concaveOn_F_sqrt {h : ℝ} (hh : 0 < h) :
    ConcaveOn ℝ (Ici 0) (fun w => F (Real.sqrt w) h) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact (continuousOn_F_radius hh).comp Real.continuous_sqrt.continuousOn
      (fun w _ => Real.sqrt_nonneg w)
  · intro w hw
    exact (hasDerivAt_F_sqrt (by simpa using hw) hh).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    have ha0 : 0 < a := by simpa using ha
    have hb0 : 0 < b := by simpa using hb
    rw [(hasDerivAt_F_sqrt ha0 hh).deriv, (hasDerivAt_F_sqrt hb0 hh).deriv]
    exact antitoneOn_F_radius_ratio hh (Real.sqrt_pos.mpr ha0) (Real.sqrt_pos.mpr hb0)
      (Real.sqrt_le_sqrt hab)

theorem antitoneOn_F_div_sq {h : ℝ} (hh : 0 < h) :
    AntitoneOn (fun z => F z h / z^2) (Ioi 0) := by
  intro a ha b hb hab
  have h := (concaveOn_F_sqrt hh).antitoneOn_slope_gt (x := 0) (show (0 : ℝ) ∈ Ici 0 by norm_num)
    (show a^2 ∈ {y ∈ Ici (0 : ℝ) | 0 < y} from ⟨sq_nonneg a, sq_pos_of_pos ha⟩)
    (show b^2 ∈ {y ∈ Ici (0 : ℝ) | 0 < y} from ⟨sq_nonneg b, sq_pos_of_pos hb⟩)
    (pow_le_pow_left₀ ha.le hab 2)
  simpa only [slope_def_field, Real.sqrt_zero, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le,
    F, ↓reduceIte, sub_zero] using h

/-- Concavity in squared radius bounds the average at two displaced radii. -/
theorem F_average_le_sqrt {h : ℝ} (hh : 0 < h) (r d : ℝ) :
    (F |r - d| h + F |r + d| h) / 2 ≤ F (Real.sqrt (r^2 + d^2)) h := by
  have hj := (concaveOn_F_sqrt hh).2
    (show (r - d)^2 ∈ Ici (0 : ℝ) by change (0 : ℝ) ≤ (r - d)^2; exact sq_nonneg (r - d))
    (show (r + d)^2 ∈ Ici (0 : ℝ) by change (0 : ℝ) ≤ (r + d)^2; exact sq_nonneg (r + d))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, Real.sqrt_sq_eq_abs] at hj
  have he : (1 / 2 : ℝ) * (r - d)^2 + (1 / 2) * (r + d)^2 = r^2 + d^2 := by ring
  rw [he] at hj
  linarith

theorem F_sqrt_increment_le {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (d : ℝ) :
    F (Real.sqrt (r^2 + d^2)) h - F r h ≤
      d^2 / (2 * r) * deriv (fun z => F z h) r := by
  by_cases hd : d = 0
  · subst d
    simp only [sq, mul_zero, add_zero, Real.sqrt_mul_self hr.le, sub_self, zero_div, zero_mul, le_refl]
  have hd2 : 0 < d^2 := sq_pos_of_ne_zero hd
  have hs := (concaveOn_F_sqrt hh).slope_le_of_hasDerivAt
    (show r^2 ∈ Ici (0 : ℝ) by change (0 : ℝ) ≤ r^2; exact sq_nonneg r)
    (show r^2 + d^2 ∈ Ici (0 : ℝ) by change (0 : ℝ) ≤ r^2 + d^2; exact add_nonneg (sq_nonneg r) (sq_nonneg d))
    (show r^2 < r^2 + d^2 by linarith) (hasDerivAt_F_sqrt (sq_pos_of_pos hr) hh)
  simp only [slope_def_field, Real.sqrt_sq hr.le, add_sub_cancel_left] at hs
  have hs' := (div_le_iff₀ hd2).mp hs
  convert! hs' using 1
  ring

/-- Averaged radial difference estimate, valid even when a displaced radius crosses zero. -/
theorem F_average_difference_le {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (d : ℝ) :
    (F |r - d| h + F |r + d| h) / 2 - F r h ≤
      d^2 / (2 * r) * deriv (fun z => F z h) r := by
  have h₁ := F_average_le_sqrt hh r d
  have h₂ := F_sqrt_increment_le hr hh d
  linarith

end GeneralCK


