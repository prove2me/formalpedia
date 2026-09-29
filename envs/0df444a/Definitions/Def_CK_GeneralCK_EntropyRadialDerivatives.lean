-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
-- name    : CK_GeneralCK_EntropyRadialDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:37:33.518276+00:00
-- url     : https://prove2.me/theorems/c8cea11a-4a34-4b2d-8216-d7304ff22e99
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyRadialDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyRadialDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyRadialDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyRadialDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyRadialDerivatives.lean)

import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_MixedDerivative
import Definitions.Def_CK_GeneralCK_RadialConvexity

namespace GeneralCK
open Set Filter
open scoped Topology

theorem deriv_F_radius_normalize {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z = deriv (fun r => F r 1) (z/h) := by
  rw [deriv_F_radius_slope hz hh,
    deriv_F_radius_slope (div_pos hz hh) (by norm_num),
    radialContact_normalize_entropy z hh.ne']

theorem deriv2_F_radius_normalize {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (deriv (fun r => F r h)) z =
      (1/h)*deriv (deriv (fun r => F r 1)) (z/h) := by
  have hd := (hasDerivAt_deriv_F_radius (h := 1) (div_pos hz hh) (by norm_num)).differentiableAt.hasDerivAt
  have hc := hd.comp z ((hasDerivAt_id z).div_const h)
  have heq : deriv (fun r => F r h) =ᶠ[𝓝 z] (fun r => deriv (fun s => F s 1) (r/h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    exact deriv_F_radius_normalize hr hh
  have hh' := (hc.congr_of_eventuallyEq heq).deriv
  simpa only [mul_comm] using hh'

/-- Derivative in entropy of the radial first derivative. -/
theorem hasDerivAt_deriv_F_radius_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun q => deriv (fun r => F r q) z)
      (-(z/h)*deriv (deriv (fun r => F r h)) z) h := by
  have hd := (hasDerivAt_deriv_F_radius (h := 1) (div_pos hz hh) (by norm_num)).differentiableAt.hasDerivAt
  have hw := (hasDerivAt_const h z).div (hasDerivAt_id h) hh.ne'
  have hc := hd.comp h hw
  have heq : (fun q => deriv (fun r => F r q) z) =ᶠ[𝓝 h]
      (fun q => deriv (fun r => F r 1) (z/q)) := by
    filter_upwards [Ioi_mem_nhds hh] with q hq
    exact deriv_F_radius_normalize hz hq
  have hd' := hc.congr_of_eventuallyEq heq
  convert! hd' using 1
  rw [deriv2_F_radius_normalize hz hh]
  dsimp only [id_eq, Function.comp_apply, Pi.div_apply]
  field_simp
  ring

theorem deriv_F_radius_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun q => deriv (fun r => F r q) z) h =
      -(z/h)*deriv (deriv (fun r => F r h)) z :=
  (hasDerivAt_deriv_F_radius_entropy hz hh).deriv

theorem hasDerivAt_F_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (F z)
      (F (z/h) 1 - (z/h)*deriv (fun r => F r 1) (z/h)) h := by
  have hd := (hasDerivAt_F_radius (h := 1) (div_pos hz hh) (by norm_num)).differentiableAt.hasDerivAt
  have hw := (hasDerivAt_const h z).div (hasDerivAt_id h) hh.ne'
  have hc := (hasDerivAt_id h).mul (hd.comp h hw)
  have heq : F z =ᶠ[𝓝 h] (fun q => q*F (z/q) 1) := by
    filter_upwards [Ioi_mem_nhds hh] with q hq
    exact F_perspective hq.ne' z
  have hd' := hc.congr_of_eventuallyEq heq
  convert! hd' using 1
  dsimp only [id_eq, Function.comp_apply, Pi.div_apply]
  field_simp
  ring

theorem deriv_F_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (F z) h = F (z/h) 1 - (z/h)*deriv (fun r => F r 1) (z/h) :=
  (hasDerivAt_F_entropy hz hh).deriv

/-- The entropy second derivative is the radial second derivative times the
square of the radius-to-entropy ratio. -/
theorem hasDerivAt_deriv_F_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (deriv (F z))
      ((z/h)^2*deriv (deriv (fun r => F r h)) z) h := by
  have hd := (hasDerivAt_F_radius (h := 1) (div_pos hz hh) (by norm_num)).differentiableAt.hasDerivAt
  have hd2 := (hasDerivAt_deriv_F_radius (h := 1) (div_pos hz hh) (by norm_num)).differentiableAt.hasDerivAt
  have hw := (hasDerivAt_const h z).div (hasDerivAt_id h) hh.ne'
  have hc := (hd.comp h hw).sub (hw.mul (hd2.comp h hw))
  have heq : deriv (F z) =ᶠ[𝓝 h]
      (fun q => F (z/q) 1 - (z/q)*deriv (fun r => F r 1) (z/q)) := by
    filter_upwards [Ioi_mem_nhds hh] with q hq
    exact deriv_F_entropy hz hq
  have hd' := hc.congr_of_eventuallyEq heq
  convert! hd' using 1
  rw [deriv2_F_radius_normalize hz hh]
  dsimp only [id_eq, Function.comp_apply, Pi.div_apply]
  field_simp
  ring

theorem deriv2_F_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (deriv (F z)) h = (z/h)^2*deriv (deriv (fun r => F r h)) z :=
  (hasDerivAt_deriv_F_entropy hz hh).deriv

theorem deriv2_F_entropy_le {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (deriv (F z)) h ≤ 13*z/(6*h^2) := by
  have hb := mul_le_mul_of_nonneg_left (global_mixed_derivative_bound hz hh)
    (show 0 ≤ z/h^2 by positivity)
  rw [deriv2_F_entropy hz hh]
  convert! hb using 1 <;> ring

/-- The analytic profile in radius/entropy coordinates, before replacing the
radius by the absolute mean imbalance. -/
noncomputable def radialPhi (z h : ℝ) : ℝ := eta h - F z h

theorem hasDerivAt_radialPhi_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => radialPhi r h) (-deriv (fun r => F r h) z) z :=
  ((hasDerivAt_F_radius hz hh).differentiableAt.hasDerivAt).const_sub (eta h)

theorem deriv_radialPhi_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => radialPhi r h) z = -deriv (fun r => F r h) z :=
  (hasDerivAt_radialPhi_radius hz hh).deriv

theorem hasDerivAt_deriv_radialPhi_radius_entropy {z h : ℝ}
    (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun q => deriv (fun r => radialPhi r q) z)
      ((z/h)*deriv (deriv (fun r => F r h)) z) h := by
  have hd := (hasDerivAt_deriv_F_radius_entropy hz hh).neg
  have heq : (fun q => deriv (fun r => radialPhi r q) z) =ᶠ[𝓝 h]
      (fun q => -deriv (fun r => F r q) z) := by
    filter_upwards [Ioi_mem_nhds hh] with q hq
    exact deriv_radialPhi_radius hz hq
  simpa only [neg_mul, neg_neg] using hd.congr_of_eventuallyEq heq

theorem deriv_radialPhi_radius_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun q => deriv (fun r => radialPhi r q) z) h =
      (z/h)*deriv (deriv (fun r => F r h)) z :=
  (hasDerivAt_deriv_radialPhi_radius_entropy hz hh).deriv

theorem deriv_radialPhi_radius_entropy_le {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun q => deriv (fun r => radialPhi r q) z) h ≤ 13/(6*h) := by
  have hb := mul_le_mul_of_nonneg_left (global_mixed_derivative_bound hz hh)
    (show 0 ≤ 1/h by positivity)
  rw [deriv_radialPhi_radius_entropy hz hh]
  convert! hb using 1 <;> ring

theorem deriv_radialPhi_radius_entropy_nonneg {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 ≤ deriv (fun q => deriv (fun r => radialPhi r q) z) h := by
  rw [deriv_radialPhi_radius_entropy hz hh]
  exact mul_nonneg (div_pos hz hh).le (deriv2_F_radius_nonneg hz hh)

theorem deriv2_F_entropy_nonneg {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 ≤ deriv (deriv (F z)) h := by
  rw [deriv2_F_entropy hz hh]
  exact mul_nonneg (sq_nonneg _) (deriv2_F_radius_nonneg hz hh)

end GeneralCK


