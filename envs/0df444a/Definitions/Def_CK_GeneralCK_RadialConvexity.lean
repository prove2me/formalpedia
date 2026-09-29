-- Prove2me | Definitions.Def_CK_GeneralCK_RadialConvexity
-- name    : CK_GeneralCK_RadialConvexity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:28:12.938341+00:00
-- url     : https://prove2.me/theorems/7c7c9c5d-361f-4ed1-9187-2ada4b88abba
-- title:
--   Courtade–Kumar proof module `GeneralCK.RadialConvexity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.RadialConvexity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.RadialConvexity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.RadialConvexity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/RadialConvexity.lean)

import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Definitions.Def_CK_GeneralCK_EtaMonotone
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

namespace GeneralCK
open Set Filter
open scoped Topology BigOperators

theorem F_nonneg {z h : ℝ} (hz : 0 ≤ z) (hh : 0 < h) : 0 ≤ F z h := by
  rcases hz.eq_or_lt with rfl | hz
  · simp [F]
  · simp only [F, hz.ne', ↓reduceIte]
    exact mul_nonneg hz.le (J_nonneg (radialContact_pos hz hh)
      (radialContact_lt_half hz hh).le)

theorem F_mono_radius {a b h : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hh : 0 < h) :
    F a h ≤ F b h := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa [F] using F_nonneg hab hh
  have hb : 0 < b := ha.trans_le hab
  have hj := J_antitone (radialContact_pos hb hh) (radialContact_lt_half ha hh).le
    (radialContact_anti_radius ha hab hh)
  simp only [F, ha.ne', hb.ne', ↓reduceIte]
  exact mul_le_mul hab hj (J_nonneg (radialContact_pos ha hh)
    (radialContact_lt_half ha hh).le) hb.le

theorem F_le_linear_near_zero {z h : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) (hh : 0 < h) :
    F z h ≤ z * J (radialContact 1 h) := by
  rcases hz.eq_or_lt with rfl | hz
  · simp [F]
  simp only [F, hz.ne', ↓reduceIte]
  exact mul_le_mul_of_nonneg_left
    (J_antitone (radialContact_pos (by norm_num : (0 : ℝ) < 1) hh)
      (radialContact_lt_half hz hh).le (radialContact_anti_radius hz hz' hh)) hz.le

theorem continuousWithinAt_F_zero {h : ℝ} (hh : 0 < h) :
    ContinuousWithinAt (fun z => F z h) (Ici 0) 0 := by
  change Tendsto (fun z => F z h) (𝓝[Ici 0] 0) (𝓝 (F 0 h))
  simp only [F, ↓reduceIte]
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact F_nonneg hz hh
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with z hz hz'
    exact F_le_linear_near_zero hz hz'.le hh
  · have ht := (tendsto_id.mul_const (J (radialContact 1 h))).mono_left
      (show 𝓝[Ici (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa using ht

theorem continuousOn_F_radius {h : ℝ} (hh : 0 < h) :
    ContinuousOn (fun z => F z h) (Ici 0) := by
  intro z hz
  change 0 ≤ z at hz
  rcases hz.eq_or_lt with rfl | hz
  · exact continuousWithinAt_F_zero hh
  · exact (hasDerivAt_F_radius hz hh).continuousAt.continuousWithinAt

theorem kap_sq_gap_nonneg {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    0 ≤ 2 * Certificates.Mixed.kap v - (1 - 2*v)^2 := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  have hl := Real.log_le_sub_one_of_pos hp
  unfold Certificates.Mixed.kap
  nlinarith only [hl, hp]

theorem deriv2_F_radius_nonneg {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 ≤ deriv (deriv (fun r => F r h)) z := by
  rw [(hasDerivAt_deriv_F_radius hz hh).deriv]
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hH := (H_pos hv hv').le
  have hn : 0 ≤ Certificates.Mixed.hn (radialContact z h) := by
    rw [Certificates.Mixed.hn_eq_H_mul_log]
    exact mul_nonneg hH log_two_pos.le
  have hg := kap_sq_gap_nonneg hv hv'
  have hd := (radialContact_denominator_pos hz hh).le
  exact div_nonneg (mul_nonneg (mul_nonneg hn hg) hH) (by positivity)

theorem convexOn_F_radius {h : ℝ} (hh : 0 < h) :
    ConvexOn ℝ (Ici 0) (fun z => F z h) := by
  apply convexOn_of_deriv2_nonneg (convex_Ici 0) (continuousOn_F_radius hh)
  · intro z hz
    exact (hasDerivAt_F_radius (by simpa using hz) hh).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_deriv_F_radius (by simpa using hz) hh).differentiableAt.differentiableWithinAt
  · intro z hz
    exact deriv2_F_radius_nonneg (by simpa using hz) hh

theorem positive_weighted_entropy {a b h₁ h₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    0 < a*h₁+b*h₂ := by
  rcases ha.eq_or_lt with rfl | ha
  · have hb' : b = 1 := by linarith
    simpa [hb'] using hh₂
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hh₁) (mul_nonneg hb hh₂.le)

/-- Convexity of the perspective, including zero radii and zero convex weights. -/
theorem F_convex_combination {a b z₁ z₂ h₁ h₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    F (a*z₁+b*z₂) (a*h₁+b*h₂) ≤ a*F z₁ h₁+b*F z₂ h₂ := by
  let h := a*h₁+b*h₂
  have hp : 0 < h := positive_weighted_entropy ha hb hab hh₁ hh₂
  have hw : a*h₁/h+b*h₂/h = 1 := by rw [← add_div]; exact div_self hp.ne'
  have hc := (convexOn_F_radius (h := 1) (by norm_num)).2
    (show z₁/h₁ ∈ Ici 0 from div_nonneg hz₁ hh₁.le)
    (show z₂/h₂ ∈ Ici 0 from div_nonneg hz₂ hh₂.le)
    (div_nonneg (mul_nonneg ha hh₁.le) hp.le)
    (div_nonneg (mul_nonneg hb hh₂.le) hp.le) hw
  simp only [smul_eq_mul] at hc
  have hx : a*h₁/h*(z₁/h₁)+b*h₂/h*(z₂/h₂) = (a*z₁+b*z₂)/h := by
    field_simp
  rw [hx] at hc
  have hm := mul_le_mul_of_nonneg_left hc hp.le
  rw [F_perspective hp.ne' (a*z₁+b*z₂), F_perspective hh₁.ne' z₁,
    F_perspective hh₂.ne' z₂]
  change h * F ((a*z₁+b*z₂)/h) 1 ≤ _
  convert! hm using 1
  field_simp

theorem convexOn_F_joint :
    ConvexOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 < p.2} (fun p => F p.1 p.2) := by
  constructor
  · intro x hx y hy a b ha hb hab
    change 0 ≤ a*x.1+b*y.1 ∧ 0 < a*x.2+b*y.2
    exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
      positive_weighted_entropy ha hb hab hx.2 hy.2⟩
  · intro x hx y hy a b ha hb hab
    exact F_convex_combination ha hb hab hx.1 hy.1 hx.2 hy.2

/-- Finite-law Jensen inequality for the homogeneous radial profile. -/
theorem F_sum_le {ι : Type*} (s : Finset ι) (w z h : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hh : ∀ i ∈ s, 0 < h i) :
    F (∑ i ∈ s, w i*z i) (∑ i ∈ s, w i*h i) ≤ ∑ i ∈ s, w i*F (z i) (h i) := by
  have hj := convexOn_F_joint.map_sum_le (p := fun i => (z i,h i)) hw hw1
    (fun i hi => And.intro (hz i hi) (hh i hi))
  simpa only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hj

end GeneralCK


