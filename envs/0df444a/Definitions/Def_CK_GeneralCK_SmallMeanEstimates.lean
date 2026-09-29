-- Prove2me | Definitions.Def_CK_GeneralCK_SmallMeanEstimates
-- name    : CK_GeneralCK_SmallMeanEstimates
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:05.480215+00:00
-- url     : https://prove2.me/theorems/cf7a84de-9064-4769-a9df-176ac35119b8
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallMeanEstimates` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallMeanEstimates` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallMeanEstimates` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallMeanEstimates (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallMeanEstimates.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanAnalytic

namespace GeneralCK.SmallMean
open Set

theorem Cn_ge_half_sq {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) : r^2/2 ≤ Cn r := by
  have hm : MonotoneOn (fun r => Cn r-r^2/2) (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun r => A r-r)
    · exact Cn_continuous.continuousOn.sub ((continuous_id.pow 2).div_const 2).continuousOn
    · intro r hr
      rw [interior_Icc] at hr
      have h := (hasDerivAt_Cn (by linarith [hr.1]) hr.2).sub
        (((hasDerivAt_id r).pow 2).div_const 2)
      convert! h.hasDerivWithinAt using 1
      simp
    · intro r hr
      rw [interior_Icc] at hr
      exact sub_nonneg.mpr (A_lower hr.1.le hr.2)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨hr,hr'⟩ hr
  simp only [Cn_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero] at h
  linarith

theorem Cn_le_log_mul_sq {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    Cn r ≤ Real.log 2*r^2 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have h := Cn_ratio_monotone ⟨hr,hr'⟩ ⟨by norm_num,le_rfl⟩ hr'
  simpa using (div_le_iff₀ (sq_pos_of_pos hr)).mp (by simpa using h)

theorem Cn_scale_le {r k : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hk : 0 ≤ k) (hk' : k ≤ 1) :
    Cn (k*r) ≤ k^2*Cn r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rcases hk.eq_or_lt with rfl | hk
  · simp
  have hkr : 0 < k*r := mul_pos hk hr
  have hkr' : k*r ≤ r := mul_le_of_le_one_left hr.le hk'
  have h := Cn_ratio_monotone ⟨hkr,hkr'.trans hr'⟩ ⟨hr,hr'⟩ hkr'
  have hc := (div_le_div_iff₀ (sq_pos_of_pos hkr) (sq_pos_of_pos hr)).mp h
  nlinarith [sq_pos_of_pos hr]

theorem gamma_le_four_log {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    gamma r ≤ 4*Real.log 2 := by
  rw [gamma_eq hr hr']
  have hc := Cn_pos hr hr'
  have hratio : (1/2 : ℝ) ≤ Cn r/r^2 :=
    (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith [Cn_ge_half_sq hr.le hr'])
  have hprod : 1 ≤ (1+r)*(1+r/31) := by nlinarith
  have hden := mul_le_mul hprod hratio (by norm_num : (0 : ℝ) ≤ 1/2) (by positivity)
  apply (div_le_iff₀ (show 0 < (1+r)*(1+r/31)*(Cn r/r^2) by positivity)).mpr
  nlinarith [log_two_pos, mul_nonneg log_two_pos.le (sub_nonneg.mpr hden)]

theorem A_upper_sharp {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    A r ≤ r+r^3/(3*(1-r^2)) := by
  let g : ℝ → ℝ := fun r => r+r^3/(3*(1-r^2))-A r
  have hd : ∀ r ∈ Ico (0 : ℝ) 1, HasDerivAt g (2*r^4/(3*(1-r^2)^2)) r := by
    intro r hr
    have hn : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
    have h := ((hasDerivAt_id r).add (((hasDerivAt_id r).pow 3).div
      ((((hasDerivAt_id r).pow 2).const_sub 1).const_mul 3) (by positivity))).sub
      (hasDerivAt_A (by linarith [hr.1]) hr.2)
    convert! h using 1
    simp only [id_eq,Pi.pow_apply]
    field_simp [hn.ne']; ring
  have hm : MonotoneOn g (Ico 0 1) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
    (fun r hr => by positivity)
  have h := hm (by norm_num : (0 : ℝ) ∈ Ico 0 1) ⟨hr,hr'⟩ hr
  dsimp [g] at h
  simp only [A_zero,zero_pow (by norm_num : 3 ≠ 0),zero_pow (by norm_num : 2 ≠ 0),
    zero_div,zero_add,sub_self] at h
  linarith

/-- The coefficient comparison from the source, proved by differentiation. -/
theorem mean_cost_bonus {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    (2/3 : ℝ)*r^2*Cn r ≤ 2*r*A r-4*Cn r := by
  let g : ℝ → ℝ := fun r => 2*r*A r-(4+2*r^2/3)*Cn r
  let d : ℝ → ℝ := fun r => 2*r/(1-r^2)-(2+2*r^2/3)*A r-(4*r/3)*Cn r
  have hd : ∀ r ∈ Ico (0 : ℝ) 1, HasDerivAt g (d r) r := by
    intro r hr
    have ha := hasDerivAt_A (by linarith [hr.1]) hr.2
    have hc := hasDerivAt_Cn (by linarith [hr.1]) hr.2
    have h := (((hasDerivAt_id r).const_mul 2).mul ha).sub
      ((((((hasDerivAt_id r).pow 2).const_mul 2).div_const 3).const_add 4).mul hc)
    convert! h using 1
    dsimp only [d,id_eq,Pi.pow_apply]
    ring
  have hdpos : ∀ r ∈ Ico (0 : ℝ) 1, 0 ≤ d r := by
    intro r hr
    have hn : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
    have hc := Cn_dilation_derivative_nonneg hr.1 hr.2
    have ha := A_upper_sharp hr.1 hr.2
    have h₁ := mul_le_mul_of_nonneg_left (show Cn r ≤ r*A r/2 by linarith)
      (show 0 ≤ 4*r/3 by linarith [hr.1])
    have h₂ := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2+4*r^2/3 by positivity)
    have he : 2*r/(1-r^2)-(2+4*r^2/3)*(r+r^3/(3*(1-r^2))) =
        8*r^5/(9*(1-r^2)) := by field_simp [hn.ne']; ring
    have hp : 0 ≤ 8*r^5/(9*(1-r^2)) := by have := hr.1; positivity
    dsimp [d]
    nlinarith [he]
  have hm : MonotoneOn g (Ico 0 1) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
    (fun r hr => hdpos r (interior_subset hr))
  have h := hm (by norm_num : (0 : ℝ) ∈ Ico 0 1) ⟨hr,hr'⟩ hr
  dsimp [g] at h
  simp only [Cn_zero,A_zero,mul_zero,sub_self] at h
  linarith

end GeneralCK.SmallMean


