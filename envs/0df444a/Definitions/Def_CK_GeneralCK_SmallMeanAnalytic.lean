-- Prove2me | Definitions.Def_CK_GeneralCK_SmallMeanAnalytic
-- name    : CK_GeneralCK_SmallMeanAnalytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:29:44.27206+00:00
-- url     : https://prove2.me/theorems/8ba0859a-de09-4f16-95f1-41dc5d17da3b
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallMeanAnalytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallMeanAnalytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallMeanAnalytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallMeanAnalytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallMeanAnalytic.lean)

import Definitions.Def_CK_GeneralCK_ProfileLowerBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.SmallMean
open Set




noncomputable def gamma (r : ℝ) : ℝ :=
  2*r^2 / ((1+r)*(1+r/31)*(1-H ((1-r)/2)))

@[simp] theorem Cn_zero : Cn 0 = 0 := by norm_num [Cn]
@[simp] theorem Cn_one : Cn 1 = Real.log 2 := by norm_num [Cn]
@[simp] theorem A_zero : A 0 = 0 := by norm_num [A]

theorem Cn_continuous : Continuous Cn := by
  exact continuous_const.mul (continuous_const.sub
    (H_continuous.comp ((continuous_const.sub continuous_id).div_const 2)))

theorem A_eq_J (r : ℝ) : A r = Real.log 2 / 2 * J ((1-r)/2) := by
  have he : (1 - (1-r)/2) / ((1-r)/2) = (1+r)/(1-r) := by
    by_cases hr : r = 1
    · subst r; norm_num
    · field_simp [show 1-r ≠ 0 by exact sub_ne_zero.mpr (Ne.symm hr)]
      ring
  unfold A J
  rw [he]
  field_simp [log_two_pos.ne']

theorem hasDerivAt_A {r : ℝ} (hr : -1 < r) (hr' : r < 1) :
    HasDerivAt A (1/(1-r^2)) r := by
  have hp : 0 < (1-r)/2 := by linarith
  have hp' : (1-r)/2 < 1 := by linarith
  have hd := (((hasDerivAt_J hp hp').comp r
    (((hasDerivAt_id r).const_sub 1).div_const 2)).const_mul (Real.log 2/2))
  have he : A = fun r => Real.log 2/2 * J ((1-r)/2) := funext A_eq_J
  rw [he]
  convert! hd using 1
  field_simp [log_two_pos.ne', show 1-r ≠ 0 by linarith,
    show 1+r ≠ 0 by linarith, show 1-r^2 ≠ 0 by nlinarith]
  rw [eq_div_iff (show 2-(1-r) ≠ 0 by linarith)]
  ring

theorem hasDerivAt_Cn {r : ℝ} (hr : -1 < r) (hr' : r < 1) : HasDerivAt Cn (A r) r := by
  have hp : 0 < (1-r)/2 := by linarith
  have hp' : (1-r)/2 < 1 := by linarith
  have hd := (((Comparison.hasDerivAt_H hp hp').comp r
    (((hasDerivAt_id r).const_sub 1).div_const 2)).const_sub 1).const_mul (Real.log 2)
  convert! hd using 1
  rw [A_eq_J]; ring

theorem Cn_pos {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) : 0 < Cn r := by
  have hp : 0 ≤ (1-r)/2 := by linarith
  have hp' : (1-r)/2 < 1/2 := by linarith
  have h := H_strictMonoOn ⟨hp, hp'.le⟩ ⟨by norm_num, le_rfl⟩ hp'
  rw [H_half] at h
  exact mul_pos log_two_pos (sub_pos.mpr h)

theorem A_upper {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) : A r ≤ r/(1-r^2) := by
  have hp : 0 < (1-r)/2 := by linarith
  have hp' : (1-r)/2 ≤ 1/2 := by linarith
  have h := Scalar.logit_slope_bound hp hp'
  rw [A_eq_J]
  apply (le_div_iff₀ (show 0 < 1-r^2 by nlinarith)).2
  nlinarith

theorem A_lower {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) : r ≤ A r := by
  have h := Real.sum_range_le_log_div hr hr' 1
  norm_num at h
  unfold A
  linarith

theorem Cn_dilation_derivative_nonneg {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    0 ≤ r*A r - 2*Cn r := by
  let g : ℝ → ℝ := fun r => r*A r - 2*Cn r
  have hd : ∀ r ∈ Ico (0 : ℝ) 1,
      HasDerivAt g (r/(1-r^2)-A r) r := by
    intro r hr
    have h := ((hasDerivAt_id r).mul (hasDerivAt_A (by linarith [hr.1]) hr.2)).sub
      ((hasDerivAt_Cn (by linarith [hr.1]) hr.2).const_mul 2)
    convert! h using 1
    simp only [id_eq]; ring
  have hm : MonotoneOn g (Ico 0 1) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
    (fun r hr => sub_nonneg.mpr (A_upper (interior_subset hr).1 (interior_subset hr).2))
  have h := hm (by norm_num : (0 : ℝ) ∈ Ico 0 1) ⟨hr,hr'⟩ hr
  simpa [g] using h

theorem Cn_ratio_monotone : MonotoneOn (fun r => Cn r/r^2) (Ioc 0 1) := by
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r => Cn r/r^2)
      ((r*A r-2*Cn r)/r^3) r := by
    intro r hr
    have h := (hasDerivAt_Cn (by linarith [hr.1]) hr.2).div
      ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr.1.ne')
    convert! h using 1
    simp only [Pi.pow_apply, id_eq]; field_simp [hr.1.ne']; ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1)
  · intro r hr
    exact (Cn_continuous.continuousAt.div (continuousAt_id.pow 2) (pow_ne_zero 2 hr.1.ne')).continuousWithinAt
  · intro r hr
    exact (hd r (by simpa only [interior_Ioc] using hr)).hasDerivWithinAt
  · intro r hr
    rw [interior_Ioc] at hr
    exact div_nonneg (Cn_dilation_derivative_nonneg hr.1.le hr.2) (pow_pos hr.1 3).le

theorem gamma_eq {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    gamma r = 2*Real.log 2 / ((1+r)*(1+r/31)*(Cn r/r^2)) := by
  have hc := (Cn_pos hr hr').ne'
  have he : 1-H ((1-r)/2) ≠ 0 := by
    intro he; apply hc; simp [Cn,he]
  unfold gamma Cn
  field_simp [he,log_two_pos.ne',hr.ne', show 1+r ≠ 0 by linarith,
    show 1+r/31 ≠ 0 by linarith]

theorem gamma_pos {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) : 0 < gamma r := by
  rw [gamma_eq hr hr']
  have hc := Cn_pos hr hr'
  positivity

theorem gamma_antitone : AntitoneOn gamma (Ioc 0 1) := by
  intro r hr s hs hrs
  have hr0 : 0 < r := hr.1
  have hs0 : 0 < s := hs.1
  rw [gamma_eq hr.1 hr.2, gamma_eq hs.1 hs.2]
  have hc := Cn_pos hr.1 hr.2
  have hratio := Cn_ratio_monotone hr hs hrs
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply mul_le_mul
  · apply mul_le_mul <;> linarith [hr.1,hs.1]
  · exact hratio
  · exact div_nonneg hc.le (sq_nonneg _)
  · positivity

end GeneralCK.SmallMean


