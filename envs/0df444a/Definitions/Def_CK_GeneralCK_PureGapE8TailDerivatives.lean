-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8TailDerivatives
-- name    : CK_GeneralCK_PureGapE8TailDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:45:40.426308+00:00
-- url     : https://prove2.me/theorems/eff91077-15e3-43d0-a72f-ffaf383bdce5
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8TailDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8TailDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8TailDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8TailDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8TailDerivatives.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8TailParameters
import Definitions.Def_CK_GeneralCK_PureGapE8TailAlgebra

-- ===== source module GeneralCK.PureGapE8TailDerivatives =====
section

namespace GeneralCK

open Set Filter Certificates.Mixed

theorem profile_eq_e8TailScaledProfile {v : ℝ} (hv : 0 < v) (hvh : v < 1 / 2) :
    profile v = e8TailScaledProfile v (e8TailE v) (e8TailW v) / Real.log 2 := by
  have hk : kap v ≠ 0 := (kap_pos hv hvh).ne'
  have hc : 1-v ≠ 0 := by linarith
  unfold profile
  rw [hn_eq_tail_parameters hv hvh]
  unfold e8TailScaledProfile e8TailW
  field_simp [hk, hc, hv.ne', log_two_pos.ne']
  ring

theorem e8_tail_profile_bounds {x : ℝ} (hx : 0 < x) (hy : 20 ≤ e8Theta x) :
    57 / 40 ≤ profile (radialContact (2*x) 1) ∧
      profile (radialContact (2*x) 1) ≤ 25 / 16 := by
  obtain ⟨hv0, hvU, he0, heU, hw0, hwU⟩ := e8_tail_parameter_bounds hx hy
  have hp := e8Tail_scaled_profile_bounds hv0.le hvU he0 heU hw0.le hwU
  have hvh : radialContact (2*x) 1 < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  rw [profile_eq_e8TailScaledProfile hv0 hvh]
  have hlo := log_two_gt_69.le
  have hhi := Certificates.PilotData.log_two.2
  norm_num only [div_one] at hhi
  constructor
  · apply (le_div_iff₀ log_two_pos).2
    linarith only [hp.1, hhi]
  · apply (div_le_iff₀ log_two_pos).2
    linarith only [hp.2, hlo]

theorem e8RegularQ_deriv_eq_contact {y : ℝ} (hy : y ∈ e8SlopeRange) :
    deriv e8RegularQ y = e8Q y / profile (radialContact (2 * e8Q y) 1) := by
  have heq : e8RegularQ =ᶠ[nhds y] e8Q := by
    filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
    exact e8RegularQ_eq_e8Q hz.le
  rw [heq.deriv_eq, deriv_e8Q hy, deriv_e8Theta_eq_profile (e8Q_pos hy), inv_div]

theorem e8_tail_inverse_first_bounds {y : ℝ} (hy : y ∈ e8SlopeRange) (hy20 : 20 ≤ y) :
    3 / 5 * e8RegularQ y ≤ deriv e8RegularQ y ∧
      deriv e8RegularQ y ≤ 3 / 4 * e8RegularQ y := by
  have hx := e8Q_pos hy
  have hp := e8_tail_profile_bounds hx (by simpa only [e8Theta_e8Q hy] using hy20)
  have hp0 : 0 < profile (radialContact (2 * e8Q y) 1) := by linarith only [hp.1]
  rw [e8RegularQ_deriv_eq_contact hy, e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  have hlo := mul_le_mul_of_nonneg_left hp.1 hx.le
  have hhi := mul_le_mul_of_nonneg_left hp.2 hx.le
  constructor
  · apply (le_div_iff₀ hp0).2
    nlinarith only [hhi, hx]
  · apply (div_le_iff₀ hp0).2
    nlinarith only [hlo, hx]

#print axioms profile_eq_e8TailScaledProfile
#print axioms e8_tail_profile_bounds
#print axioms e8RegularQ_deriv_eq_contact
#print axioms e8_tail_inverse_first_bounds

end GeneralCK

end


