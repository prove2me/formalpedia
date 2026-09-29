-- Prove2me | Definitions.Def_CK_CKLaneA1_BSAnalysis
-- name    : CK_CKLaneA1_BSAnalysis
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T17:57:39.045451+00:00
-- url     : https://prove2.me/theorems/57ac778a-5279-491f-8eca-2aeb9ed3db2b
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSAnalysis` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSAnalysis` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSAnalysis` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSAnalysis (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSAnalysis.lean)

import Definitions.Def_CK_CKLaneA1_FEStrip
import Definitions.Def_CK_CKLaneA1_BSIdentities

/-!
# CKLaneA1.BSAnalysis — real-analysis facts for the both-small chart

Elementary log bounds, the mean-value bracket for the divided difference `ĵ`, the monotone
bounds for `θ = δ/(1+pδ)`, and the identities expressing the scaled atoms of the both-small
chart through `r = u/w`, `p = 1/jn w`, `δ = jn u − jn w`.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

theorem log1p_bounds {y : ℝ} (hy : 0 ≤ y) :
    y / (1 + y) ≤ Real.log (1 + y) ∧ Real.log (1 + y) ≤ y := by
  have h1 : 0 < 1 + y := by linarith
  have h1' : 1 + y ≠ 0 := h1.ne'
  constructor
  · have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp <;> ring
    linarith
  · have := Real.log_le_sub_one_of_pos h1
    linarith

theorem neglog1m_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  have h1' : 1 - x ≠ 0 := h1.ne'
  constructor
  · have := Real.log_le_sub_one_of_pos h1
    linarith
  · have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by field_simp <;> ring
    linarith

/-- `δ = jn u − jn w = −log(u/w) + log(1 + (w−u)/(1−w))`. -/
theorem delta_eq {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1) :
    jn u - jn w = -Real.log (u / w) + Real.log (1 + (w - u) / (1 - w)) := by
  have hw0 : 0 < w := hu.trans huw
  have h1u : 1 - u ≠ 0 := (by linarith : (0:ℝ) < 1 - u).ne'
  have h1w : 1 - w ≠ 0 := (by linarith : (0:ℝ) < 1 - w).ne'
  unfold jn
  have e : 1 + (w - u) / (1 - w) = (1 - u) / (1 - w) := by
    field_simp <;> ring
  rw [e, Real.log_div h1u hu.ne', Real.log_div h1w hw0.ne',
    Real.log_div hu.ne' hw0.ne', Real.log_div h1u h1w]
  ring

/-- Mean-value bracket for the divided difference of `jn`. -/
theorem jn_slope_mvt {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w ≤ 1/2) :
    -1 / qp u ≤ (jn w - jn u) / (w - u) ∧ (jn w - jn u) / (w - u) ≤ -1 / qp w := by
  have hcont : ContinuousOn jn (Set.Icc u w) := by
    intro x hx
    exact (hasDerivAt_jn (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope jn (fun x => -1/(x*(1-x))) huw hcont
    (fun x hx => hasDerivAt_jn (by linarith [hx.1]) (by linarith [hx.2]))
  rw [← hceq]
  have hc0 : 0 < c := hu.trans hc.1
  have hqu : 0 < qp u := by unfold qp; nlinarith
  have hqc : qp u ≤ qp c := qp_mono hu.le hc.1.le (by linarith [hc.2])
  have hqw : qp c ≤ qp w := qp_mono hc0.le hc.2.le hw
  have hqc0 : 0 < qp c := hqu.trans_le hqc
  constructor
  · change -1 / qp u ≤ -1 / (c * (1 - c))
    have e : c * (1 - c) = qp c := rfl
    rw [e, div_le_div_iff₀ hqu hqc0]
    nlinarith
  · change -1 / (c * (1 - c)) ≤ -1 / qp w
    have e : c * (1 - c) = qp c := rfl
    rw [e, div_le_div_iff₀ hqc0 (hqc0.trans_le hqw)]
    nlinarith

theorem theta_lower {p δ phi dlo : ℝ} (hp : 0 ≤ p) (hpp : p ≤ phi) (hd : 0 ≤ dlo) (hdd : dlo ≤ δ) :
    dlo / (1 + phi * dlo) ≤ δ / (1 + p * δ) := by
  have h1 : 0 < 1 + phi * dlo := by nlinarith [mul_nonneg (hp.trans hpp) hd]
  have h2 : 0 < 1 + p * δ := by nlinarith [mul_nonneg hp (hd.trans hdd)]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (mul_nonneg hd (hd.trans hdd)) (sub_nonneg.mpr hpp)]

theorem theta_upper {p δ plo dhi : ℝ} (hplo : 0 ≤ plo) (hpp : plo ≤ p) (hd : 0 ≤ δ) (hdd : δ ≤ dhi) :
    δ / (1 + p * δ) ≤ dhi / (1 + plo * dhi) := by
  have h1 : 0 < 1 + p * δ := by nlinarith [mul_nonneg (hplo.trans hpp) hd]
  have h2 : 0 < 1 + plo * dhi := by nlinarith [mul_nonneg hplo (hd.trans hdd)]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (mul_nonneg hd (hd.trans hdd)) (sub_nonneg.mpr hpp)]

theorem theta_le_inv {p δ plo : ℝ} (hplo : 0 < plo) (hpp : plo ≤ p) (hd : 0 ≤ δ) :
    δ / (1 + p * δ) ≤ 1 / plo := by
  have h1 : 0 < 1 + p * δ := by nlinarith [mul_nonneg (hplo.le.trans hpp) hd]
  rw [div_le_div_iff₀ h1 hplo]
  nlinarith [mul_le_mul_of_nonneg_left hpp hd]

theorem wjn_tail {w w2 : ℝ} (hw : 0 < w) (hww : w ≤ w2) (hw2 : w2 ≤ 1/4) :
    w * jn w ≤ w2 * (-Real.log w2) := by
  have h2 : jn w ≤ -Real.log w := by
    unfold jn
    rw [Real.log_div (by linarith) hw.ne']
    have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - w) (by linarith)
    linarith
  have h4 : 1 ≤ -Real.log w2 := by
    have hw2p : 0 < w2 := hw.trans_le hww
    have hl : Real.log w2 ≤ Real.log (1/4) := Real.log_le_log hw2p hw2
    have h4' : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have h2' : 1 - (2:ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    linarith
  calc w * jn w ≤ w * (-Real.log w) := mul_le_mul_of_nonneg_left h2 hw.le
    _ ≤ w2 * (-Real.log w2) := mul_neglog_le hw hww h4

theorem neglog_ge_one {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1/4) : 1 ≤ -Real.log r := by
  have hl : Real.log r ≤ Real.log (1/4) := Real.log_le_log hr hr2
  have h4' : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1/4 : ℝ) = (2^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
  have h2' : 1 - (2:ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos (by norm_num)
  linarith

/-! ## Scaled atoms of the both-small chart -/

/-- `S·p/w = r/τ + 1 + p·(A_u + λ_w)` with `A_u = −log(1−u)/w`, `λ_w = −log(1−w)/w`. -/
theorem Sp_eq {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    (1 / jn w) * entropySum u w / w =
      (u / w) * (jn u / jn w) + 1 + (1 / jn w) * ((-Real.log (1 - u)) / w + (-Real.log (1 - w)) / w) := by
  have hw0 : 0 < w := hu.trans huw
  have hJw := natural_jn_nonzero hw0 hw
  have hw0' : w ≠ 0 := hw0.ne'
  unfold entropySum
  rw [hn_eq_mul_jn hu (by linarith), hn_eq_mul_jn hw0 (by linarith)]
  field_simp <;> ring

theorem kh_eq {u w : ℝ} (hw0 : 0 < w) (hJw : jn w ≠ 0) :
    (1 / jn w) * (qp u * jn u) / w = (1 - u) * ((u / w) * (jn u / jn w)) := by
  have hw0' : w ≠ 0 := hw0.ne'
  unfold qp; field_simp <;> ring

theorem rtau_eq {u w : ℝ} (hJw : jn w ≠ 0) :
    (u / w) * (jn u / jn w) = u / w + (1 / jn w) * ((u / w) * (jn u - jn w)) := by
  have h : jn w / jn w = 1 := div_self hJw
  calc (u / w) * (jn u / jn w)
      = u / w * (jn w / jn w) + (1 / jn w) * ((u / w) * (jn u - jn w)) := by ring
    _ = u / w + (1 / jn w) * ((u / w) * (jn u - jn w)) := by rw [h, mul_one]

theorem tau_eq {u w : ℝ} (hJw : 0 < jn w) (hJu : 0 < jn u) :
    jn w / jn u = 1 / (1 + (1 / jn w) * (jn u - jn w)) := by
  have h1 : jn w ≠ 0 := hJw.ne'
  have h2 : jn u ≠ 0 := hJu.ne'
  have e : 1 + (1 / jn w) * (jn u - jn w) = jn u / jn w := by field_simp <;> ring
  rw [e, one_div_div]

theorem jhat_eq {u w : ℝ} (hw0 : w ≠ 0) (hd : w - u ≠ 0) :
    w * ((jn w - jn u) / (w - u)) = -((jn u - jn w) / ((w - u) / w)) := by
  field_simp <;> ring

theorem qjh_eq {u w : ℝ} (hw0 : w ≠ 0) (hd : w - u ≠ 0) :
    (qp u / w) * (w * ((jn w - jn u) / (w - u))) =
      -((1 - u) * ((u / w) * (jn u - jn w)) / ((w - u) / w)) := by
  unfold qp; field_simp <;> ring

theorem sigma_eq {u w : ℝ} (hw0 : w ≠ 0) (hd : w - u ≠ 0) (hJu : jn u ≠ 0) :
    -(jn w / jn u) * (w * ((jn w - jn u) / (w - u))) =
      (jn w / jn u) * (jn u - jn w) / ((w - u) / w) := by
  field_simp <;> ring

theorem theta_eq {u w : ℝ} (hJw : 0 < jn w) (hJu : 0 < jn u) :
    (jn w / jn u) * (jn u - jn w) = (jn u - jn w) / (1 + (1 / jn w) * (jn u - jn w)) := by
  have h1 : jn w ≠ 0 := hJw.ne'
  have h2 : jn u ≠ 0 := hJu.ne'
  have e : 1 + (1 / jn w) * (jn u - jn w) = jn u / jn w := by field_simp <;> ring
  rw [e, div_div_eq_mul_div]
  field_simp <;> ring

#print axioms log1p_bounds
#print axioms neglog1m_bounds
#print axioms delta_eq
#print axioms jn_slope_mvt
#print axioms theta_lower
#print axioms theta_upper
#print axioms theta_le_inv
#print axioms wjn_tail
#print axioms Sp_eq

end CKLaneA1


