-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Bound
-- name    : CK_CKLaneM07_CE_R3Bound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:53:34.246149+00:00
-- url     : https://prove2.me/theorems/1445c3a2-aa45-478e-8ffb-456e41910902
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Bound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Bound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Bound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Bound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Bound.lean)

import Definitions.Def_CK_CKLaneM07_CE_GapLB
import Definitions.Def_CK_CKLaneN1_EdgeAlg
import Definitions.Def_CK_GeneralCK_EntropyCurvatureStrict

-- ===== source module CKLaneM07.CE.R3Bound =====
section

/-!
# Lane M07 / CE-stat row 3: analytic ingredients of the box bound for `gapLB`

For `0 < a < b < c < 1/2` (with `e = H a`, `f = H b`, `h = (e+f)/2`, `q = ι h`, `M = (a+b)/2`,
`t_C = rc(1 − 2c, f)`):

`gapLB = [F(c−a,h) − F(b−a,h)] + interiorCost a b − Υ(q)(a + b − 2q) − (Υ(q) − Υ(t_C))(c − b)`,

and each piece is bounded by quantities that a rational box checker can evaluate:
* `ratio`: `F(c−a,h) − F(b−a,h) ≥ (Θ(X)/X)((c−a)² − (b−a)²)/(4h)` for `X ≥ (c−a)/(2h)` (N1);
* `interiorCost a b ≥ (b−a)²/((a+b) log 2)` (N1);
* Jensen: `a ≤ q ≤ M`, `J(M)(M − q) ≤ H(M) − h` (N1 `q_facts`);
* `Υ` antitone and positive on `(0,1/2)`; `Υ(u) − Υ(v) ≤ D (v − u)` with an explicit `D` from the
  corpus derivative of `radialSlope`;
* contact step: `t_C − b ≤ 2 (c − b) · H(c)/((1−2c) J(c) + 2f)`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3

open GeneralCK GeneralCK.Certificates.Mixed Set CKLaneN1.Edge

theorem log2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

/-! ## Υ = radialSlope -/

theorem hn_pos' {v : ℝ} (hv : 0 < v) (hv' : v < 1) : 0 < hn v := by
  rw [hn_eq_H_mul_log]; exact mul_pos (H_pos hv hv') log2_pos

theorem ups_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < radialSlope v := by
  unfold radialSlope
  have hJ := J_pos hv hv'
  have hk := kap_pos hv hv'
  have hn := hn_pos' hv (by linarith)
  have hL := log2_pos
  have h1 : 0 < 1 - 2 * v := by linarith
  have h2 : 0 < 1 - v := by linarith
  positivity

theorem ups_anti {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1 / 2) :
    radialSlope v ≤ radialSlope u :=
  ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ⟨hu, by linarith⟩ ⟨by linarith, hv⟩ huv

theorem hn_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : hn u ≤ hn v := by
  rw [hn_eq_H_mul_log, hn_eq_H_mul_log]
  exact mul_le_mul_of_nonneg_right (H_mono hu.le huv hv) log2_pos.le

theorem kap_anti {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : kap v ≤ kap u := by
  unfold kap
  have h2 : 0 < u * (1 - u) := mul_pos hu (by linarith)
  have h1 : u * (1 - u) ≤ v * (1 - v) := by nlinarith
  have := Real.log_le_log h2 h1
  linarith

/-- the magnitude of `Υ'` (corpus `hasDerivAt_radialSlope`) -/
noncomputable def dUps (w : ℝ) : ℝ :=
  hn w * (2 * kap w - (1 - 2 * w) ^ 2) / (4 * Real.log 2 * w ^ 2 * (1 - w) ^ 2 * kap w ^ 2)

/-- explicit bound of `|Υ'|` on `[u, v] ⊂ (0, 1/2)` -/
noncomputable def dUpsBound (u v : ℝ) : ℝ :=
  hn v * (2 * kap u) / (4 * Real.log 2 * u ^ 2 * (1 - v) ^ 2 * kap v ^ 2)

theorem dUps_le {u v w : ℝ} (hu : 0 < u) (huw : u ≤ w) (hwv : w ≤ v) (hv : v < 1 / 2) :
    dUps w ≤ dUpsBound u v := by
  unfold dUps dUpsBound
  have hw : 0 < w := hu.trans_le huw
  have hkw := kap_pos hw (by linarith)
  have hkv := kap_pos (hu.trans_le (huw.trans hwv)) hv
  have hgap := kap_sq_gap_pos hw (by linarith)
  have hL := log2_pos
  have hnw := hn_pos' hw (by linarith)
  have hn1 : hn w ≤ hn v := hn_mono hw hwv hv.le
  have hk1 : kap w ≤ kap u := kap_anti hu huw (by linarith)
  have hk2 : kap v ≤ kap w := kap_anti hw hwv hv.le
  have hnum : hn w * (2 * kap w - (1 - 2 * w) ^ 2) ≤ hn v * (2 * kap u) := by
    have h3 : 2 * kap w - (1 - 2 * w) ^ 2 ≤ 2 * kap u := by nlinarith [sq_nonneg (1 - 2 * w)]
    exact mul_le_mul hn1 h3 hgap.le (hnw.le.trans hn1)
  have hden : 4 * Real.log 2 * u ^ 2 * (1 - v) ^ 2 * kap v ^ 2 ≤
      4 * Real.log 2 * w ^ 2 * (1 - w) ^ 2 * kap w ^ 2 := by
    have e1 : u ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hu.le huw 2
    have e2 : (1 - v) ^ 2 ≤ (1 - w) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have e3 : kap v ^ 2 ≤ kap w ^ 2 := pow_le_pow_left₀ hkv.le hk2 2
    have p1 : 0 ≤ 4 * Real.log 2 := by positivity
    have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left e1 p1) e2 (by positivity) (by positivity))
      e3 (by positivity) (by positivity)
    simpa [mul_assoc] using this
  have hdpos : 0 < 4 * Real.log 2 * u ^ 2 * (1 - v) ^ 2 * kap v ^ 2 := by
    have : 0 < 1 - v := by linarith
    positivity
  have hnv := hn_pos' (hu.trans_le (huw.trans hwv)) (by linarith)
  have hku := kap_pos hu (by linarith)
  exact div_le_div₀ (mul_nonneg hnv.le (by linarith)) hnum hdpos hden

theorem hasDerivAt_ups {w : ℝ} (hw : 0 < w) (hw' : w < 1 / 2) :
    HasDerivAt radialSlope (-dUps w) w := by
  have h := hasDerivAt_radialSlope hw hw'
  convert h using 1
  unfold dUps
  ring

/-- mean-value bound for the decreasing `Υ` -/
theorem ups_sub_le {u v D : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1 / 2)
    (hD : ∀ w ∈ Icc u v, dUps w ≤ D) : radialSlope u - radialSlope v ≤ D * (v - u) := by
  have hg : ∀ w ∈ Icc u v, HasDerivAt (fun x => radialSlope x + D * x) (-dUps w + D) w := by
    intro w hw
    exact (hasDerivAt_ups (hu.trans_le hw.1) (lt_of_le_of_lt hw.2 hv)).add
      ((hasDerivAt_id w).const_mul D |>.congr_deriv (by simp))
  have hmono : MonotoneOn (fun x => radialSlope x + D * x) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
    · intro w hw; exact (hg w hw).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact (hg w ⟨hw.1.le, hw.2.le⟩).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hg w ⟨hw.1.le, hw.2.le⟩).deriv]
      linarith [hD w ⟨hw.1.le, hw.2.le⟩]
  have := hmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  simp only at this
  linarith

/-! ## the contact step -/

theorem cap_contact_H {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) :
    radialContact (1 - 2 * b) (H b) = b :=
  radialContact_eq_of_equation (by linarith) (H_pos hb (by linarith)) hb hb' (by ring)

theorem contact_lt {b c : ℝ} (hb : 0 < b) (hbc : b < c) (hc : c < 1 / 2) :
    radialContact (1 - 2 * c) (H b) < c := by
  have hf := H_pos hb (by linarith)
  have hz : 0 < 1 - 2 * c := by linarith
  by_contra hn
  push Not at hn
  have heq := radialContact_equation hz hf
  have hl := radialContact_lt_half hz hf
  have hH : H b < H (radialContact (1 - 2 * c) (H b)) :=
    H_strictMonoOn ⟨hb.le, by linarith⟩ ⟨by linarith, hl.le⟩ (lt_of_lt_of_le hbc hn)
  have h1 : (1 - 2 * c) * H b < (1 - 2 * c) * H (radialContact (1 - 2 * c) (H b)) :=
    mul_lt_mul_of_pos_left hH hz
  have h2 : H b * (1 - 2 * radialContact (1 - 2 * c) (H b)) ≤ H b * (1 - 2 * c) :=
    mul_le_mul_of_nonneg_left (by linarith) hf.le
  linarith

theorem contact_step {b c : ℝ} (hb : 0 < b) (hbc : b < c) (hc : c < 1 / 2) :
    radialContact (1 - 2 * c) (H b) - b ≤
      2 * (c - b) * (H c / ((1 - 2 * c) * J c + 2 * H b)) := by
  set f := H b with hf_def
  have hf : 0 < f := H_pos hb (by linarith)
  have hc1 : 0 < 1 - 2 * c := by linarith
  have hJc := J_pos (hb.trans hbc) hc
  set K := H c / ((1 - 2 * c) * J c + 2 * f) with hK
  have hden : 0 < (1 - 2 * c) * J c + 2 * f := by positivity
  have htC := contact_lt hb hbc hc
  -- on `[1 − 2c, 1 − 2b]` the contact lies in `(0, c)`
  have hrange : ∀ z ∈ Icc (1 - 2 * c) (1 - 2 * b), 0 < radialContact z f ∧ radialContact z f ≤ radialContact (1 - 2 * c) f := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hc1 hz.1
    refine ⟨radialContact_pos hz0 hf, ?_⟩
    exact radialContact_anti_radius hc1 hz.1 hf
  have hg : ∀ z ∈ Icc (1 - 2 * c) (1 - 2 * b), HasDerivAt (fun r => radialContact r f + K * r)
      (-H (radialContact z f) / (z * J (radialContact z f) + 2 * f) + K) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hc1 hz.1
    exact (hasDerivAt_radialContact_radius hz0 hf).add
      ((hasDerivAt_id z).const_mul K |>.congr_deriv (by simp))
  have hmono : MonotoneOn (fun r => radialContact r f + K * r) (Icc (1 - 2 * c) (1 - 2 * b)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro z hz; exact (hg z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hg z ⟨hz.1.le, hz.2.le⟩).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz' : z ∈ Icc (1 - 2 * c) (1 - 2 * b) := ⟨hz.1.le, hz.2.le⟩
      rw [(hg z hz').deriv]
      obtain ⟨hr0, hr1⟩ := hrange z hz'
      have hrc : radialContact z f ≤ c := hr1.trans htC.le
      have hz0 : 0 < z := lt_of_lt_of_le hc1 hz'.1
      have hH : H (radialContact z f) ≤ H c := H_mono hr0.le hrc hc.le
      have hJ : J c ≤ J (radialContact z f) := J_anti hr0 hrc (by linarith)
      have hden' : (1 - 2 * c) * J c + 2 * f ≤ z * J (radialContact z f) + 2 * f := by
        have := mul_le_mul hz'.1 hJ hJc.le hz0.le
        linarith
      have hpos : 0 < z * J (radialContact z f) + 2 * f := lt_of_lt_of_le hden hden'
      have hH0 : 0 ≤ H (radialContact z f) := H_nonneg hr0.le (by linarith)
      have : H (radialContact z f) / (z * J (radialContact z f) + 2 * f) ≤ K := by
        rw [hK]
        exact div_le_div₀ (H_nonneg (hb.trans hbc).le (by linarith)) hH hden hden'
      rw [neg_div]
      linarith
  have hle : 1 - 2 * c ≤ 1 - 2 * b := by linarith
  have := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  simp only at this
  rw [cap_contact_H hb (by linarith)] at this
  nlinarith

end CKLaneM07.CE.R3

end


