-- Prove2me | Definitions.Def_CK_CKLaneP_RightFiber
-- name    : CK_CKLaneP_RightFiber
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:16:50.310868+00:00
-- url     : https://prove2.me/theorems/e81fa74a-d557-4759-9525-d5b0b7002234
-- title:
--   Courtade–Kumar proof module `CKLaneP.RightFiber` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.RightFiber` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.RightFiber` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.RightFiber (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/RightFiber.lean)

import Definitions.Def_CK_CKLaneP_ThetaBounds
import Definitions.Def_CK_GeneralCK_PureGapMeanStationarity
import Definitions.Def_CK_GeneralCK_PureGapCompactMean

-- ===== source module CKLaneP.RightFiber =====
section
/-
Lane P — the right cap fiber is increasing at tiny scales.

For `0 < a ≤ x < b ≤ 1/10000`, with `e = H a`, `f = H b`, the fiber derivative
    R'(x) = −Θ((b−x)/(e+f)) − Θ((1−x−b)/(e+f)) + Θ((1−2x)/(2e))
is nonnegative (`rightFiber_deriv_nonneg`).  Proof: with U=(b−x)/E, V=(1−x−b)/E, W=(1−2x)/(2e),
E=e+f, one has W = λ(U+V), λ = E/(2e) ≥ 1, so
    R' = [Θ(W) − Θ(V)] − Θ(U) ≥ log₂ λ − 12 U                (theta_log_increment, theta_le_twelve)
and log λ ≥ (r−1)/(r+1) (r = f/e) while 12U ≤ (12/J b)(r−1)/(r+1) (concavity of H);
J b ≥ 13 > 12 log 2 closes it.  Consequently (`rightFiber_mono`)
    cPG(a, b, H a, H b) ≤ cPG(x0, b, H a, H b)   for a ≤ x0 ≤ b ≤ 1/10000.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set

/-- The right-fiber derivative in `e8Theta` form. -/
theorem hasDerivAt_rightFiber {x b e f : ℝ} (hxb : x < b) (hsum : x + b < 1) (hx : x < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    HasDerivAt (fun t => canonicalPureGap t b e f)
      (-e8Theta ((b - x) / (e + f)) - e8Theta ((1 - x - b) / (e + f)) +
        e8Theta ((1 - 2 * x) / (2 * e))) x := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hFd := (hasDerivAt_F_radius (sub_pos.mpr hxb) hef).differentiableAt.hasDerivAt
  have hFc := (hasDerivAt_F_radius (show 0 < 1 - x - b by linarith) hef).differentiableAt.hasDerivAt
  have hFl := (hasDerivAt_F_radius (show 0 < 1 - 2 * x by linarith) he).differentiableAt.hasDerivAt
  have hdiff := hFd.comp x ((hasDerivAt_id x).const_sub b)
  have hcenter := hFc.comp x (((hasDerivAt_id x).const_sub 1).sub_const b)
  have hleft := hFl.comp x (((hasDerivAt_id x).const_mul 2).const_sub 1)
  have hright := hasDerivAt_const x (radialPhi (1 - 2 * b) f)
  have _htotal :=
    ((hdiff.add (hasDerivAt_const x (entropyCorrection e f))).sub
      ((hasDerivAt_const x (eta ((e + f) / 2))).sub hcenter)).add
      (((((hasDerivAt_const x (eta e)).sub hleft).add hright).div_const 2))
  have hd1 := deriv_F_radius_eq_e8Theta (sub_pos.mpr hxb) hef
  have hd2 := deriv_F_radius_eq_e8Theta (show 0 < 1 - x - b by linarith) hef
  have hd3 := deriv_F_radius_eq_e8Theta (show 0 < 1 - 2 * x by linarith) he
  have e1 : (b - x) / (2 * ((e + f) / 2)) = (b - x) / (e + f) := by ring_nf
  have e2 : (1 - x - b) / (2 * ((e + f) / 2)) = (1 - x - b) / (e + f) := by ring_nf
  rw [e1] at hd1
  rw [e2] at hd2
  have hdiff' : HasDerivAt (fun t => F (b - t) ((e + f) / 2))
      (deriv (fun r => F r ((e + f) / 2)) (b - x) * -1) x := hdiff
  have hcenter' : HasDerivAt (fun t => F (1 - t - b) ((e + f) / 2))
      (deriv (fun r => F r ((e + f) / 2)) (1 - x - b) * -1) x := hcenter
  have hleft' : HasDerivAt (fun t => F (1 - 2 * t) e)
      (deriv (fun r => F r e) (1 - 2 * x) * -(2 * 1)) x := hleft
  have hsum :=
    ((hdiff'.add (hasDerivAt_const x (entropyCorrection e f))).sub
      ((hasDerivAt_const x (eta ((e + f) / 2))).sub hcenter')).add
      (((((hasDerivAt_const x (eta e)).sub hleft').add hright).div_const 2))
  have hev : (fun t => canonicalPureGap t b e f) =ᶠ[nhds x]
      (fun t => F (b - t) ((e + f) / 2) + entropyCorrection e f -
        (eta ((e + f) / 2) - F (1 - t - b) ((e + f) / 2)) +
        ((eta e - F (1 - 2 * t) e) + radialPhi (1 - 2 * b) f) / 2) :=
    Filter.Eventually.of_forall (fun t => by
      simp only [canonicalPureGap, radialPhi]
      try ring_nf)
  refine (hsum.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hd1, hd2, hd3]
  ring

/-- Certified: `J (1/10000) ≥ 13`. -/
theorem J_ten_thousandth_ge : (13 : ℝ) ≤ J (1 / 10000) := by
  unfold J
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : (1 - (1 / 10000 : ℝ)) / (1 / 10000) = 9999 := by norm_num
  rw [e, le_div_iff₀ hl2]
  have h : Real.log ((2 : ℝ) ^ 13) ≤ Real.log 9999 := Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- Certified: `H (1/10000) ≤ 1618/1000000`. -/
theorem H_ten_thousandth_le : H (1 / 10000) ≤ 1618 / 1000000 := by
  have hl2 := log_two_gt
  have hlog2 : 0 < Real.log 2 := by linarith
  have hlog10k : Real.log (10000 : ℝ) ≤ 92104 / 10000 := by
    have h := logChk_sound (q := 10000) (k := 13) (n := 12) (lo := 9) (hi := 92104 / 10000)
      (by decide +kernel)
    have e : ((10000 : ℚ) : ℝ) = (10000 : ℝ) := by norm_num
    rw [e] at h
    have h2 := h.2
    push_cast at h2
    linarith
  obtain ⟨_, hm⟩ := neg_log_one_sub_bounds (v := 1 / 10000) (by norm_num) (by norm_num)
  have hhn : Certificates.Mixed.hn (1 / 10000) =
      (1 / 10000) * Real.log 10000 + (1 - 1 / 10000) * (-Real.log (1 - 1 / 10000)) := by
    unfold Certificates.Mixed.hn
    rw [show Real.log (1 / 10000 : ℝ) = -Real.log 10000 by
      rw [one_div, Real.log_inv]]
    ring
  have hhn_le : Certificates.Mixed.hn (1 / 10000) ≤ (1 / 10000) * (92104 / 10000) +
      (1 - 1 / 10000) * (2 * (1 / 10000)) := by
    rw [hhn]; nlinarith
  have hH := (Certificates.Mixed.hn_eq_H_mul_log (1 / 10000 : ℝ))
  by_contra hcon
  push Not at hcon
  have : (1618 / 1000000 : ℝ) * (6931 / 10000) < H (1 / 10000) * Real.log 2 := by
    have h1 : (1618 / 1000000 : ℝ) * (6931 / 10000) < (1618 / 1000000) * Real.log 2 := by nlinarith
    have h2 : (1618 / 1000000 : ℝ) * Real.log 2 ≤ H (1 / 10000) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcon.le hlog2.le
    linarith
  rw [← hH] at this
  norm_num at hhn_le this
  linarith

/-- The core inequality: the right fiber derivative is nonnegative at tiny scales. -/
theorem rightFiber_deriv_nonneg {a x b : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x < b)
    (hb : b ≤ 1 / 10000) :
    0 ≤ -e8Theta ((b - x) / (H a + H b)) - e8Theta ((1 - x - b) / (H a + H b)) +
        e8Theta ((1 - 2 * x) / (2 * H a)) := by
  have hab : a < b := lt_of_le_of_lt hax hxb
  have hb0 : 0 < b := ha.trans hab
  have hb12 : b ≤ 1 / 2 := by linarith
  have ha12 : a ≤ 1 / 2 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2hi := log_two_lt
  set e := H a with hedef
  set f := H b with hfdef
  have he : 0 < e := H_pos ha (by linarith)
  have hf : 0 < f := H_pos hb0 (by linarith)
  have hef : e < f := H_strictMonoOn ⟨ha.le, ha12⟩ ⟨hb0.le, hb12⟩ hab
  set E := e + f with hEdef
  have hE : 0 < E := by positivity
  -- J b ≥ 13
  have hJb : 13 ≤ J b := le_trans J_ten_thousandth_ge (J_antitone hb0 (by norm_num) hb)
  -- f small
  have hfs : f ≤ 1618 / 1000000 := le_trans
    (H_strictMonoOn.monotoneOn ⟨hb0.le, hb12⟩ ⟨by norm_num, by norm_num⟩ hb)
    H_ten_thousandth_le
  -- H b ≥ J b * b
  have hHb : J b * b ≤ f := by
    have h := J_mul_le_H_sub (a := 0) (b := b) le_rfl hb0.le hb12
    simp only [H_zero, sub_zero] at h
    exact h
  -- concavity increment
  have hHab : J b * (b - a) ≤ f - e := J_mul_le_H_sub ha.le hab.le hb12
  -- U, V, W
  set U := (b - x) / E with hUdef
  set V := (1 - x - b) / E with hVdef
  set W := (1 - 2 * x) / (2 * e) with hWdef
  have hU0 : 0 < U := div_pos (by linarith) hE
  have hJbpos : 0 < J b := by linarith
  have hU1 : U ≤ 2 / 25 := by
    have h1 : U ≤ b / f := by
      rw [hUdef, div_le_div_iff₀ hE hf]
      have : b - x ≤ b := by linarith
      nlinarith
    have h2 : b / f ≤ 1 / J b := by
      rw [div_le_div_iff₀ hf hJbpos]; linarith
    have h3 : 1 / J b ≤ 1 / 13 := by
      rw [div_le_div_iff₀ hJbpos (by norm_num)]; linarith
    linarith
  have hV300 : 300 ≤ V := by
    rw [hVdef, le_div_iff₀ hE]
    have hE2 : E ≤ 2 * f := by linarith
    have : 300 * E ≤ 300 * (2 * f) := by linarith
    nlinarith
  have hlam : 1 ≤ E / (2 * e) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hWeq : W = E / (2 * e) * (U + V) := by
    rw [hWdef, hUdef, hVdef]
    field_simp
    ring
  have hVW : V ≤ W := by
    rw [hWeq]
    have : V ≤ U + V := by linarith
    nlinarith
  have hinc := theta_log_increment hV300 hVW
  have hV0 : 0 < V := by linarith
  have hratio : E / (2 * e) ≤ W / V := by
    rw [hWeq, le_div_iff₀ hV0]
    nlinarith
  have hloglam : Real.log (E / (2 * e)) ≤ Real.log (W / V) :=
    Real.log_le_log (by positivity) hratio
  have hThU : e8Theta U ≤ 12 * U := theta_le_twelve hU0 hU1
  -- the ratio r = f/e
  set r := f / e with hrdef
  have hr1 : 1 ≤ r := by rw [hrdef, le_div_iff₀ he]; linarith
  have hlamr : E / (2 * e) = (1 + r) / 2 := by
    rw [hrdef, hEdef]; field_simp; try ring
  have hlogr := log_half_one_add_ge hr1
  have hfrac : (f - e) / E = (r - 1) / (r + 1) := by
    rw [hrdef, hEdef]; field_simp; try ring
  -- 12 U ≤ (12 / J b) (r - 1)/(r + 1)
  have h12U : 12 * U ≤ 12 / J b * ((r - 1) / (r + 1)) := by
    rw [← hfrac]
    have hUle : U ≤ (b - a) / E := by
      rw [hUdef]; exact div_le_div_of_nonneg_right (by linarith) hE.le
    have hba : b - a ≤ (f - e) / J b := by rw [le_div_iff₀ hJbpos]; linarith
    have : (b - a) / E ≤ (f - e) / J b / E := div_le_div_of_nonneg_right hba hE.le
    have e3 : (f - e) / J b / E = 1 / J b * ((f - e) / E) := by field_simp
    calc 12 * U ≤ 12 * ((f - e) / J b / E) := by linarith
      _ = 12 / J b * ((f - e) / E) := by rw [e3]; ring
  -- combine
  have hq0 : 0 ≤ (r - 1) / (r + 1) := div_nonneg (by linarith) (by linarith)
  have hcoef : 12 / J b ≤ 1 / Real.log 2 := by
    rw [div_le_div_iff₀ hJbpos hlog2]; nlinarith
  have hmain : 12 * U ≤ Real.log (W / V) / Real.log 2 := by
    have h1 : 12 / J b * ((r - 1) / (r + 1)) ≤ 1 / Real.log 2 * ((r - 1) / (r + 1)) :=
      mul_le_mul_of_nonneg_right hcoef hq0
    have h2 : 1 / Real.log 2 * ((r - 1) / (r + 1)) ≤ Real.log (W / V) / Real.log 2 := by
      rw [one_div_mul_eq_div]
      apply div_le_div_of_nonneg_right _ hlog2.le
      rw [hlamr] at hloglam
      linarith
    linarith
  linarith

/-- Continuity of the right fiber on the physical interval. -/
theorem continuousOn_rightFiber {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    ContinuousOn (fun t => canonicalPureGap t b (H a) (H b)) (Icc a b) := by
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hHb : 0 < H b := lt_of_lt_of_le hHa
    (H_strictMonoOn.monotoneOn ⟨ha.le, by linarith⟩ ⟨hb0, hb⟩ hab)
  have hc := continuousOn_canonicalPureGap hHa hHb
  have hmap : ContinuousOn (fun t : ℝ => ((t, b) : ℝ × ℝ)) (Icc a b) :=
    (continuous_id.prodMk continuous_const).continuousOn
  refine hc.comp hmap ?_
  intro t ht
  refine ⟨ha.le.trans ht.1, ht.2, hb, ?_, le_rfl⟩
  exact H_strictMonoOn.monotoneOn ⟨ha.le, by linarith⟩ ⟨ha.le.trans ht.1, by linarith [ht.2]⟩ ht.1

/-- Monotonicity of the right fiber at tiny scales. -/
theorem rightFiber_mono {a x0 b : ℝ} (ha : 0 < a) (hax0 : a ≤ x0) (hx0b : x0 ≤ b)
    (hb : b ≤ 1 / 10000) :
    canonicalPureGap a b (H a) (H b) ≤ canonicalPureGap x0 b (H a) (H b) := by
  have hb12 : b ≤ 1 / 2 := by linarith
  have hcont : ContinuousOn (fun t => canonicalPureGap t b (H a) (H b)) (Icc a x0) :=
    (continuousOn_rightFiber ha (hax0.trans hx0b) hb12).mono (Icc_subset_Icc le_rfl hx0b)
  have hmono : MonotoneOn (fun t => canonicalPureGap t b (H a) (H b)) (Icc a x0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a x0) hcont
    · rw [interior_Icc]
      intro t ht
      have htb : t < b := lt_of_lt_of_le ht.2 hx0b
      have he : 0 < H a := H_pos ha (by linarith)
      have hf : 0 < H b := H_pos (ha.trans (lt_of_le_of_lt ht.1.le htb)) (by linarith)
      exact (hasDerivAt_rightFiber htb (by linarith) (by linarith) he hf).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have htb : t < b := lt_of_lt_of_le ht.2 hx0b
      have he : 0 < H a := H_pos ha (by linarith)
      have hf : 0 < H b := H_pos (ha.trans (lt_of_le_of_lt ht.1.le htb)) (by linarith)
      rw [(hasDerivAt_rightFiber htb (by linarith) (by linarith) he hf).deriv]
      exact rightFiber_deriv_nonneg ha ht.1.le htb hb
  exact hmono ⟨le_rfl, hax0⟩ ⟨hax0, le_rfl⟩ hax0

end CKLaneP

end


