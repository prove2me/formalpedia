-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWBase
-- name    : CK_CKLaneP_SeamWBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:04:35.26083+00:00
-- url     : https://prove2.me/theorems/b22ac4c6-de9a-4afa-a8b6-0a4712e3d740
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWBase.lean)

import Definitions.Def_CK_CKLaneP_SeamNCheck
import Definitions.Def_CK_CKLaneP_LogQ

-- ===== source module CKLaneP.SeamWBase =====
section
/-
Lane P — value-form ingredients for the away-from-diagonal (W) and vacuity (V) seam cells.

* `profile_ge_bracket0` : for `0 < v ≤ vb ≤ 1/1000` (no lower contact bracket):
      profile v ≥ (1 − 2vb)/((1 + vb/2)³ log 2).
* `seamDelta_le_log`   : Δ(y) ≤ (P/2)·log(f/e) + P·y/(1−S−y).
* `seam_master_Aval`   : value-form master inequality, case A.
* `gap_concave_min`    : `aβ − bβ² ≥ min(g(β1), g(β2))` on `[β1, β2]` (`b ≥ 0`).
* `kappa_ratio_mono`   : `(1+κh)²/(4κh) ≤ (1+κ)²/(4κ)` for `0 < κ ≤ κh ≤ 1`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

theorem profile_ge_bracket0 {v vb : ℝ} (hv0 : 0 < v) (hvb : v ≤ vb) (hvb1 : vb ≤ 1 / 1000)
    (hL4 : 4 ≤ -Real.log vb) :
    (1 - 2 * vb) / ((1 + vb / 2) ^ 3 * Real.log 2) ≤ profile v := by
  have hvb0 : 0 < vb := lt_of_lt_of_le hv0 hvb
  have hLv : -Real.log vb ≤ -Real.log v := by
    have := Real.log_le_log hv0 hvb; linarith
  have h := profile_ge_bracket (La := -Real.log v) hv0 le_rfl hvb hvb1 le_rfl hL4
  set L := -Real.log v with hLdef
  have hL4' : 4 ≤ L := le_trans hL4 hLv
  have hu0 : (0 : ℝ) ≤ 1 / L := by positivity
  have hu4 : 1 / L ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hL4'
  have hmono := psiLo_poly_mono (w := vb) hvb0.le (by linarith) (le_refl 0) hu0 hu4
  simp only [mul_zero, add_zero, one_pow, sub_zero, mul_one] at hmono
  have hr0 : 0 ≤ 1 - 2 * vb := by linarith
  have hdpos : 0 < (1 + vb / 2) ^ 3 * Real.log 2 := by
    have := log_two_pos; positivity
  calc (1 - 2 * vb) / ((1 + vb / 2) ^ 3 * Real.log 2)
      = (1 - 2 * vb) * 1 / ((1 + vb / 2) ^ 3 * Real.log 2) := by ring
    _ ≤ (1 - 2 * vb) * ((1 + (1 - vb) * (1 / L)) ^ 2 * (1 - 1 / L)) /
          ((1 + vb / 2) ^ 3 * Real.log 2) := by
        apply div_le_div_of_nonneg_right _ hdpos.le
        exact mul_le_mul_of_nonneg_left hmono hr0
    _ = (1 - 2 * vb) * (1 + (1 - vb) * (1 / L)) ^ 2 * (1 - 1 / L) /
          ((1 + vb / 2) ^ 3 * Real.log 2) := by ring
    _ ≤ profile v := h

/-- Upper bound of `Δ(y)` in the pure logarithmic form. -/
theorem seamDelta_le_log {S e f y P : ℝ} (he : 0 < e) (hef : e ≤ f) (hy : 0 ≤ y) (hS1 : S + y < 1)
    (hP0 : 0 ≤ P)
    (hP : ∀ t ∈ Icc ((1 - S - y) / (2 * f)) ((1 - S + y) / (2 * e)),
      profile (radialContact (2 * t) 1) ≤ P) :
    seamDelta S e f y ≤ P / 2 * Real.log (f / e) + P * (y / (1 - S - y)) := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  have hA : 0 < 1 - S - y := by linarith
  have hB : 0 < 1 - S + y := by linarith
  have hX : 0 < (1 - S - y) / (2 * f) := by positivity
  have hXY : (1 - S - y) / (2 * f) ≤ (1 - S + y) / (2 * e) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 - S - y) * (2 * e) ≤ (1 - S + y) * (2 * e) := by nlinarith
    have h2 : (1 - S + y) * (2 * e) ≤ (1 - S + y) * (2 * f) := by nlinarith
    linarith
  have hlog := theta_log_le hX hXY hP
  have hratio : (1 - S + y) / (2 * e) / ((1 - S - y) / (2 * f)) =
      (f / e) * ((1 - S + y) / (1 - S - y)) := by
    field_simp
  rw [hratio, Real.log_mul (by positivity) (by positivity)] at hlog
  have hy2 : Real.log ((1 - S + y) / (1 - S - y)) ≤ 2 * y / (1 - S - y) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 - S + y) / (1 - S - y) by positivity)
    have e : (1 - S + y) / (1 - S - y) - 1 = 2 * y / (1 - S - y) := by field_simp; ring
    linarith
  unfold seamDelta
  have hP2 := mul_le_mul_of_nonneg_left hy2 hP0
  have e3 : P * (2 * y / (1 - S - y)) = 2 * (P * (y / (1 - S - y))) := by ring
  linarith

/-- Value-form master inequality, case A. -/
theorem seam_master_Aval {S p q ys DC0 R0 B0 M Y : ℝ}
    (hS0 : 0 < S) (hS : S ≤ 1 / 10000) (hp : 0 < p) (hpq : p < q) (hqS : q ≤ S / 2)
    (hys0 : 0 < ys) (hysS : ys < S - 2 * p)
    (hstat : seamD S (H p) (H q) ys = 0)
    (hDC : DC0 ≤ canonicalPureGap p q (H p) (H q))
    (hR : R0 ≤ canonicalPureGap q q (H p) (H q) - canonicalPureGap p q (H p) (H q))
    (hB : B0 ≤ emLine (H p) (H q) (S / 2) - emLine (H p) (H q) q)
    (hM : ∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      M * ((ys - t) / (H p + H q)))
    (hM0 : 0 ≤ M) (hY : ys ≤ Y)
    (hcheck : 0 ≤ DC0 + R0 + B0 - M * Y ^ 2 / (2 * (H p + H q))) :
    0 ≤ seamCurve S (H p) (H q) ys := by
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q :=
    H_strictMonoOn.monotoneOn ⟨hp.le, by linarith⟩ ⟨(hp.trans hpq).le, by linarith⟩ hpq.le
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hdip := seam_dip_M (S := S) (y0 := 0) hS0.le hHp hHq le_rfl hys0 (by linarith) hstat hM
  rw [seamCurve_zero] at hdip
  have hem : emLine (H p) (H q) q = canonicalPureGap q q (H p) (H q) := rfl
  have hY2 : ys ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hys0.le hY 2
  have hdip2 : M * (ys - 0) ^ 2 / (2 * (H p + H q)) ≤ M * Y ^ 2 / (2 * (H p + H q)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hY2 hM0
  linarith

theorem gap_concave_min {a b β β1 β2 : ℝ} (hb : 0 ≤ b) (h1 : β1 ≤ β) (h2 : β ≤ β2) :
    min (a * β1 - b * β1 ^ 2) (a * β2 - b * β2 ^ 2) ≤ a * β - b * β ^ 2 := by
  by_cases hc : 0 ≤ a - b * (β + β1)
  · have : a * β1 - b * β1 ^ 2 ≤ a * β - b * β ^ 2 := by
      have e : a * β - b * β ^ 2 - (a * β1 - b * β1 ^ 2) = (β - β1) * (a - b * (β + β1)) := by ring
      nlinarith [mul_nonneg (sub_nonneg.2 h1) hc]
    exact le_trans (min_le_left _ _) this
  · push Not at hc
    have hc2 : a - b * (β + β2) < 0 := by nlinarith
    have : a * β2 - b * β2 ^ 2 ≤ a * β - b * β ^ 2 := by
      have e : a * β - b * β ^ 2 - (a * β2 - b * β2 ^ 2) = (β - β2) * (a - b * (β + β2)) := by ring
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (le_of_lt (neg_pos.2 hc2))]
    exact le_trans (min_le_right _ _) this

theorem kappa_ratio_mono {κ κh : ℝ} (hk : 0 < κ) (hkh : κ ≤ κh) (hkh1 : κh ≤ 1) :
    (1 + κh) ^ 2 / (4 * κh) ≤ (1 + κ) ^ 2 / (4 * κ) := by
  have hkh0 : 0 < κh := lt_of_lt_of_le hk hkh
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : (1 + κ) ^ 2 * (4 * κh) - (1 + κh) ^ 2 * (4 * κ) = 4 * ((κh - κ) * (1 - κ * κh)) := by ring
  have h1 : 0 ≤ κh - κ := by linarith
  have h2 : 0 ≤ 1 - κ * κh := by nlinarith
  nlinarith [mul_nonneg h1 h2]

end CKLaneP

end


