-- Prove2me | Definitions.Def_CK_CKLaneP_SeamNCore
-- name    : CK_CKLaneP_SeamNCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:43:28.811075+00:00
-- url     : https://prove2.me/theorems/b34ae898-9348-414e-bcc3-e3d5088a6a92
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamNCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamNCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamNCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamNCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamNCore.lean)

import Definitions.Def_CK_CKLaneP_SeamMaster

-- ===== source module CKLaneP.SeamNCore =====
section
/-
Lane P — real-valued core of the normalized (N-mode) seam cell check.

`ncore_A`: for a stationary seam point with `q ≤ S/2`, real bounds on `H, J, radialSlope`,
profile brackets and a Θ-ratio point `x̄` imply `0 ≤ s(y*)` as soon as the normalized check
    0 ≤ DCn + c1n − c2/2 + Bn − M·Yn²/(2 E_lo)
holds, where (all normalized by β² = (q−p)²)
    DCn = max(0, 1/(p1 (2+ρ) log2⁺) − rs0/(4 log2⁻ p0(1−p0) Jq)),   ρ = βhi/p0
    c1n = Pmin·2 Jq/(3 eH + fH),   c2 = 12/E_lo,   Bn = max(0, S/2 − qd)·(9/40)·Jq²/fH²
    A0n = (Pmax/2)·Jp·E_hi/(2 eL fL),   λ = Pmax/(1 − 2S + 2p0),
    Yn  = A0n·E_hi/(θ̄/x̄ − λ E_hi),   M ≥ Θ' on (0, x̄].
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- Double cap lower bound in normalized form, cell-uniform. -/
theorem dc_cell_lower {p q p0 p1 βhi Jq rs0 l2hi l2lo : ℝ} (hp0 : 0 < p0) (hp0p : p0 ≤ p)
    (hpp1 : p ≤ p1) (hpq : p < q) (hq : q < 1 / 2) (hβ : q - p ≤ βhi)
    (hJq : Jq ≤ J q) (hJq0 : 0 < Jq) (hrs : radialSlope p ≤ rs0)
    (hl2hi : Real.log 2 ≤ l2hi) (hl2lo : l2lo ≤ Real.log 2) (hl2lo0 : 0 < l2lo) :
    (q - p) ^ 2 * (1 / (p1 * (2 + βhi / p0) * l2hi) -
        rs0 / (4 * l2lo * (p0 * (1 - p0)) * Jq)) ≤ canonicalPureGap p q (H p) (H q) := by
  have hp : 0 < p := lt_of_lt_of_le hp0 hp0p
  have hL := log_two_pos
  have hβ0 : 0 < q - p := by linarith
  have hdc := dc_lower_log hp hpq hq
  set β := q - p with hβd
  -- first term: β log(1+β/p)/(2 log2) ≥ β²/(p (2 + β/p) log 2) ≥ β²/(p1 (2 + βhi/p0) l2hi)
  have hlog := log_one_add_ge (u := β / p) (by positivity)
  have ht1 : β ^ 2 * (1 / (p1 * (2 + βhi / p0) * l2hi)) ≤
      β * (Real.log (1 + β / p) / Real.log 2) / 2 := by
    have h1 : 2 * (β / p) / (2 + β / p) / Real.log 2 ≤ Real.log (1 + β / p) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog hL.le
    have h2 : β ^ 2 * (1 / (p1 * (2 + βhi / p0) * l2hi)) ≤
        β * (2 * (β / p) / (2 + β / p) / Real.log 2) / 2 := by
      have e : β * (2 * (β / p) / (2 + β / p) / Real.log 2) / 2 =
          β ^ 2 * (1 / (p * (2 + β / p) * Real.log 2)) := by
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply one_div_le_one_div_of_le (by positivity)
      have hr : β / p ≤ βhi / p0 := by
        rw [div_le_div_iff₀ hp hp0]
        nlinarith
      have h3 : p * (2 + β / p) ≤ p1 * (2 + βhi / p0) :=
        mul_le_mul hpp1 (by linarith) (by positivity) (by linarith)
      have h4 : p * (2 + β / p) * Real.log 2 ≤ p1 * (2 + βhi / p0) * l2hi :=
        mul_le_mul h3 hl2hi hL.le (le_trans (by positivity) h3)
      exact h4
    have h5 := mul_le_mul_of_nonneg_left h1 hβ0.le
    linarith
  -- second term
  have ht2 : β ^ 2 * (radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J ((p + q) / 2))) ≤
      β ^ 2 * (rs0 / (4 * l2lo * (p0 * (1 - p0)) * Jq)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hm : (p + q) / 2 ≤ q := by linarith
    have hJm : Jq ≤ J ((p + q) / 2) := le_trans hJq (J_antitone (by linarith) hq.le hm)
    have hpp : p0 * (1 - p0) ≤ p * (1 - p) := by nlinarith
    have hrs0 : 0 ≤ radialSlope p := by
      have hxw : (0 : ℝ) < (1 - 2 * p) / (2 * H p) := div_pos (by linarith)
        (mul_pos two_pos (H_pos hp (by linarith)))
      have := e8Theta_pos hxw
      rw [theta_eq_radialSlope hxw] at this
      have hHp0 : H p ≠ 0 := (H_pos hp (by linarith)).ne'
      have hrc : radialContact (2 * ((1 - 2 * p) / (2 * H p))) 1 = p := by
        apply radialContact_eq_of_equation (mul_pos two_pos hxw) one_pos hp (by linarith)
        field_simp
      rw [hrc] at this
      exact this.le
    have hden : 4 * l2lo * (p0 * (1 - p0)) * Jq ≤ 4 * (Real.log 2 * (p * (1 - p))) * J ((p + q) / 2) := by
      have h1 : l2lo * (p0 * (1 - p0)) ≤ Real.log 2 * (p * (1 - p)) :=
        mul_le_mul hl2lo hpp (by nlinarith) hL.le
      have h2 := mul_le_mul h1 hJm hJq0.le (mul_nonneg hL.le (mul_nonneg hp.le (by linarith)))
      nlinarith
    have hden0 : 0 < 4 * l2lo * (p0 * (1 - p0)) * Jq := by
      have : 0 < p0 * (1 - p0) := mul_pos hp0 (by linarith)
      positivity
    calc radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J ((p + q) / 2))
        ≤ radialSlope p / (4 * l2lo * (p0 * (1 - p0)) * Jq) :=
          div_le_div_of_nonneg_left hrs0 hden0 hden
      _ ≤ rs0 / (4 * l2lo * (p0 * (1 - p0)) * Jq) :=
          div_le_div_of_nonneg_right hrs hden0.le
  have e : β ^ 2 * (1 / (p1 * (2 + βhi / p0) * l2hi) - rs0 / (4 * l2lo * (p0 * (1 - p0)) * Jq)) =
      β ^ 2 * (1 / (p1 * (2 + βhi / p0) * l2hi)) - β ^ 2 * (rs0 / (4 * l2lo * (p0 * (1 - p0)) * Jq)) := by
    ring
  rw [e]
  linarith

/-- Right-fiber derivative lower bound in the normalized affine form. -/
theorem rightD_cell_lower {p q t Pmin eH fH Jq EL : ℝ} (hp : 0 < p) (hpt : p ≤ t) (htq : t < q)
    (hq : q ≤ 1 / 10000) (hPmin0 : 0 ≤ Pmin)
    (hP : ∀ x ∈ Icc ((1 - t - q) / (H p + H q)) ((1 - 2 * t) / (2 * H p)),
      Pmin ≤ profile (radialContact (2 * x) 1))
    (heH : H p ≤ eH) (hfH : H q ≤ fH) (hJq : Jq ≤ J q) (hJq0 : 0 ≤ Jq)
    (hEL : EL ≤ H p + H q) (hEL0 : 0 < EL) :
    Pmin * (2 * Jq / (3 * eH + fH)) * (q - p) - 12 / EL * (q - t) ≤ rightD q (H p) (H q) t := by
  have hq0 : 0 < q := lt_of_lt_of_le hp (hpt.trans htq.le)
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hpq : p ≤ q := hpt.trans htq.le
  have hHpq : H p ≤ H q := H_strictMonoOn.monotoneOn ⟨hp.le, by linarith⟩ ⟨hq0.le, by linarith⟩ hpq
  have hE : 0 < H p + H q := by linarith
  have h1 := rightD_ge hp hpt htq hq hPmin0 hP
  -- log(E/(2e)) ≥ 2(f−e)/(3e+f) ≥ 2 Jq (q−p)/(3 eH + fH)
  have hlog : 2 * Jq / (3 * eH + fH) * (q - p) ≤ Real.log ((H p + H q) / (2 * H p)) := by
    have hu : 0 ≤ (H q - H p) / (2 * H p) := div_nonneg (by linarith) (by linarith)
    have h2 := log_one_add_ge hu
    have e1 : 1 + (H q - H p) / (2 * H p) = (H p + H q) / (2 * H p) := by field_simp; ring
    rw [e1] at h2
    have e2 : 2 * ((H q - H p) / (2 * H p)) / (2 + (H q - H p) / (2 * H p)) =
        2 * (H q - H p) / (3 * H p + H q) := by field_simp; ring
    rw [e2] at h2
    have hfe : Jq * (q - p) ≤ H q - H p := by
      have := J_mul_le_H_sub hp.le hpq (by linarith)
      nlinarith
    have hden : 3 * H p + H q ≤ 3 * eH + fH := by linarith
    have hden0 : 0 < 3 * H p + H q := by linarith
    have h3 : 2 * Jq / (3 * eH + fH) * (q - p) ≤ 2 * (H q - H p) / (3 * H p + H q) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) hden0]
      have h4 : 0 ≤ Jq * (q - p) := mul_nonneg hJq0 (by linarith)
      nlinarith
    linarith
  have h12 : 12 * ((q - t) / (H p + H q)) ≤ 12 / EL * (q - t) := by
    rw [mul_div_assoc', div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left (by nlinarith) hEL0 hEL
  have := mul_le_mul_of_nonneg_left hlog hPmin0
  nlinarith

end CKLaneP

end


