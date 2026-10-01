-- Prove2me | Definitions.Def_CK_CKLaneM06_CapBounds
-- name    : CK_CKLaneM06_CapBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:31:35.74864+00:00
-- url     : https://prove2.me/theorems/a0ba1223-95c1-4d18-80e5-5b94df2993f7
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapBounds.lean)

import Definitions.Def_CK_CKLaneM06_CapCore
import Definitions.Def_CK_CKLaneE_FastPoint

-- ===== source module CKLaneM06.CapBounds =====
section

/-!
# Lane M06: real-variable box bounds for the cap checker

Monotone substitutions turning the pointwise analytic bounds into box bounds:

* `K6_bound` : `Δ ≤ K6 (b-a)²` from `CKLaneE.entropyDrop_le_normalized6` with box constants
  `ρ ≤ ρh`, `κ ≤ κh`, `mL ≤ m ≤ mH`, `Lq ≤ log 2`.
* `W6_bound` : `4Δ + (b-a)² W ≤ j` from `interiorCost_sub_four_drop6` with `ρ ≥ ρl`, `κ ≥ κl`,
  `m ≤ mH`, `mL ≤ m`, `log 2 ≤ Lq`.
* `plane_box` : interval lower bounds for the normalized mean-contact-plane coefficients `A0, D0` from
  enclosures of the four logarithms `-log a, -log b, -log(1-a), -log(1-b)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK

/-- Box form of the quartic-exact normalized entropy-drop bound. -/
theorem K6_bound {a b ρh κh mL mH Lq : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hρ : (b - a) / (a + b) ≤ ρh) (hκ : (b - a) / (2 - a - b) ≤ κh)
    (hmL : 0 < mL) (hmL' : mL ≤ (a + b) / 2) (hmH : (a + b) / 2 ≤ mH) (hmH1 : mH < 1)
    (hLq : 0 < Lq) (hLq' : Lq ≤ Real.log 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤
      ((1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4) / mL + (1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4) / (1 - mH)) /
        (8 * Lq) * (b - a) ^ 2 := by
  have hnorm := CKLaneE.entropyDrop_le_normalized6 ha hab hb
  have hd0 : 0 < b - a := by linarith
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hρ0 : 0 ≤ (b - a) / (a + b) := div_nonneg hd0.le hs.le
  have hκ0 : 0 ≤ (b - a) / (2 - a - b) := div_nonneg hd0.le ht.le
  have hρ2 : ((b - a) / (a + b)) ^ 2 ≤ ρh ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
  have hρ4 : ((b - a) / (a + b)) ^ 4 ≤ ρh ^ 4 := pow_le_pow_left₀ hρ0 hρ 4
  have hκ2 : ((b - a) / (2 - a - b)) ^ 2 ≤ κh ^ 2 := pow_le_pow_left₀ hκ0 hκ 2
  have hκ4 : ((b - a) / (2 - a - b)) ^ 4 ≤ κh ^ 4 := pow_le_pow_left₀ hκ0 hκ 4
  have hm0 : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hnum1 : 0 ≤ 1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4 := by positivity
  have hnum2 : 0 ≤ 1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4 := by
    positivity
  have t1 : (1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) ≤
      (1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4) / mL :=
    div_le_div₀ (by positivity) (by linarith) hmL hmL'
  have t2 : (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
      (1 - (a + b) / 2) ≤ (1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4) / (1 - mH) :=
    div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
  have hsum := add_le_add t1 t2
  have hLL : (b - a) ^ 2 / (8 * Real.log 2) ≤ (b - a) ^ 2 / (8 * Lq) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hX : 0 ≤ (1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
      (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
        (1 - (a + b) / 2) := by positivity
  calc H ((a + b) / 2) - (H a + H b) / 2 ≤ _ := hnorm
    _ ≤ (b - a) ^ 2 / (8 * Lq) *
        ((1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
          (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
            (1 - (a + b) / 2)) :=
        mul_le_mul_of_nonneg_right hLL hX
    _ ≤ (b - a) ^ 2 / (8 * Lq) *
        ((1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4) / mL + (1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4) / (1 - mH)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Box form of the sextic mean-cost bonus. -/
theorem W6_bound {a b ρl κl mL mH Lq : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hρl : 0 ≤ ρl) (hρ : ρl ≤ (b - a) / (a + b)) (hκl : 0 ≤ κl) (hκ : κl ≤ (b - a) / (2 - a - b))
    (hmH : (a + b) / 2 ≤ mH) (hmL : mL ≤ (a + b) / 2) (hmL1 : mL < 1)
    (hLq : Real.log 2 ≤ Lq) :
    4 * (H ((a + b) / 2) - (H a + H b) / 2) +
        (b - a) ^ 2 * (((ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH + (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL)) /
          (12 * Lq)) ≤ interiorCost a b := by
  have hbonus := interiorCost_sub_four_drop6 ha hab hb
  have hL := log_two_pos
  have hs : 0 < a + b := by linarith
  have hm0 : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hρ2 : ρl ^ 2 ≤ ((b - a) / (a + b)) ^ 2 := pow_le_pow_left₀ hρl hρ 2
  have hρ4 : ρl ^ 4 ≤ ((b - a) / (a + b)) ^ 4 := pow_le_pow_left₀ hρl hρ 4
  have hκ2 : κl ^ 2 ≤ ((b - a) / (2 - a - b)) ^ 2 := pow_le_pow_left₀ hκl hκ 2
  have hκ4 : κl ^ 4 ≤ ((b - a) / (2 - a - b)) ^ 4 := pow_le_pow_left₀ hκl hκ 4
  have hmHpos : 0 < mH := by linarith
  have t1 : (ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH ≤
      (((b - a) / (a + b)) ^ 2 + 4 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) :=
    div_le_div₀ (by positivity) (by linarith) hm0 hmH
  have t2 : (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL) ≤
      (((b - a) / (2 - a - b)) ^ 2 + 4 / 5 * ((b - a) / (2 - a - b)) ^ 4) / (1 - (a + b) / 2) :=
    div_le_div₀ (by positivity) (by linarith) hm1 (by linarith)
  have hsum := add_le_add t1 t2
  have hY : 0 ≤ (ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH + (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL) := by
    have : 0 < 1 - mL := by linarith
    positivity
  have hLL : (b - a) ^ 2 / (12 * Lq) ≤ (b - a) ^ 2 / (12 * Real.log 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hd2 : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have step : (b - a) ^ 2 * (((ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH + (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL)) /
      (12 * Lq)) ≤ (b - a) ^ 2 / (12 * Real.log 2) *
        ((((b - a) / (a + b)) ^ 2 + 4 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
          (((b - a) / (2 - a - b)) ^ 2 + 4 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
            (1 - (a + b) / 2)) := by
    calc (b - a) ^ 2 * (((ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH + (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL)) /
          (12 * Lq))
        = (b - a) ^ 2 / (12 * Lq) *
            ((ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH + (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL)) := by ring
      _ ≤ (b - a) ^ 2 / (12 * Real.log 2) *
            ((ρl ^ 2 + 4 / 5 * ρl ^ 4) / mH + (κl ^ 2 + 4 / 5 * κl ^ 4) / (1 - mL)) :=
          mul_le_mul_of_nonneg_right hLL hY
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith

/-- Interval lower bounds for the normalized mean-contact-plane coefficients. -/
theorem plane_box {a b l11 h11 l12 h12 l21 h21 l22 h22 a0 a1 b0 b1 : ℝ}
    (ha0 : 0 < a0) (ha : a0 ≤ a) (ha' : a ≤ a1) (hb0 : 0 < b0) (hb : b0 ≤ b) (hb' : b ≤ b1)
    (ha1 : a1 < 1) (hb1 : b1 < 1)
    (m11l : l11 ≤ -Real.log a) (m11h : -Real.log a ≤ h11)
    (m12l : l12 ≤ -Real.log b) (m12h : -Real.log b ≤ h12)
    (m21l : l21 ≤ -Real.log (1 - a)) (m21h : -Real.log (1 - a) ≤ h21)
    (m22l : l22 ≤ -Real.log (1 - b)) (m22h : -Real.log (1 - b) ≤ h22)
    (p11 : 0 ≤ l11) (p12 : 0 ≤ l12) (p21 : 0 ≤ l21) (p22 : 0 ≤ l22)
    (hdetL : 0 < l11 * l22 - h12 * h21)
    (hnA : 0 < l22 / (2 * a1 * b1) - h12 / (2 * (1 - a1) * (1 - b1)))
    (hnD : 0 < l11 / (2 * (1 - a0) * (1 - b0)) - h21 / (2 * a0 * b0)) :
    0 < pDet a b ∧
      (l22 / (2 * a1 * b1) - h12 / (2 * (1 - a1) * (1 - b1))) / (h11 * h22 - l12 * l21) ≤ pA0 a b ∧
      (l11 / (2 * (1 - a0) * (1 - b0)) - h21 / (2 * a0 * b0)) / (h11 * h22 - l12 * l21) ≤ pD0 a b := by
  have hapos : 0 < a := lt_of_lt_of_le ha0 ha
  have hbpos : 0 < b := lt_of_lt_of_le hb0 hb
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have h1a1 : 0 < 1 - a1 := by linarith
  have h1b1 : 0 < 1 - b1 := by linarith
  have ha1pos : 0 < a1 := lt_of_lt_of_le hapos ha'
  have hb1pos : 0 < b1 := lt_of_lt_of_le hbpos hb'
  set m11 := -Real.log a
  set m12 := -Real.log b
  set m21 := -Real.log (1 - a)
  set m22 := -Real.log (1 - b)
  -- determinant bounds
  have hdet_lo : l11 * l22 - h12 * h21 ≤ m11 * m22 - m12 * m21 := by
    have e1 : l11 * l22 ≤ m11 * m22 := mul_le_mul m11l m22l p22 (p11.trans m11l)
    have e2 : m12 * m21 ≤ h12 * h21 := mul_le_mul m12h m21h (p21.trans m21l) ((p12.trans m12l).trans m12h)
    linarith
  have hdet_hi : m11 * m22 - m12 * m21 ≤ h11 * h22 - l12 * l21 := by
    have e1 : m11 * m22 ≤ h11 * h22 := mul_le_mul m11h m22h (p22.trans m22l) ((p11.trans m11l).trans m11h)
    have e2 : l12 * l21 ≤ m12 * m21 := mul_le_mul m12l m21l p21 (p12.trans m12l)
    linarith
  have hdet : 0 < pDet a b := by
    show 0 < m11 * m22 - m12 * m21
    linarith
  refine ⟨hdet, ?_, ?_⟩
  · -- numerator of A0
    have hn : l22 / (2 * a1 * b1) - h12 / (2 * (1 - a1) * (1 - b1)) ≤
        m22 / (2 * a * b) - m12 / (2 * (1 - a) * (1 - b)) := by
      have q1 : l22 / (2 * a1 * b1) ≤ m22 / (2 * a * b) := by
        apply div_le_div₀ (p22.trans m22l) m22l (by positivity)
        have : a * b ≤ a1 * b1 := mul_le_mul ha' hb' hbpos.le ha1pos.le
        linarith
      have q2 : m12 / (2 * (1 - a) * (1 - b)) ≤ h12 / (2 * (1 - a1) * (1 - b1)) := by
        apply div_le_div₀ ((p12.trans m12l).trans m12h) m12h (by positivity)
        have : (1 - a1) * (1 - b1) ≤ (1 - a) * (1 - b) :=
          mul_le_mul (by linarith) (by linarith) h1b1.le h1a.le
        linarith
      linarith
    have hpA : pA0 a b = (m22 / (2 * a * b) - m12 / (2 * (1 - a) * (1 - b))) / (m11 * m22 - m12 * m21) :=
      rfl
    rw [hpA]
    have hdpos : 0 < m11 * m22 - m12 * m21 := hdet
    calc (l22 / (2 * a1 * b1) - h12 / (2 * (1 - a1) * (1 - b1))) / (h11 * h22 - l12 * l21)
        ≤ (l22 / (2 * a1 * b1) - h12 / (2 * (1 - a1) * (1 - b1))) / (m11 * m22 - m12 * m21) :=
          div_le_div_of_nonneg_left hnA.le hdpos hdet_hi
      _ ≤ _ := div_le_div_of_nonneg_right hn hdpos.le
  · -- numerator of D0
    have hn : l11 / (2 * (1 - a0) * (1 - b0)) - h21 / (2 * a0 * b0) ≤
        m11 / (2 * (1 - a) * (1 - b)) - m21 / (2 * a * b) := by
      have q1 : l11 / (2 * (1 - a0) * (1 - b0)) ≤ m11 / (2 * (1 - a) * (1 - b)) := by
        apply div_le_div₀ (p11.trans m11l) m11l (by positivity)
        have : (1 - a) * (1 - b) ≤ (1 - a0) * (1 - b0) :=
          mul_le_mul (by linarith) (by linarith) h1b.le (by linarith)
        linarith
      have q2 : m21 / (2 * a * b) ≤ h21 / (2 * a0 * b0) := by
        apply div_le_div₀ ((p21.trans m21l).trans m21h) m21h (by positivity)
        have : a0 * b0 ≤ a * b := mul_le_mul ha hb hb0.le hapos.le
        linarith
      linarith
    have hpD : pD0 a b = (m11 / (2 * (1 - a) * (1 - b)) - m21 / (2 * a * b)) / (m11 * m22 - m12 * m21) :=
      rfl
    rw [hpD]
    have hdpos : 0 < m11 * m22 - m12 * m21 := hdet
    calc (l11 / (2 * (1 - a0) * (1 - b0)) - h21 / (2 * a0 * b0)) / (h11 * h22 - l12 * l21)
        ≤ (l11 / (2 * (1 - a0) * (1 - b0)) - h21 / (2 * a0 * b0)) / (m11 * m22 - m12 * m21) :=
          div_le_div_of_nonneg_left hnD.le hdpos hdet_hi
      _ ≤ _ := div_le_div_of_nonneg_right hn hdpos.le

end CKLaneM06.Cap

end


