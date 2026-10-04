-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeSound_part03
-- name    : CK_CKLaneN1_EdgeSound_part03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:20:23.919985+00:00
-- url     : https://prove2.me/theorems/4f7f94b5-0a9c-41af-a1a3-e526de0ed0d8
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeSound (part 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeSound (part 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeSound (part 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeSound (part 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeSound (part 4 of 5).lean)

import Definitions.Def_CK_CKLaneN1_EdgeSound_part02

set_option autoImplicit false
namespace CKLaneN1.Edge
open GeneralCK CKLaneE.FP CKLaneN1.Capital Set
section Terms
variable {a b y z : ℝ}
theorem T4_alg_direct {cb y z Θd c4 Lh y0 : ℝ} (hcb : cb = y * (1 - z)) (hz1 : z ≤ 1)
    (hy0 : 0 < y0) (hyy0 : y0 ≤ y) (hLh : 0 ≤ Lh)
    (hΘ : Θd ≤ 81 / 50 * (y * c4 + Lh)) :
    cb * Θd ≤ y ^ 2 * (81 / 50 * (c4 + Lh / y0) + -(81 / 50 * (c4 + Lh / y0)) * z) := by
  have hy : 0 < y := lt_of_lt_of_le hy0 hyy0
  have hcb0 : 0 ≤ cb := by rw [hcb]; exact mul_nonneg hy.le (by linarith)
  have h := mul_le_mul_of_nonneg_left hΘ hcb0
  have hL : y * Lh ≤ y ^ 2 * (Lh / y0) := by
    rw [show y ^ 2 * (Lh / y0) = y * Lh * (y / y0) by field_simp]
    have : 1 ≤ y / y0 := by rw [le_div_iff₀ hy0]; linarith
    nlinarith [mul_nonneg hy.le hLh]
  have e1 : cb * (81 / 50 * (y * c4 + Lh)) = 81 / 50 * (1 - z) * (y ^ 2 * c4 + y * Lh) := by
    rw [hcb]; ring
  have e2 : y ^ 2 * (81 / 50 * (c4 + Lh / y0) + -(81 / 50 * (c4 + Lh / y0)) * z) =
      81 / 50 * (1 - z) * (y ^ 2 * c4 + y ^ 2 * (Lh / y0)) := by ring
  have h3 : 81 / 50 * (1 - z) * (y ^ 2 * c4 + y * Lh) ≤
      81 / 50 * (1 - z) * (y ^ 2 * c4 + y ^ 2 * (Lh / y0)) := by
    apply mul_le_mul_of_nonneg_left _ (by nlinarith)
    linarith
  linarith

/-- Outer tangent term. -/
theorem T4_sound {B : B3} {w : EWit} (hV : eVarOK B w = true) (hab : a < b)
    (hy : 0 < y) (hd : b - a = z * y) (hz1 : z ≤ 1)
    {c q e f : ℝ} (hcb : c - b = y * (1 - z)) (hcq : c - q ≤ y) (hc1 : c ≤ ((ec1 B : ℚ) : ℝ))
    (hc1' : 0 < 1 - 2 * ((ec1 B : ℚ) : ℝ))
    (hq2 : q ≤ c) (he0 : ((ee0 B : ℚ) : ℝ) ≤ e) (he0' : 0 ≤ ((ee0 B : ℚ) : ℝ))
    (hef : e ≤ f) (hf1 : f ≤ ((ef1 B : ℚ) : ℝ)) {h : ℝ} (hh : h = (e + f) / 2)
    (hh0 : ((eh0 B : ℚ) : ℝ) ≤ h) (hh0p : 0 < ((eh0 B : ℚ) : ℝ))
    (hfe : f - e ≤ J a * (b - a)) (hJa : ∀ _ : 0 < ((ea0 B : ℚ) : ℝ), ptOk (ea0 B) = true →
      J a ≤ ((lamHi (ea0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ)) (hJa0 : 0 ≤ J a)
    (hy0 : ((ey0 B : ℚ) : ℝ) ≤ y)
    {Θq Θc : ℝ}
    (hΘ : Θq - Θc ≤ 81 / 50 * Real.log (((1 - 2 * q) / (2 * h)) / ((1 - 2 * c) / (2 * f)))) :
    (c - b) * (Θq - Θc) ≤
      y ^ 2 * (((eT4 B w).1 : ℝ) + ((eT4 B w).2.1 : ℝ) * z + ((eT4 B w).2.2 : ℝ) * z ^ 2) := by
  subst hh
  have hf0 : 0 < f := by linarith
  have hef0 : 0 < e + f := by linarith
  have hhpos : 0 < (e + f) / 2 := by linarith
  have h1c : 0 < 1 - 2 * c := by linarith
  have h1q : 0 < 1 - 2 * q := by linarith
  have hlog : Real.log (((1 - 2 * q) / (2 * ((e + f) / 2))) / ((1 - 2 * c) / (2 * f))) =
      Real.log ((1 - 2 * q) / (1 - 2 * c)) + Real.log (f / ((e + f) / 2)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hlog] at hΘ
  have hl1 : Real.log ((1 - 2 * q) / (1 - 2 * c)) ≤ y * (2 / (1 - 2 * ((ec1 B : ℚ) : ℝ))) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (1 - 2 * q) / (1 - 2 * c) by positivity)
    have e1 : (1 - 2 * q) / (1 - 2 * c) - 1 = 2 * (c - q) / (1 - 2 * c) := by
      field_simp; ring
    rw [e1] at this
    have h2 : 2 * (c - q) / (1 - 2 * c) ≤ 2 * y / (1 - 2 * ((ec1 B : ℚ) : ℝ)) := by
      rw [div_le_div_iff₀ h1c hc1']
      nlinarith
    have e2 : 2 * y / (1 - 2 * ((ec1 B : ℚ) : ℝ)) = y * (2 / (1 - 2 * ((ec1 B : ℚ) : ℝ))) := by
      ring
    linarith
  have hcb0 : 0 ≤ c - b := by rw [hcb]; exact mul_nonneg hy.le (by linarith)
  have hc4 : ((ec4 B : ℚ) : ℝ) = 2 / (1 - 2 * ((ec1 B : ℚ) : ℝ)) := by
    simp only [ec4]; push_cast; ring
  have hK : ((Kq : ℚ) : ℝ) = 81 / 50 := by norm_num [Kq]
  cases hk : w.k4
  · simp only [eT4, hk, Bool.false_eq_true, if_false]
    simp only [eVarOK, hk, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq]
      at hV
    obtain ⟨-, ⟨ha0p, hpa0⟩⟩ := hV
    have ha0R : (0 : ℝ) < ((ea0 B : ℚ) : ℝ) := by exact_mod_cast ha0p
    have hJ := hJa ha0R hpa0
    have hl2 : Real.log (f / ((e + f) / 2)) ≤ z * y * ((eg B : ℚ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show 0 < f / ((e + f) / 2) by positivity)
      have e1 : f / ((e + f) / 2) - 1 = (f - e) / (2 * ((e + f) / 2)) := by
        field_simp; ring
      rw [e1] at this
      have hnum : 0 ≤ J a * (b - a) := mul_nonneg hJa0 (by linarith)
      have h3 : (f - e) / (2 * ((e + f) / 2)) ≤ J a * (b - a) / (2 * ((eh0 B : ℚ) : ℝ)) :=
        calc (f - e) / (2 * ((e + f) / 2)) ≤ J a * (b - a) / (2 * ((e + f) / 2)) :=
              div_le_div_of_nonneg_right hfe (by linarith)
          _ ≤ J a * (b - a) / (2 * ((eh0 B : ℚ) : ℝ)) :=
              div_le_div_of_nonneg_left hnum (by linarith) (by linarith)
      have h4 : J a * (b - a) / (2 * ((eh0 B : ℚ) : ℝ)) ≤ z * y * ((eg B : ℚ) : ℝ) := by
        have hg : ((eg B : ℚ) : ℝ) = ((lamHi (ea0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) /
            (2 * ((eh0 B : ℚ) : ℝ)) := by
          simp only [eg]; push_cast; ring
        rw [hd, hg]
        have hzy : 0 ≤ z * y := by rw [← hd]; linarith
        rw [show J a * (z * y) / (2 * ((eh0 B : ℚ) : ℝ)) =
          z * y * (J a / (2 * ((eh0 B : ℚ) : ℝ))) by ring]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hJ (by linarith)) hzy
      linarith
    have htot : Θq - Θc ≤ 81 / 50 * (y * ((ec4 B : ℚ) : ℝ) + z * y * ((eg B : ℚ) : ℝ)) := by
      rw [hc4]; linarith
    have := T4_alg_norm hcb hcb0 htot
    push_cast
    rw [hK]
    linarith
  · simp only [eT4, hk, if_true]
    simp only [eVarOK, hk, if_true, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨-, ⟨hy0p, hpq4⟩⟩ := hV
    have hy0R : (0 : ℝ) < ((ey0 B : ℚ) : ℝ) := by exact_mod_cast hy0p
    have hq4 := ptOk_pos hpq4
    have hs := (ptOk_sound hpq4).2.2.1
    have hf1p : 0 < ((ef1 B : ℚ) : ℝ) := by linarith
    have hq4e : ((eq4 B : ℚ) : ℝ) = (((ef1 B : ℚ) : ℝ) - ((ee0 B : ℚ) : ℝ)) /
        (2 * ((ef1 B : ℚ) : ℝ)) := by
      simp only [eq4]; push_cast; ring
    have hone : 1 - ((eq4 B : ℚ) : ℝ) = (((ee0 B : ℚ) : ℝ) + ((ef1 B : ℚ) : ℝ)) /
        (2 * ((ef1 B : ℚ) : ℝ)) := by
      rw [hq4e]; field_simp; ring
    have hratio : f / ((e + f) / 2) ≤ (1 - ((eq4 B : ℚ) : ℝ))⁻¹ := by
      rw [hone, inv_div, div_le_div_iff₀ hhpos (by linarith)]
      nlinarith
    have hl2 : Real.log (f / ((e + f) / 2)) ≤ ((eLhi B : ℚ) : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hratio
      rw [Real.log_inv] at h1
      simp only [eLhi]
      push_cast
      linarith
    have hLhi0 : 0 ≤ ((eLhi B : ℚ) : ℝ) := by
      have hq40 : (0 : ℝ) < ((eq4 B : ℚ) : ℝ) := by exact_mod_cast hq4.1
      have hq41 : ((eq4 B : ℚ) : ℝ) < 1 := by exact_mod_cast hq4.2
      have : Real.log (1 - ((eq4 B : ℚ) : ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      simp only [eLhi]
      push_cast
      linarith
    have htot : Θq - Θc ≤ 81 / 50 * (y * ((ec4 B : ℚ) : ℝ) + ((eLhi B : ℚ) : ℝ)) := by
      rw [hc4]; linarith
    have := T4_alg_direct hcb hz1 hy0R hy0 hLhi0 htot
    push_cast
    rw [hK]
    linarith

end Terms


/-! ## Box geometry helpers -/

theorem min4_le_bilin {B : B3} {t z : ℝ} (f : ℚ → ℚ → ℚ) (α β γ : ℝ)
    (hf : ∀ u v : ℚ, ((f u v : ℚ) : ℝ) = α + β * u + γ * u * v)
    (ht0 : (B.a0 : ℝ) ≤ t) (ht1 : t ≤ (B.a1 : ℝ)) (hz0 : (B.b0 : ℝ) ≤ z) (hz1 : z ≤ (B.b1 : ℝ)) :
    ((min (min (f B.a0 B.b0) (f B.a0 B.b1)) (min (f B.a1 B.b0) (f B.a1 B.b1)) : ℚ) : ℝ) ≤
      α + β * t + γ * t * z := by
  apply bilin_ge ht0 ht1 hz0 hz1
  · rw [← hf]; exact rle (le_trans (min_le_left _ _) (min_le_left _ _))
  · rw [← hf]; exact rle (le_trans (min_le_left _ _) (min_le_right _ _))
  · rw [← hf]; exact rle (le_trans (min_le_right _ _) (min_le_left _ _))
  · rw [← hf]; exact rle (le_trans (min_le_right _ _) (min_le_right _ _))

theorem bilin_le_max4 {B : B3} {t z : ℝ} (f : ℚ → ℚ → ℚ) (α β γ : ℝ)
    (hf : ∀ u v : ℚ, ((f u v : ℚ) : ℝ) = α + β * u + γ * u * v)
    (ht0 : (B.a0 : ℝ) ≤ t) (ht1 : t ≤ (B.a1 : ℝ)) (hz0 : (B.b0 : ℝ) ≤ z) (hz1 : z ≤ (B.b1 : ℝ)) :
    α + β * t + γ * t * z ≤
      ((max (max (f B.a0 B.b0) (f B.a0 B.b1)) (max (f B.a1 B.b0) (f B.a1 B.b1)) : ℚ) : ℝ) := by
  apply bilin_le ht0 ht1 hz0 hz1
  · rw [← hf]; exact rle (le_trans (le_max_left _ _) (le_max_left _ _))
  · rw [← hf]; exact rle (le_trans (le_max_right _ _) (le_max_left _ _))
  · rw [← hf]; exact rle (le_trans (le_max_left _ _) (le_max_right _ _))
  · rw [← hf]; exact rle (le_trans (le_max_right _ _) (le_max_right _ _))

theorem bAt_cast (u v : ℚ) :
    ((bAt u v : ℚ) : ℝ) = 1 / 20000 + (-(1 / 20000)) * (u : ℝ) + (2 / 20000) * u * v := by
  simp only [bAt, mq]; push_cast; ring

theorem MAt_cast (u v : ℚ) :
    ((MAt u v : ℚ) : ℝ) = 1 / 20000 + (-(1 / 20000)) * (u : ℝ) + (1 / 20000) * u * v := by
  simp only [MAt, mq]; push_cast; ring

end CKLaneN1.Edge


