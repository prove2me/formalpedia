-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundPhys
-- name    : CK_CKLaneR2_Tail_SoundPhys
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:02:13.18057+00:00
-- url     : https://prove2.me/theorems/56a47474-1e1e-4b08-9db4-8ebe40f39554
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundPhys` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundPhys` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundPhys` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundPhys (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundPhys.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundAsm

-- ===== source module CKLaneR2.Tail.SoundPhys =====
section

/-!
# Lane R2 — tail checker soundness, part 9: the raw cell value at physical points and the cell theorem
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-! ## Mode S at physical points -/

set_option maxHeartbeats 4000000 in
theorem rawT5S_le {t u b : ℝ} (hu0 : 0 < u) (hub : u < b) (hb : b ≤ 1 / 2) (ht0 : 0 ≤ t) :
    rawT5S t u b (1 - 2 * b + 2 * t * (b - u)) (-Real.log u)⁻¹ (-Real.log (1 - u)) (g1 u)
      ≤ u ^ 2 * (-(CKLaneN23.RS.raySec (1 - 2 * b + 2 * t * (b - u)) (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)) / 2) := by
  have hd : 0 < b - u := by linarith
  have htd : 0 ≤ t * (b - u) := mul_nonneg ht0 hd.le
  have hu1 : u < 1 / 2 := by linarith
  have hu1' : u < 1 := by linarith
  have hL := log2_pos
  have hg1u : g1 u = (1 - u) * (-Real.log (1 - u)) / u := g1_pos_eq hu0
  set s3 := 1 - 2 * b + 2 * t * (b - u) with hs3def
  have hs3nn : 0 ≤ s3 := by rw [hs3def]; nlinarith
  have h2td : 2 * t * (b - u) ≤ s3 := by rw [hs3def]; linarith
  rcases hs3nn.eq_or_lt with h0 | hpos
  · -- s3 = 0: t = 0, both sides vanish
    have ht : t = 0 := by
      have : t * (b - u) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exfalso; linarith
    have hrs : CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u) = 0 := by
      unfold CKLaneN23.RS.raySec
      rw [← h0, ht]
      simp [F]
    rw [hrs]
    unfold rawT5S
    simp only
    rw [← h0, ht]
    simp
  · have hcl := raySec5_closed (t := t) hu0 hu1 hpos
    simp only at hcl
    rw [show u ^ 2 * (-(CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)) / 2)
        = -(u ^ 2 * CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)) / 2 by ring, hcl]
    set v := radialContact (s3 / H u) 1 with hvdef
    have hHu : 0 < H u := H_pos hu0 (by linarith)
    have hz : 0 < s3 / H u := div_pos hpos hHu
    have hv0 : 0 < v := radialContact_pos hz one_pos
    have hv1 : v < 1 / 2 := radialContact_lt_half hz one_pos
    have hv1' : v < 1 := by linarith
    have heq : s3 / H u * H v = 1 * (1 - 2 * v) := radialContact_equation hz one_pos
    set a := -Real.log u with hadef
    set c1 := -Real.log (1 - u) with hc1def
    set av := -Real.log v with havdef
    set cv := -Real.log (1 - v) with hcvdef
    set L := Real.log 2 with hLdef
    have ha : 0 < a := by have := Real.log_neg hu0 hu1'; linarith
    have hc1 : 0 ≤ c1 := by
      have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - u) (by linarith); linarith
    have hav : 0 < av := by have := Real.log_neg hv0 hv1'; linarith
    have hcv : 0 ≤ cv := by
      have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - v) (by linarith); linarith
    have hHuE : H u = (u * a + (1 - u) * c1) / L := H_logs hu0 hu1'
    have hHvE : H v = (v * av + (1 - v) * cv) / L := H_logs hv0 hv1'
    have hHuL : 0 < u * a + (1 - u) * c1 := by
      have := mul_pos hHu hL; rw [hHuE, div_mul_cancel₀ _ hL.ne'] at this; exact this
    have hHvL : 0 < v * av + (1 - v) * cv := by
      have := mul_pos (H_pos hv0 (by linarith)) hL; rw [hHvE, div_mul_cancel₀ _ hL.ne'] at this; exact this
    have hcontact : s3 * (v * av + (1 - v) * cv) = (1 - 2 * v) * (u * a + (1 - u) * c1) := by
      rw [hHuE, hHvE] at heq
      field_simp at heq
      linarith
    have hk : 0 < av + cv := by linarith
    have hRv := Rv_le_two hv0 hv1.le havdef hcvdef
    have hkd : (1 - 2 * v) ^ 2 ≤ av + cv := by
      have hvv : v * (1 - v) ≤ 1 / 4 := by nlinarith
      have hl : Real.log (v * (1 - v)) ≤ Real.log (1 / 4) := Real.log_le_log (by nlinarith) hvv
      have hl4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
        rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
      have hsum : av + cv = -Real.log (v * (1 - v)) := by
        rw [havdef, hcvdef, Real.log_mul hv0.ne' (by linarith)]; ring
      have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have : 1 < av + cv := by rw [hsum]; linarith
      nlinarith
    have hQA := QA_le (t := t) hL hv0 hv1 hpos hHuL hHvL hk hkd hRv hcontact
    have hQB := QB_le hL hu0 hu1' hv0 hv1 hpos ha hc1 hHvL hk hRv
    set ω := u * (a - c1) / (u * a + (1 - u) * c1) with hω
    have hq2 := q2_le hpos hd ht0 h2td ω
    have homega : (1 - a⁻¹ * c1) * (a⁻¹ * g1 u + 1)⁻¹ = ω := by
      rw [hg1u, hω]; field_simp; ring
    unfold rawT5S
    simp only
    rw [homega]
    push_cast
    have hUB1 : 4 * ((2 * (t * u) + s3 * ω) ^ 2 / s3) / L
        ≤ 4 * ((2 * (t * u * u * (b - u)⁻¹) + 4 * (t * u * ω) + s3 * (ω * ω)) * (1 / L)) := by
      rw [show 4 * ((2 * (t * u * u * (b - u)⁻¹) + 4 * (t * u * ω) + s3 * (ω * ω)) * (1 / L))
          = 4 * (2 * (t * u * u * (b - u)⁻¹) + 4 * (t * u * ω) + s3 * (ω * ω)) / L by ring]
      apply div_le_div_of_nonneg_right _ hL.le
      linarith
    have hUB2 : 2 * s3 * a⁻¹ / (L * (1 - u)) = 2 * (s3 * a⁻¹) * (1 / L * (1 - u)⁻¹) := by
      field_simp
    linarith

/-! ## The raw cell value at physical points -/

theorem rawRS_scale (z ie ds de dde u : ℝ) :
    rawRS z ie (u * ds) (u * de) (u ^ 2 * dde) = u ^ 2 * rawRS z ie ds de dde := by
  unfold rawRS; ring

theorem rawEta_scale (E de dde u : ℝ) : rawEta E (u * de) (u ^ 2 * dde) = u ^ 2 * rawEta E de dde := by
  unfold rawEta; ring

end CKLaneR2.Tail

end


