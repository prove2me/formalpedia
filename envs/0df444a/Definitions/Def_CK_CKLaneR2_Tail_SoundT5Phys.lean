-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundT5Phys
-- name    : CK_CKLaneR2_Tail_SoundT5Phys
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:45:28.827824+00:00
-- url     : https://prove2.me/theorems/589c1e3b-8fdd-4edc-8b4f-c2ed0d7c839e
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundT5Phys` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundT5Phys` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundT5Phys` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundT5Phys (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundT5Phys.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundT5R

-- ===== source module CKLaneR2.Tail.SoundT5Phys =====
section

/-!
# Lane R2 — tail checker soundness, part 6: the fifth block at physical points (mode R identity, mode S bound)
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-! ## `Rv ≤ 2`: `v ln(1/v) + (1-v) ln(1/(1-v)) ≤ 2 v (1-v) (ln(1/v) + ln(1/(1-v)))` on `(0, 1/2]` -/

theorem psi_nonneg {v : ℝ} (h0 : 0 < v) (h1 : v ≤ 1 / 2) :
    (1 - v) * (-Real.log (1 - v)) ≤ v * (-Real.log v) := by
  have h1v : 0 < 1 - v := by linarith
  by_cases hA : v ≤ 9 / 25
  · -- ln(1/v) ≥ 1 and (1-v) ln(1/(1-v)) ≤ v
    have he : Real.exp 1 < 25 / 9 := by have := Real.exp_one_lt_d9; linarith
    have hlv : Real.log v ≤ -1 := by
      rw [Real.log_le_iff_le_exp h0]
      have : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
      rw [this]
      have hpos : 0 < Real.exp 1 := Real.exp_pos 1
      rw [le_inv_comm₀ h0 hpos]
      calc Real.exp 1 ≤ 25 / 9 := he.le
        _ ≤ v⁻¹ := by rw [le_inv_comm₀ (by norm_num) h0]; linarith
    have hl2 := Real.one_sub_inv_le_log_of_pos h1v
    have hc : (1 - v) * (-Real.log (1 - v)) ≤ v := by
      have e : (1 - v) * (1 - (1 - v)⁻¹) = -v := by field_simp; ring
      nlinarith
    nlinarith
  · push_neg at hA
    set w := 1 / 2 - v with hw
    have hw0 : 0 ≤ w := by linarith
    -- (1/2)(ln(1-v) - ln v) ≥ 2w
    have ht : 0 ≤ (1 - 2 * v) / v := div_nonneg (by linarith) h0.le
    have hlog1 := Real.le_log_one_add_of_nonneg ht
    have e1 : 1 + (1 - 2 * v) / v = (1 - v) / v := by field_simp; ring
    have e2 : 2 * ((1 - 2 * v) / v) / ((1 - 2 * v) / v + 2) = 2 * (1 - 2 * v) := by
      field_simp
      ring
    rw [e1, e2, Real.log_div h1v.ne' h0.ne'] at hlog1
    -- ln(v(1-v)) ≥ -2
    have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
    have hvv : 1 / 5 ≤ v * (1 - v) := by nlinarith
    have hexp : Real.exp (-2) ≤ 1 / 5 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      norm_num at hq ⊢; linarith
    have hlog2 : -2 ≤ Real.log v + Real.log (1 - v) := by
      rw [← Real.log_mul h0.ne' h1v.ne']
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith
    nlinarith

theorem Rv_le_two {v av cv : ℝ} (h0 : 0 < v) (h1 : v ≤ 1 / 2) (hav : av = -Real.log v)
    (hcv : cv = -Real.log (1 - v)) :
    v * av + (1 - v) * cv ≤ 2 * v * (1 - v) * (av + cv) := by
  have hp := psi_nonneg h0 h1
  rw [hav, hcv]
  nlinarith

/-! ## Rewriting Lane C's closed forms at `δ = 1 - 2v` -/

theorem cforms {v : ℝ} (h0 : 0 < v) (h1 : v < 1) :
    cJ (1 - 2 * v) = (-Real.log v - -Real.log (1 - v)) / Real.log 2 ∧
    cHn (1 - 2 * v) = v * -Real.log v + (1 - v) * -Real.log (1 - v) ∧
    cKap (1 - 2 * v) = (-Real.log v + -Real.log (1 - v)) / 2 ∧
    cOm (1 - 2 * v) = 4 * v * (1 - v) := by
  have h1v : 0 < 1 - v := by linarith
  have hp : Real.log (1 - 2 * v + 1) = Real.log 2 + Real.log (1 - v) := by
    rw [show 1 - 2 * v + 1 = 2 * (1 - v) by ring, Real.log_mul two_ne_zero h1v.ne']
  have hm : Real.log (1 - (1 - 2 * v)) = Real.log 2 + Real.log v := by
    rw [show 1 - (1 - 2 * v) = 2 * v by ring, Real.log_mul two_ne_zero h0.ne']
  have hL := log2_pos.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cJ; rw [hp, hm]; field_simp; ring
  · unfold cHn; rw [hp, hm]; ring
  · unfold cKap; rw [hp, hm]; ring
  · unfold cOm; ring

/-! ## `u² · raySec5` in closed form -/

/-- The quadratic-form part `QA` and the `dde` part `QB` (atoms). -/
noncomputable def QA (L u v a c1 av cv s3 t : ℝ) : ℝ :=
  (2 * (t * u) + s3 * (u * (a - c1) / (u * a + (1 - u) * c1))) ^ 2
    * ((v * av + (1 - v) * cv) ^ 3 * ((av + cv) - (1 - 2 * v) ^ 2)
      / (L * (u * a + (1 - u) * c1) * (v ^ 2 * (1 - v) ^ 2 * (av + cv) ^ 3)))

noncomputable def QB (L u v a c1 av cv s3 : ℝ) : ℝ :=
  s3 * (1 - 2 * v) * (v * av + (1 - v) * cv) * u
    / (2 * v * ((av + cv) / 2) * L * (1 - u) * (1 - v) * (u * a + (1 - u) * c1))

theorem raySec5_closed {t u s3 : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) (hs3 : 0 < s3) :
    let v := radialContact (s3 / H u) 1
    u ^ 2 * CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)
      = QA (Real.log 2) u v (-Real.log u) (-Real.log (1 - u)) (-Real.log v) (-Real.log (1 - v)) s3 t
        + QB (Real.log 2) u v (-Real.log u) (-Real.log (1 - u)) (-Real.log v) (-Real.log (1 - v)) s3 := by
  intro v
  have hHu : 0 < H u := H_pos hu0 (by linarith)
  have hz : 0 < s3 / H u := div_pos hs3 hHu
  have hv0 : 0 < v := radialContact_pos hz one_pos
  have hv1 : v < 1 / 2 := radialContact_lt_half hz one_pos
  have heq : s3 / H u * H v = 1 * (1 - 2 * v) := radialContact_equation hz one_pos
  have hu1' : u < 1 := by linarith
  have hv1' : v < 1 := by linarith
  have hL := log2_pos
  set L := Real.log 2 with hLdef
  set a := -Real.log u with hadef
  set c1 := -Real.log (1 - u) with hc1def
  set av := -Real.log v with havdef
  set cv := -Real.log (1 - v) with hcvdef
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
  have hk : 0 < av + cv := by linarith
  have hcontact : s3 * (v * av + (1 - v) * cv) = (1 - 2 * v) * (u * a + (1 - u) * c1) := by
    rw [hHuE, hHvE] at heq
    field_simp at heq
    linarith
  have hJu : J u = (a - c1) / L := by
    unfold J; rw [Real.log_div (by linarith) hu0.ne']; simp only [hadef, hc1def, hLdef]; ring
  have hJd1 : CKLaneN23.RS.Jd1 u = -1 / (L * u * (1 - u)) := by unfold CKLaneN23.RS.Jd1; rfl
  -- raySec via Lane C's raw form
  have hrs := raySec_eq (s := s3) (ds := 2 * t) (e := H u) (de := -(J u)) (dde := CKLaneN23.RS.Jd1 u)
    (zf := s3 / H u) (ief := 1 / H u) hHu rfl rfl hz.le (fun h => absurd h hz.ne')
  rw [← hrs]
  have hdC : dC (s3 / H u) = 1 - 2 * v := by unfold dC; rw [if_neg hz.ne']
  rw [hdC]
  obtain ⟨hcJ, hcHn, hcKap, hcOm⟩ := cforms hv0 hv1'
  unfold cF1 cF2
  rw [hcJ, hcHn, hcKap, hcOm, hHuE, hJu, hJd1]
  have hA := t5_partA (t := t) hL hu0 hv0 hv1' hHuL hHvL hk hcontact
  have hB := t5_partB (s3 := s3) hL hu0 hu1' hv0 hv1' hHuL hk
  unfold QA QB
  rw [← hA, ← hB]
  ring

end CKLaneR2.Tail

end


