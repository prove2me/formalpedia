-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundT5Final
-- name    : CK_CKLaneR2_Tail_SoundT5Final
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:51:29.816276+00:00
-- url     : https://prove2.me/theorems/e2b7dd5f-0a1a-423d-bab8-8e6d2ec663ef
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundT5Final` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundT5Final` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundT5Final` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundT5Final (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundT5Final.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundT5Phys

-- ===== source module CKLaneR2.Tail.SoundT5Final =====
section

/-!
# Lane R2 — tail checker soundness, part 7: mode R identity at physical points
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

theorem g1_pos_eq {x : ℝ} (hx : 0 < x) : g1 x = (1 - x) * (-Real.log (1 - x)) / x := by
  unfold g1; rw [if_neg hx.ne']; ring

section AtomSimp

variable {u v a c1 av cv : ℝ}

theorem at_X (hv : 0 < v) (ha : 0 < a) :
    a⁻¹ * ((1 - v) * cv / v) - a⁻¹ * (a - av) + 1 = (v * av + (1 - v) * cv) / (v * a) := by
  field_simp; ring

theorem at_Yc (ha : 0 < a) : a⁻¹ * cv - a⁻¹ * (a - av) + 1 = (av + cv) / a := by
  field_simp; ring

theorem at_LG1 (hu : 0 < u) (ha : 0 < a) : a⁻¹ * ((1 - u) * c1 / u) + 1 = (u * a + (1 - u) * c1) / (u * a) := by
  field_simp; ring

theorem at_omega (hu : 0 < u) (ha : 0 < a) (hH : 0 < u * a + (1 - u) * c1) :
    (1 - a⁻¹ * c1) * ((u * a + (1 - u) * c1) / (u * a))⁻¹ = u * (a - c1) / (u * a + (1 - u) * c1) := by
  field_simp

end AtomSimp

set_option maxHeartbeats 4000000 in
theorem rawT5R_atoms {L u v a c1 av cv s3 t : ℝ} (hL : 0 < L) (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1)
    (ha : 0 < a) (hH : 0 < u * a + (1 - u) * c1) (hh : 0 < v * av + (1 - v) * cv) (hk : 0 < av + cv) :
    let X := (v * av + (1 - v) * cv) / (v * a)
    let Yc := (av + cv) / a
    let om2v := 1 - 2 * v
    let Yd := Yc - a⁻¹ * (om2v * om2v)
    let LG1 := (u * a + (1 - u) * c1) / (u * a)
    let omega := u * (a - c1) / (u * a + (1 - u) * c1)
    let Yt := ((X * X) * Yd) * (((1 - v)⁻¹ * (1 - v)⁻¹) * ((Yc⁻¹ * Yc⁻¹) * Yc⁻¹))
    let q := 2 * (t * u) + s3 * omega
    let A1 := (((q * q) * (v / u)) * (X * Yt)) * (1 / L * LG1⁻¹)
    let A2 := ((s3 * om2v) * (X * a⁻¹)) * (1 / L * (((1 - u)⁻¹ * (1 - v)⁻¹) * (Yc⁻¹ * LG1⁻¹)))
    A1 = QA L u v a c1 av cv s3 t ∧ A2 = QB L u v a c1 av cv s3 := by
  intro X Yc om2v Yd LG1 omega Yt q A1 A2
  have hv1' : 0 < 1 - v := by linarith
  have hu1' : 0 < 1 - u := by linarith
  constructor
  · simp only [A1, Yt, Yd, X, Yc, om2v, LG1, q, omega, QA]
    field_simp
    try ring
  · simp only [A2, X, Yc, om2v, LG1, QB]
    field_simp
    try ring

set_option maxHeartbeats 4000000 in
theorem rawT5R_phys {t u s3 : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) (hs3 : 0 < s3) :
    rawT5R t u s3 (-Real.log u)⁻¹ (-Real.log (1 - u)) (g1 u) (radialContact (s3 / H u) 1 / u)
      = u ^ 2 * (-(CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)) / 2) := by
  have hcl := raySec5_closed (t := t) hu0 hu1 hs3
  simp only at hcl
  rw [show u ^ 2 * (-(CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)) / 2)
      = -(u ^ 2 * CKLaneN23.RS.raySec s3 (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u)) / 2 by ring, hcl]
  set v := radialContact (s3 / H u) 1 with hvdef
  have hHu : 0 < H u := H_pos hu0 (by linarith)
  have hz : 0 < s3 / H u := div_pos hs3 hHu
  have hv0 : 0 < v := radialContact_pos hz one_pos
  have hv1 : v < 1 / 2 := radialContact_lt_half hz one_pos
  have hu1' : u < 1 := by linarith
  have hv1' : v < 1 := by linarith
  have hL := log2_pos
  have huv : u * (v / u) = v := by field_simp
  have hlr : Real.log (v / u) = -Real.log u - -Real.log v := by rw [Real.log_div hv0.ne' hu0.ne']; ring
  have hg1v : g1 v = (1 - v) * (-Real.log (1 - v)) / v := g1_pos_eq hv0
  have hg1u : g1 u = (1 - u) * (-Real.log (1 - u)) / u := g1_pos_eq hu0
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
  have hk : 0 < av + cv := by linarith
  obtain ⟨e1, e2⟩ := rawT5R_atoms (s3 := s3) (t := t) hL hu0 hu1' hv0 hv1' ha hHuL hHvL hk
  unfold rawT5R
  simp only
  rw [huv, hlr, hg1v, hg1u]
  rw [at_X hv0 ha, at_Yc ha, at_LG1 hu0 ha, at_omega hu0 ha hHuL]
  rw [← e1, ← e2]
  push_cast
  ring

end CKLaneR2.Tail

end


