-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundCellThm
-- name    : CK_CKLaneR2_Tail_SoundCellThm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:12:08.422984+00:00
-- url     : https://prove2.me/theorems/70dc4f50-17fc-41da-bbae-76102497110d
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundCellThm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundCellThm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundCellThm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundCellThm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundCellThm.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundPhys

-- ===== source module CKLaneR2.Tail.SoundCellThm =====
section

/-!
# Lane R2 — tail checker soundness, part 10: the raw cell value bounds `u² · rayGamma`; the cell theorem
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

set_option maxHeartbeats 4000000 in
theorem rawG_le (S : FSem) (q : TCert) (sMode : Bool) (x y z : ℝ) (hph : Phys S x y z)
    (hb0 : 0 < S.b x y z) (hb : S.b x y z ≤ 1 / 2) (ht0 : 0 ≤ S.t x y z) (hub : S.u x y z < S.b x y z) :
    rawG S q sMode x y z ≤ S.u x y z ^ 2 * CKLaneN23.RS.rayGamma (S.b x y z) (S.t x y z) (S.b x y z - S.u x y z) := by
  obtain ⟨hu0, hlam, hw, hcq, hgg⟩ := hph
  unfold rawG
  simp only
  rw [hlam, hw, hcq, hgg]
  set b := S.b x y z with hbdef
  set t := S.t x y z with htdef
  set u := S.u x y z with hudef
  have hu1 : u < 1 / 2 := by linarith
  have hu1' : u < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hd : 0 < b - u := by linarith
  have hL := log2_pos
  have hbd : b - (b - u) = u := by ring
  -- entropies
  have hHu : (u * -Real.log u + (1 - u) * -Real.log (1 - u)) * (1 / Real.log 2) = H u := by
    rw [H_logs hu0 hu1']; ring
  have hHb : -(b * Real.log b + (1 - b) * Real.log (1 - b)) * (1 / Real.log 2) = H b := by
    rw [H_logs hb0 hb1]; ring
  rw [hHu, hHb]
  have hHupos : 0 < H u := H_pos hu0 (by linarith)
  have hHbpos : 0 < H b := H_pos hb0 hb1
  set E := (H u + H b) / 2 with hEdef
  have hE0 : 0 < E := by positivity
  have hE1 : E < 1 := by
    have h1 : H u < 1 := by
      have := H_strictMonoOn ⟨hu0.le, hu1.le⟩ ⟨by norm_num, le_refl _⟩ hu1
      rwa [H_half] at this
    have := H_le_one b; linarith
  -- scaled derivative inputs
  have hJu : J u = (Real.log (1 - u) - Real.log u) / Real.log 2 := by
    unfold J; rw [Real.log_div (by linarith) hu0.ne']
  have hude : -((u * -Real.log u - u * -Real.log (1 - u)) * (1 / Real.log 2)) / 2 = u * (-(J u) / 2) := by
    rw [hJu]; field_simp; ring
  have hu2dde : -(u * (1 - u)⁻¹ * (1 / Real.log 2)) / 2 = u ^ 2 * (CKLaneN23.RS.Jd1 u / 2) := by
    unfold CKLaneN23.RS.Jd1
    have : (1 - u) ≠ 0 := by linarith
    field_simp
  rw [hude, hu2dde]
  -- the three contact blocks
  have hiE : E⁻¹ = 1 / E := by ring
  have e1 : rawRS (t * (b - u) * E⁻¹) E⁻¹ (u * t) (u * (-(J u) / 2)) (u ^ 2 * (CKLaneN23.RS.Jd1 u / 2))
      = u ^ 2 * CKLaneN23.RS.raySec (t * (b - u)) t E (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2) := by
    rw [rawRS_scale]
    congr 1
    exact raySec_eq hE0 (by ring) hiE (mul_nonneg (mul_nonneg ht0 hd.le) (inv_pos.mpr hE0).le) (fun h0 => by
      rcases mul_eq_zero.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exfalso; linarith
      · exfalso; exact (inv_pos.mpr hE0).ne' h)
  have e2 : rawRS ((b - u) * E⁻¹) E⁻¹ u (u * (-(J u) / 2)) (u ^ 2 * (CKLaneN23.RS.Jd1 u / 2))
      = u ^ 2 * CKLaneN23.RS.raySec (b - u) 1 E (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2) := by
    have hsc := rawRS_scale ((b - u) * E⁻¹) E⁻¹ 1 (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2) u
    rw [mul_one] at hsc
    rw [hsc]
    congr 1
    exact raySec_eq hE0 (by ring) hiE (mul_nonneg hd.le (inv_pos.mpr hE0).le) (fun h0 => by
      exfalso; exact (mul_pos hd (inv_pos.mpr hE0)).ne' h0)
  have e3 : rawRS ((((-2 : ℤ) : ℝ) * b + 1 + t * (b - u)) * E⁻¹) E⁻¹ (u * t) (u * (-(J u) / 2))
      (u ^ 2 * (CKLaneN23.RS.Jd1 u / 2))
      = u ^ 2 * CKLaneN23.RS.raySec (1 - 2 * b + t * (b - u)) t E (-(J u) / 2) (CKLaneN23.RS.Jd1 u / 2) := by
    rw [rawRS_scale]
    congr 1
    have htd : 0 ≤ t * (b - u) := mul_nonneg ht0 hd.le
    exact raySec_eq hE0 (by push_cast; ring) hiE
      (mul_nonneg (by push_cast; linarith) (inv_pos.mpr hE0).le) (fun h0 => by
        rcases mul_eq_zero.mp h0 with h | h
        · have h' : t * (b - u) = 0 := by push_cast at h; linarith
          rcases mul_eq_zero.mp h' with h'' | h''
          · exact h''
          · exfalso; linarith
        · exfalso; exact (inv_pos.mpr hE0).ne' h)
  have e4 : rawEta E (u * (-(J u) / 2)) (u ^ 2 * (CKLaneN23.RS.Jd1 u / 2))
      = u ^ 2 * -(Scalar.etaCurvature E * (J u / 2) ^ 2 + Scalar.etaSlope E * (CKLaneN23.RS.Jd1 u / 2)) := by
    rw [rawEta_scale]
    obtain ⟨es, ec⟩ := eta_values hE0 hE1
    unfold rawEta
    rw [es, ec]
    ring
  rw [show u * t = u * t from rfl]
  rw [e1, e2, e3, e4]
  -- u² T0
  have e0 : (((3 : ℤ) : ℝ) * (u * (1 - u)⁻¹) + (b + 1 + ((-3 : ℤ) : ℝ) * u) * (((-2 : ℤ) : ℝ) * u + 1)
      * ((1 - u)⁻¹ * (1 - u)⁻¹) / 2) * (1 / Real.log 2)
      = u ^ 2 * (-3 * CKLaneN23.RS.Jd1 u + (1 - 2 * b + 3 * (b - u)) / 2 * CKLaneN23.RS.Jd2 u) := by
    unfold CKLaneN23.RS.Jd1 CKLaneN23.RS.Jd2
    have : (1 - u) ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  rw [e0]
  -- the fifth block
  have hs3 : ((-2 : ℤ) : ℝ) * b + 1 + ((2 : ℤ) : ℝ) * (t * (b - u)) = 1 - 2 * b + 2 * t * (b - u) := by
    push_cast; ring
  have h5 : (if sMode then rawT5S t u b (((-2 : ℤ) : ℝ) * b + 1 + ((2 : ℤ) : ℝ) * (t * (b - u))) (-Real.log u)⁻¹
        (-Real.log (1 - u)) (g1 u)
      else rawT5R t u (((-2 : ℤ) : ℝ) * b + 1 + ((2 : ℤ) : ℝ) * (t * (b - u))) (-Real.log u)⁻¹ (-Real.log (1 - u))
        (g1 u) (rhoF S q.rhoP x y z))
      ≤ u ^ 2 * (-(CKLaneN23.RS.raySec (1 - 2 * b + 2 * t * (b - u)) (2 * t) (H u) (-(J u))
        (CKLaneN23.RS.Jd1 u)) / 2) := by
    rw [hs3]
    cases sMode with
    | true => exact rawT5S_le hu0 hub hb ht0
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hs3nn : 0 ≤ 1 - 2 * b + 2 * t * (b - u) := by nlinarith [mul_nonneg ht0 hd.le]
      rcases hs3nn.eq_or_lt with h0 | hpos
      · have ht : t = 0 := by
          have : t * (b - u) = 0 := by nlinarith [mul_nonneg ht0 hd.le]
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exfalso; linarith
        have hrs : CKLaneN23.RS.raySec (1 - 2 * b + 2 * t * (b - u)) (2 * t) (H u) (-(J u)) (CKLaneN23.RS.Jd1 u) = 0 := by
          unfold CKLaneN23.RS.raySec
          rw [← h0, ht]
          simp [F]
        rw [hrs, ← h0, ht]
        unfold rawT5R
        simp
      · have hrho : rhoF S q.rhoP x y z = radialContact ((1 - 2 * b + 2 * t * (b - u)) / H u) 1 / u := by
          unfold rhoF
          rw [if_pos ⟨⟨hu0, hlam, hw, hcq, hgg⟩, by rw [hs3]; exact hpos⟩]
          rw [hs3]
        rw [hrho]
        exact (rawT5R_phys hu0 hu1 hpos).le
  unfold CKLaneN23.RS.rayGamma
  rw [hbd]
  have hEeq : (H u + H b) / 2 = E := rfl
  rw [hEeq]
  have ht2 : t * (b - u) = t * (b - u) := rfl
  nlinarith [h5]

/-- The cell theorem: a passing tail check certifies `rayGamma > 0` at every physical point of the chart. -/
theorem tail_sound (F : Front) (S : FSem) (hF : FOK F S) (q : TCert) (sMode : Bool)
    (hc : tailCheck F q sMode = true) :
    ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → Phys S x y z →
      0 < CKLaneN23.RS.rayGamma (S.b x y z) (S.t x y z) (S.b x y z - S.u x y z) := by
  intro x y z hx hy hz hph
  simp only [tailCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hok, hlow⟩, hDdok⟩, hDd⟩ := hc
  have hDdC : Contains one (base F).Dd (fun x y z => S.b x y z - S.u x y z) := Contains.sub hF.hB hF.hU
  have hub : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → S.u x y z < S.b x y z := by
    intro x y z hx hy hz
    have := Contains.lower_le hone hDdC hDdok x y z hx hy hz
    have h0 : (0 : ℝ) < ((base F).Dd.lower : ℝ) / one := div_pos (by exact_mod_cast hDd) CKLaneR2.Cell.hone'
    linarith
  have hC := cellG_contains F S hF q sMode hub
  have hv := Contains.lower_le hone hC hok x y z hx hy hz
  have hpos : 0 < ((cellG F q sMode).lower : ℝ) / one := div_pos (by exact_mod_cast hlow) CKLaneR2.Cell.hone'
  have hG := rawG_le S q sMode x y z hph (hF.b_pos x y z hx hy hz) (hF.b_le x y z hx hy hz)
    (hF.t_nn x y z hx hy hz) (hub x y z hx hy hz)
  have hu0 := hph.1
  have : 0 < S.u x y z ^ 2 * CKLaneN23.RS.rayGamma (S.b x y z) (S.t x y z) (S.b x y z - S.u x y z) := by linarith
  exact pos_of_mul_pos_right this (by positivity)

end CKLaneR2.Tail

end


