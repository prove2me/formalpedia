-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerFinal_v2
-- name    : CK_CKLaneN23_CornerFinal_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T11:13:34.747679+00:00
-- url     : https://prove2.me/theorems/2ae7eade-b07d-4c68-9752-f7e5d476cc2c
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerFinal.lean)

import Definitions.Def_CK_CKLaneN23_TChain_v2
import Definitions.Def_CK_CKLaneN23_CPos

-- ===== source module CKLaneN23.CornerFinal =====
section

/-!
# CKLaneN23.CornerFinal — the RA-stat corner certificate `GammaCorner (1/20)` (Lane N23b)

* `F_tc_Gam_eq` : on the corner domain (`x ∈ (0, 1/20]`, `σ ∈ (-1/2, 1/2]`, `|τ| ≤ 1/2`) the trivariate
  chain's semantic function is exactly `rayGamma (1/2 - x(1/2-σ)) (1/2+τ) (x(1/2+σ))`.
* `cornerCheck` : the Boolean checker (univariate contact chain, univariate entropy chain, trivariate
  chain, positivity grid).  `cornerCheck_sound : cornerCheck = true → GammaCorner (1/20)`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

open GeneralCK CKLaneN23.RS

/-- corner coordinates `b = 1/2 - x(1/2-σ)`, `d = x(1/2+σ)`, `t = 1/2+τ` -/
noncomputable def bOf (x σ : ℝ) : ℝ := 1 / 2 - x * (1 / 2 - σ)
noncomputable def dOf (x σ : ℝ) : ℝ := x * (1 / 2 + σ)
noncomputable def tOf (τ : ℝ) : ℝ := 1 / 2 + τ

theorem bd_sub (x σ : ℝ) : bOf x σ - dOf x σ = 1 / 2 - x := by unfold bOf dOf; ring

/-! ## the generic contact-block identity -/

theorem raySec_chain (s ds ie de dde : ℝ) (hie : 0 < ie) (hs : 0 ≤ s) (hs0 : s = 0 → ds = 0) :
    (ds + ((-1 : ℚ) : ℝ) * (s * ie * de)) * (ds + ((-1 : ℚ) : ℝ) * (s * ie * de)) * ie *
        Phi2 (((((1 : ℚ) / 2) : ℚ) : ℝ) * (((2 : ℚ) : ℝ) * (s * ie * (s * ie)))) +
      ((-1 : ℚ) : ℝ) * (s * ie * dde *
        (s * ie * Phi1 (((((1 : ℚ) / 2) : ℚ) : ℝ) * (((2 : ℚ) : ℝ) * (s * ie * (s * ie)))))) +
      dde * Phi0 (((((1 : ℚ) / 2) : ℚ) : ℝ) * (((2 : ℚ) : ℝ) * (s * ie * (s * ie)))) =
    raySec s ds (1 / ie) de dde := by
  have e1 : ((((1 : ℚ) / 2) : ℚ) : ℝ) * (((2 : ℚ) : ℝ) * (s * ie * (s * ie))) = (s * ie) ^ 2 := by
    push_cast; ring
  rw [e1]
  unfold raySec
  have hsd : s / (1 / ie) = s * ie := by field_simp
  rw [hsd]
  have hz : 0 ≤ s * ie := mul_nonneg hs hie.le
  rcases hz.lt_or_eq with hpos | hzero
  · obtain ⟨h0, h1, h2⟩ := contact_values hpos
    rw [h0, h2, ← h1]
    push_cast
    field_simp
    ring
  · have hs0' : s = 0 := by
      rcases mul_eq_zero.mp hzero.symm with h | h
      · exact h
      · linarith
    have hds := hs0 hs0'
    subst hs0'
    subst hds
    simp [F, Phi0_zero]

/-! ## pointwise identities of the chain pieces -/

section pieces

variable {x σ τ : ℝ}

theorem c_one : F_tc_one x σ τ = 1 := by
  show LPoly.eval (Real.log 2) [(0, (1 : ℚ))] = 1
  rw [LPoly.eval_c]; norm_num

theorem c_Hu (hd : Dom x σ τ) : F_tc_Hu x σ τ = H (bOf x σ - dOf x σ) := by
  show hent (Real.sqrt ((2 * x) ^ 2)) = _
  rw [Real.sqrt_sq (by linarith [hd.1]), bd_sub]
  unfold hent; congr 1; ring

theorem c_Hb (hd : Dom x σ τ) : F_tc_Hb x σ τ = H (bOf x σ) := by
  show hent (Real.sqrt ((2 * (x * (1 / 2 - σ))) ^ 2)) = _
  have hσ := (abs_le.mp hd.2.2.1).2
  rw [Real.sqrt_sq (by nlinarith [hd.1])]
  unfold hent bOf; congr 1; ring

theorem c_E (hd : Dom x σ τ) :
    F_tc_E x σ τ = (H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2 := by
  show ((((1 : ℚ) / 2) : ℚ) : ℝ) * (F_tc_Hu x σ τ + F_tc_Hb x σ τ) = _
  rw [c_Hu hd, c_Hb hd]; push_cast; ring

theorem c_eps (hd : Dom x σ τ) :
    F_tc_eps x σ τ = 1 - (H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2 := by
  show F_tc_one x σ τ + ((-1 : ℚ) : ℝ) * F_tc_E x σ τ = _
  rw [c_one, c_E hd]; push_cast; ring

theorem c_invE (hd : Dom x σ τ) :
    F_tc_invE x σ τ = 1 / ((H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2) := by
  show 1 / (1 - F_tc_eps x σ τ) = _
  rw [c_eps hd]; congr 1; ring

theorem c_invHu (hd : Dom x σ τ) : F_tc_invHu x σ τ = 1 / H (bOf x σ - dOf x σ) := by
  show 1 / (1 - (F_tc_one x σ τ + ((-1 : ℚ) : ℝ) * F_tc_Hu x σ τ)) = _
  rw [c_one, c_Hu hd]; push_cast; congr 1; ring

theorem c_Ju (hd : Dom x σ τ) : F_tc_Ju x σ τ = J (bOf x σ - dOf x σ) := by
  show LPoly.eval (Real.log 2) [(-1, (4 : ℚ))] * (x * Adiv ((2 * x) ^ 2)) = _
  have hx := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  rw [LPoly.eval_invL, Adiv_of_pos (by linarith : (0 : ℝ) < 2 * x), bd_sub]
  unfold J atanhR
  have e : (1 - (1 / 2 - x)) / (1 / 2 - x) = (1 + 2 * x) / (1 - 2 * x) := by
    have : (1 / 2 - x) ≠ 0 := by linarith
    have : (1 - 2 * x) ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  have hL : Real.log 2 ≠ 0 := by positivity
  have hx0 : x ≠ 0 := hx.ne'
  push_cast
  field_simp
  ring

theorem c_Jd1 (hd : Dom x σ τ) : F_tc_Jd1 x σ τ = Jd1 (bOf x σ - dOf x σ) := by
  show LPoly.eval (Real.log 2) [(-1, ((-4 : ℚ)))] * (1 / (1 - (2 * x) ^ 2)) = _
  have hx := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  rw [LPoly.eval_invL, bd_sub]
  unfold Jd1
  have h1 : (1 / 2 - x) ≠ 0 := by linarith
  have h2 : (1 - (1 / 2 - x)) ≠ 0 := by linarith
  have h3 : (1 - (2 * x) ^ 2) ≠ 0 := by nlinarith
  have hL : Real.log 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem c_Jd2 (hd : Dom x σ τ) : F_tc_Jd2 x σ τ = Jd2 (bOf x σ - dOf x σ) := by
  show LPoly.eval (Real.log 2) [(-1, (32 : ℚ))] *
    (x * (1 / (1 - (2 * x) ^ 2) * (1 / (1 - (2 * x) ^ 2)))) = _
  have hx := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  rw [LPoly.eval_invL, bd_sub]
  unfold Jd2
  have h1 : (1 / 2 - x) ≠ 0 := by linarith
  have h2 : (1 - (1 / 2 - x)) ≠ 0 := by linarith
  have h3 : (1 - (2 * x) ^ 2) ≠ 0 := by nlinarith
  have hL : Real.log 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem c_Ap (hd : Dom x σ τ) :
    F_tc_Ap x σ τ = -3 * Jd1 (bOf x σ - dOf x σ) +
      (1 - 2 * bOf x σ + 3 * dOf x σ) / 2 * Jd2 (bOf x σ - dOf x σ) := by
  show ((-3 : ℚ) : ℝ) * F_tc_Jd1 x σ τ +
    (x * (1 / 2 - σ) + ((((3 : ℚ) / 2) : ℚ) : ℝ) * (x * (1 / 2 + σ))) * F_tc_Jd2 x σ τ = _
  rw [c_Jd1 hd, c_Jd2 hd]
  unfold bOf dOf
  push_cast
  ring

theorem Hb_pos (hd : Dom x σ τ) : 0 < H (bOf x σ) := by
  have hx := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  have hσ := abs_le.mp hd.2.2.1
  apply H_pos <;> unfold bOf <;> nlinarith

theorem Hu_pos (hd : Dom x σ τ) : 0 < H (bOf x σ - dOf x σ) := by
  have hx := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  rw [bd_sub]; apply H_pos <;> linarith

theorem Hu_lt_one (hd : Dom x σ τ) : H (bOf x σ - dOf x σ) < 1 := by
  have hx := hd.1
  have hxE : x ≤ 1 / 20 := by have := hd.2.1; simpa [Eps] using this
  have h := H_strictMonoOn (show (1 / 2 - x : ℝ) ∈ Set.Icc 0 (1 / 2) from ⟨by linarith, by linarith⟩)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) from ⟨by norm_num, le_rfl⟩) (show (1 / 2 - x : ℝ) < 1 / 2 by linarith)
  rw [H_half] at h
  rw [bd_sub]
  exact h

theorem E_pos (hd : Dom x σ τ) : 0 < (H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2 := by
  have := Hu_pos hd; have := Hb_pos hd; linarith

theorem E_lt_one (hd : Dom x σ τ) : (H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2 < 1 := by
  have := Hu_lt_one hd; have := H_le_one (bOf x σ); linarith

theorem c_RS1 (hd : Dom x σ τ) (hσ : -1 / 2 < σ) :
    F_tc_RS1 x σ τ = raySec (tOf τ * dOf x σ) (tOf τ) ((H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2)
      (-(J (bOf x σ - dOf x σ)) / 2) (Jd1 (bOf x σ - dOf x σ) / 2) := by
  have hx := hd.1
  have hτ := abs_le.mp hd.2.2.2
  have hie : 0 < F_tc_invE x σ τ := by rw [c_invE hd]; exact one_div_pos.mpr (E_pos hd)
  have hs : 0 ≤ F_tc_td x σ τ := by
    show 0 ≤ (1 / 2 + τ) * (x * (1 / 2 + σ)); apply mul_nonneg <;> nlinarith
  have hs0 : F_tc_td x σ τ = 0 → F_tc_Tt x σ τ = 0 := by
    intro h
    change (1 / 2 + τ) * (x * (1 / 2 + σ)) = 0 at h
    show 1 / 2 + τ = 0
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exfalso; have : 0 < x * (1 / 2 + σ) := mul_pos hx (by linarith); linarith
  have key := raySec_chain (F_tc_td x σ τ) (F_tc_Tt x σ τ) (F_tc_invE x σ τ) (F_tc_E1 x σ τ)
    (F_tc_E2 x σ τ) hie hs hs0
  have hl : F_tc_RS1 x σ τ = raySec (F_tc_td x σ τ) (F_tc_Tt x σ τ) (1 / F_tc_invE x σ τ)
      (F_tc_E1 x σ τ) (F_tc_E2 x σ τ) := key
  rw [hl, c_invE hd, one_div_one_div]
  have h1 : F_tc_td x σ τ = tOf τ * dOf x σ := rfl
  have h2 : F_tc_Tt x σ τ = tOf τ := rfl
  have h3 : F_tc_E1 x σ τ = -(J (bOf x σ - dOf x σ)) / 2 := by
    show ((((-1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Ju x σ τ = _
    rw [c_Ju hd]; push_cast; ring
  have h4 : F_tc_E2 x σ τ = Jd1 (bOf x σ - dOf x σ) / 2 := by
    show ((((1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Jd1 x σ τ = _
    rw [c_Jd1 hd]; push_cast; ring
  rw [h1, h2, h3, h4]

theorem c_RS2 (hd : Dom x σ τ) (hσ : -1 / 2 < σ) :
    F_tc_RS2 x σ τ = raySec (dOf x σ) 1 ((H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2)
      (-(J (bOf x σ - dOf x σ)) / 2) (Jd1 (bOf x σ - dOf x σ) / 2) := by
  have hx := hd.1
  have hie : 0 < F_tc_invE x σ τ := by rw [c_invE hd]; exact one_div_pos.mpr (E_pos hd)
  have hs : 0 ≤ F_tc_Dd x σ τ := by
    show 0 ≤ x * (1 / 2 + σ); apply mul_nonneg <;> linarith
  have hs0 : F_tc_Dd x σ τ = 0 → F_tc_one x σ τ = 0 := by
    intro h
    change x * (1 / 2 + σ) = 0 at h
    exfalso; have : 0 < x * (1 / 2 + σ) := mul_pos hx (by linarith); linarith
  have key := raySec_chain (F_tc_Dd x σ τ) (F_tc_one x σ τ) (F_tc_invE x σ τ) (F_tc_E1 x σ τ)
    (F_tc_E2 x σ τ) hie hs hs0
  have hl : F_tc_RS2 x σ τ = raySec (F_tc_Dd x σ τ) (F_tc_one x σ τ) (1 / F_tc_invE x σ τ)
      (F_tc_E1 x σ τ) (F_tc_E2 x σ τ) := key
  rw [hl, c_invE hd, one_div_one_div, c_one]
  have h1 : F_tc_Dd x σ τ = dOf x σ := rfl
  have h3 : F_tc_E1 x σ τ = -(J (bOf x σ - dOf x σ)) / 2 := by
    show ((((-1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Ju x σ τ = _
    rw [c_Ju hd]; push_cast; ring
  have h4 : F_tc_E2 x σ τ = Jd1 (bOf x σ - dOf x σ) / 2 := by
    show ((((1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Jd1 x σ τ = _
    rw [c_Jd1 hd]; push_cast; ring
  rw [h1, h3, h4]

theorem c_RS3 (hd : Dom x σ τ) (hσ : -1 / 2 < σ) :
    F_tc_RS3 x σ τ = raySec (1 - 2 * bOf x σ + tOf τ * dOf x σ) (tOf τ)
      ((H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2)
      (-(J (bOf x σ - dOf x σ)) / 2) (Jd1 (bOf x σ - dOf x σ) / 2) := by
  have hx := hd.1
  have hσ2 := (abs_le.mp hd.2.2.1).2
  have hτ := abs_le.mp hd.2.2.2
  have hie : 0 < F_tc_invE x σ τ := by rw [c_invE hd]; exact one_div_pos.mpr (E_pos hd)
  have hs3 : F_tc_s3 x σ τ = 1 - 2 * bOf x σ + tOf τ * dOf x σ := by
    show (((2 : ℚ) : ℝ)) * (x * (1 / 2 - σ)) + (1 / 2 + τ) * (x * (1 / 2 + σ)) = _
    unfold bOf dOf tOf; push_cast; ring
  have hs : 0 ≤ F_tc_s3 x σ τ := by
    show 0 ≤ (((2 : ℚ) : ℝ)) * (x * (1 / 2 - σ)) + (1 / 2 + τ) * (x * (1 / 2 + σ))
    have h1 : 0 ≤ x * (1 / 2 - σ) := mul_nonneg hx.le (by linarith)
    have h2 : 0 ≤ (1 / 2 + τ) * (x * (1 / 2 + σ)) := mul_nonneg (by linarith) (mul_nonneg hx.le (by linarith))
    push_cast; linarith
  have hs0 : F_tc_s3 x σ τ = 0 → F_tc_Tt x σ τ = 0 := by
    intro h
    change (((2 : ℚ) : ℝ)) * (x * (1 / 2 - σ)) + (1 / 2 + τ) * (x * (1 / 2 + σ)) = 0 at h
    show 1 / 2 + τ = 0
    have h1 : 0 ≤ x * (1 / 2 - σ) := mul_nonneg hx.le (by linarith)
    have h2 : 0 ≤ (1 / 2 + τ) * (x * (1 / 2 + σ)) := mul_nonneg (by linarith) (mul_nonneg hx.le (by linarith))
    push_cast at h
    have h3 : (1 / 2 + τ) * (x * (1 / 2 + σ)) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exfalso; have : 0 < x * (1 / 2 + σ) := mul_pos hx (by linarith); linarith
  have key := raySec_chain (F_tc_s3 x σ τ) (F_tc_Tt x σ τ) (F_tc_invE x σ τ) (F_tc_E1 x σ τ)
    (F_tc_E2 x σ τ) hie hs hs0
  have hl : F_tc_RS3 x σ τ = raySec (F_tc_s3 x σ τ) (F_tc_Tt x σ τ) (1 / F_tc_invE x σ τ)
      (F_tc_E1 x σ τ) (F_tc_E2 x σ τ) := key
  rw [hl, c_invE hd, one_div_one_div, hs3]
  have h2 : F_tc_Tt x σ τ = tOf τ := rfl
  have h3 : F_tc_E1 x σ τ = -(J (bOf x σ - dOf x σ)) / 2 := by
    show ((((-1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Ju x σ τ = _
    rw [c_Ju hd]; push_cast; ring
  have h4 : F_tc_E2 x σ τ = Jd1 (bOf x σ - dOf x σ) / 2 := by
    show ((((1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Jd1 x σ τ = _
    rw [c_Jd1 hd]; push_cast; ring
  rw [h2, h3, h4]

theorem c_RS4 (hd : Dom x σ τ) (hσ : -1 / 2 < σ) :
    F_tc_RS4 x σ τ = raySec (1 - 2 * bOf x σ + 2 * tOf τ * dOf x σ) (2 * tOf τ)
      (H (bOf x σ - dOf x σ)) (-(J (bOf x σ - dOf x σ))) (Jd1 (bOf x σ - dOf x σ)) := by
  have hx := hd.1
  have hσ2 := (abs_le.mp hd.2.2.1).2
  have hτ := abs_le.mp hd.2.2.2
  have hie : 0 < F_tc_invHu x σ τ := by rw [c_invHu hd]; exact one_div_pos.mpr (Hu_pos hd)
  have hs4 : F_tc_s4 x σ τ = 1 - 2 * bOf x σ + 2 * tOf τ * dOf x σ := by
    show (((2 : ℚ) : ℝ)) * (x * (1 / 2 - σ)) + (((2 : ℚ) : ℝ)) * ((1 / 2 + τ) * (x * (1 / 2 + σ))) = _
    unfold bOf dOf tOf; push_cast; ring
  have hs : 0 ≤ F_tc_s4 x σ τ := by
    show 0 ≤ (((2 : ℚ) : ℝ)) * (x * (1 / 2 - σ)) + (((2 : ℚ) : ℝ)) * ((1 / 2 + τ) * (x * (1 / 2 + σ)))
    have h1 : 0 ≤ x * (1 / 2 - σ) := mul_nonneg hx.le (by linarith)
    have h2 : 0 ≤ (1 / 2 + τ) * (x * (1 / 2 + σ)) := mul_nonneg (by linarith) (mul_nonneg hx.le (by linarith))
    push_cast; linarith
  have hs0 : F_tc_s4 x σ τ = 0 → F_tc_t2 x σ τ = 0 := by
    intro h
    change (((2 : ℚ) : ℝ)) * (x * (1 / 2 - σ)) + (((2 : ℚ) : ℝ)) * ((1 / 2 + τ) * (x * (1 / 2 + σ))) = 0 at h
    show (((2 : ℚ) : ℝ)) * (1 / 2 + τ) = 0
    have h1 : 0 ≤ x * (1 / 2 - σ) := mul_nonneg hx.le (by linarith)
    have h2 : 0 ≤ (1 / 2 + τ) * (x * (1 / 2 + σ)) := mul_nonneg (by linarith) (mul_nonneg hx.le (by linarith))
    push_cast at h ⊢
    have h3 : (1 / 2 + τ) * (x * (1 / 2 + σ)) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rw [h4]; ring
    · exfalso; have : 0 < x * (1 / 2 + σ) := mul_pos hx (by linarith); linarith
  have key := raySec_chain (F_tc_s4 x σ τ) (F_tc_t2 x σ τ) (F_tc_invHu x σ τ) (F_tc_e1 x σ τ)
    (F_tc_Jd1 x σ τ) hie hs hs0
  have hl : F_tc_RS4 x σ τ = raySec (F_tc_s4 x σ τ) (F_tc_t2 x σ τ) (1 / F_tc_invHu x σ τ)
      (F_tc_e1 x σ τ) (F_tc_Jd1 x σ τ) := key
  rw [hl, c_invHu hd, one_div_one_div, hs4, c_Jd1 hd]
  have h2 : F_tc_t2 x σ τ = 2 * tOf τ := by
    show (((2 : ℚ) : ℝ)) * (1 / 2 + τ) = _
    unfold tOf; push_cast; ring
  have h3 : F_tc_e1 x σ τ = -(J (bOf x σ - dOf x σ)) := by
    show ((-1 : ℚ) : ℝ) * F_tc_Ju x σ τ = _
    rw [c_Ju hd]; push_cast; ring
  rw [h2, h3]

theorem c_Sv (hd : Dom x σ τ) :
    F_tc_Sv x σ τ = Scalar.etaSlope ((H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2) := by
  show Sfun (((((1 : ℚ) / 5) : ℚ) : ℝ) * ((((5 : ℚ) : ℚ) : ℝ) * F_tc_eps x σ τ)) = _
  rw [c_eps hd, (eta_values (E_pos hd) (E_lt_one hd)).1]
  congr 1
  push_cast
  ring

theorem c_Kv (hd : Dom x σ τ) :
    F_tc_Kv x σ τ = Scalar.etaCurvature ((H (bOf x σ - dOf x σ) + H (bOf x σ)) / 2) := by
  show Kfun (((((1 : ℚ) / 5) : ℚ) : ℝ) * ((((5 : ℚ) : ℚ) : ℝ) * F_tc_eps x σ τ)) = _
  rw [c_eps hd, (eta_values (E_pos hd) (E_lt_one hd)).2]
  congr 1
  push_cast
  ring

/-- the chain's semantic function is `rayGamma` on the corner domain -/
theorem F_tc_Gam_eq (hd : Dom x σ τ) (hσ : -1 / 2 < σ) :
    F_tc_Gam x σ τ = rayGamma (bOf x σ) (tOf τ) (dOf x σ) := by
  have hG : F_tc_Gam x σ τ =
      F_tc_Ap x σ τ + F_tc_RS1 x σ τ + ((-1 : ℚ) : ℝ) * F_tc_RS2 x σ τ + F_tc_RS3 x σ τ +
        ((-1 : ℚ) : ℝ) * (F_tc_Kv x σ τ * (((((1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Ju x σ τ *
          (((((1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Ju x σ τ)) +
          F_tc_Sv x σ τ * (((((1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_Jd1 x σ τ)) +
        ((((-1 : ℚ) / 2) : ℚ) : ℝ) * F_tc_RS4 x σ τ := rfl
  rw [hG, c_Ap hd, c_RS1 hd hσ, c_RS2 hd hσ, c_RS3 hd hσ, c_RS4 hd hσ, c_Kv hd, c_Sv hd, c_Ju hd,
    c_Jd1 hd]
  unfold rayGamma
  push_cast
  ring

end pieces

/-! ## the Boolean corner checker and its soundness -/

/-- positivity part of the checker: valuation 2 and the 8 × 16 box grid -/
noncomputable def posCheckC : Bool :=
  zeroPrefix D_tc_Gam.P 2 && (decide (2 ≤ D_tc_Gam.n) && posGrid D_tc_Gam.P D_tc_Gam.r D_tc_Gam.n 8 16)

/-- THE corner checker -/
noncomputable def cornerCheck : Bool := ucCheck && (ueCheck && (tcCheck && posCheckC))

theorem corner_nonneg (h : cornerCheck = true) :
    ∀ x σ τ, Dom x σ τ → 0 ≤ F_tc_Gam x σ τ := by
  simp only [cornerCheck, posCheckC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hu, he, ht, hz, hn, hg⟩ := h
  have hG := tchain_sound ht (ucon_sound hu) (ueta_sound he)
  exact pos_of_grid hG hn hz 8 16 (by norm_num) (by norm_num) hg

/-- **Soundness of the corner checker**: its only premise is the Boolean check. -/
theorem cornerCheck_sound (h : cornerCheck = true) : GammaCorner (1 / 20) := by
  have hpos := corner_nonneg h
  intro b t d ht0 ht1 hd0 hdb hb hs
  set x := (1 / 2 - b) + d with hxdef
  have hx : 0 < x := by linarith
  set σ := (d - (1 / 2 - b)) / (2 * x) with hσdef
  set τ := t - 1 / 2 with hτdef
  have h2x : 0 < 2 * x := by linarith
  have hσ1 : -1 / 2 < σ := by
    rw [hσdef, lt_div_iff₀ h2x]; linarith
  have hσ2 : σ ≤ 1 / 2 := by
    rw [hσdef, div_le_iff₀ h2x]; linarith
  have hdom : Dom x σ τ := by
    refine ⟨hx, ?_, ?_, ?_⟩
    · show x ≤ ((1 / 20 : ℚ) : ℝ); push_cast; linarith
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le, hτdef]; constructor <;> linarith
  have hid := F_tc_Gam_eq hdom hσ1
  have hxσ : x * σ = (d - (1 / 2 - b)) / 2 := by
    rw [hσdef]; have := hx.ne'; field_simp
  have hb' : bOf x σ = b := by
    unfold bOf; rw [mul_sub, hxσ, hxdef]; ring
  have hd' : dOf x σ = d := by
    unfold dOf; rw [mul_add, hxσ, hxdef]; ring
  have ht' : tOf τ = t := by unfold tOf; rw [hτdef]; ring
  rw [hb', ht', hd'] at hid
  rw [← hid]
  exact hpos x σ τ hdom

end CKLaneN23.CT

end


