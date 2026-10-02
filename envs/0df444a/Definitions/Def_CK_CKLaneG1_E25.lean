-- Prove2me | Definitions.Def_CK_CKLaneG1_E25
-- name    : CK_CKLaneG1_E25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:49:18.721168+00:00
-- url     : https://prove2.me/theorems/95ba111f-e0a2-461a-b4d3-0ceb015d501b
-- title:
--   Courtade–Kumar proof module `CKLaneG1.E25` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG1.E25` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG1.E25` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG1.E25 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG1/E25.lean)

import Definitions.Def_CK_CKLaneD_FleetBase

-- ===== source module CKLaneG1.E25 =====
section

/-!
# Lane G1: archived (O) leaves whose whole physical image has `E ≤ 1/25`

`eCheckLe p w = true` certifies `InUVT (uvtBox p) a b E → E ≤ 1/25`: such a leaf is entirely inside
the region delegated to `OUTER_OPPOSITE_LOW_ENTROPY.md`.  Witness: rational upper bounds of `2^-u0`
(for `a`) and `2^-v0` (for `y = 1 - b`), certified by exact `Nat` powers, and Lane D logarithm
certificates for the entropy upper bounds at `ahc = min ahi (min (1/10) yhi)` and `yhi`.
-/

namespace CKLaneG1

open GeneralCK CKLaneD

structure EW where
  ahi : ℚ
  yhi : ℚ
  pa : PtCert
  py : PtCert
  deriving Repr, DecidableEq

def EW.ahc (w : EW) : ℚ := min w.ahi (min (1 / 10) w.yhi)

def EW.Ehi (w : EW) (t1 : ℚ) : ℚ :=
  EMIN + t1 * ((Hhi w.ahc w.pa + Hhi w.yhi w.py) / 2 - EMIN)

def eCheckLe (p : List ℕ) (w : EW) : Bool :=
  decide (0 ≤ (uvtBox p).t1) && pow2UpperOK w.ahi (uvtBox p).u0 && pow2UpperOK w.yhi (uvtBox p).v0 &&
    decide (w.yhi ≤ 1 / 2) && checkPt w.ahc w.pa && checkPt w.yhi w.py &&
    decide (w.Ehi (uvtBox p).t1 ≤ 1 / 25)

theorem eCheckLe_sound {p : List ℕ} {w : EW} (h : eCheckLe p w = true) {a b E : ℝ}
    (hin : InUVT (uvtBox p) a b E) : E ≤ 1 / 25 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hin
  unfold eCheckLe at h
  repeat rw [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨ht1, hah⟩, hyh⟩, hy2⟩, hpa⟩, hpy⟩, hE⟩ := h
  have hah' := pow2UpperOK_sound hah
  have hyh' := pow2UpperOK_sound hyh
  have hapos : 0 < a := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) h1
  have hA1 : a ≤ (w.ahc : ℝ) := by
    unfold EW.ahc
    push_cast
    refine le_min (h2.trans hah') (le_min (by linarith only [h5]) ?_)
    linarith only [h6, h3, hyh']
  have hY1 : 1 - b ≤ (w.yhi : ℝ) := by linarith only [h3, hyh']
  have hahc_le : (w.ahc : ℝ) ≤ 1 / 10 := by
    unfold EW.ahc
    push_cast
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hyhi_le : (w.yhi : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le.mpr (of_decide_eq_true hy2) : ((w.yhi : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ))
    push_cast at h
    exact h
  have hmono := H_strictMonoOn.monotoneOn
  have hHa : H a ≤ H (w.ahc : ℝ) :=
    hmono ⟨hapos.le, by linarith only [hA1, hahc_le]⟩ ⟨by linarith only [hA1, hapos], by linarith only [hahc_le]⟩ hA1
  have hHb : H b ≤ H (w.yhi : ℝ) := by
    rw [← H_complement b]
    exact hmono ⟨by linarith only [h6, hapos], by linarith only [hY1, hyhi_le]⟩
      ⟨by linarith only [hY1, h6, hapos], hyhi_le⟩ hY1
  have hPa := (checkPt_bounds hpa).2.2.2.1
  have hPy := (checkPt_bounds hpy).2.2.2.1
  have ht1' : (0 : ℝ) ≤ ((uvtBox p).t1 : ℝ) := by exact_mod_cast of_decide_eq_true ht1
  have hC : (H a + H b) / 2 - (EMIN : ℝ) ≤
      ((Hhi w.ahc w.pa : ℚ) + (Hhi w.yhi w.py : ℚ)) / 2 - (EMIN : ℝ) := by
    linarith only [hHa, hHb, hPa, hPy]
  have hmul := mul_le_mul_of_nonneg_left hC ht1'
  have hE' := (Rat.cast_le.mpr (of_decide_eq_true hE) :
    ((w.Ehi (uvtBox p).t1 : ℚ) : ℝ) ≤ ((1 / 25 : ℚ) : ℝ))
  unfold EW.Ehi at hE'
  push_cast at hE'
  linarith only [h8, hmul, hE']

theorem leLeaves_of_list (L : List (List ℕ × EW)) (hok : (L.all fun x => eCheckLe x.1 x.2) = true) :
    ∀ x ∈ L, ∀ a b E : ℝ, InUVT (uvtBox x.1) a b E → E ≤ 1 / 25 := by
  intro x hx a b E hin
  rw [List.all_eq_true] at hok
  exact eCheckLe_sound (hok x hx) hin

end CKLaneG1

#check @CKLaneG1.eCheckLe_sound
#print axioms CKLaneG1.eCheckLe_sound

end


