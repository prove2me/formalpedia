-- Prove2me | Definitions.Def_CK_CKLaneN4_OLeafKernel
-- name    : CK_CKLaneN4_OLeafKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:52:21.589619+00:00
-- url     : https://prove2.me/theorems/0043ac84-5329-4df6-a061-13b4cac81469
-- title:
--   Courtade–Kumar proof module `CKLaneN4.OLeafKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.OLeafKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.OLeafKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.OLeafKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/OLeafKernel.lean)

import Definitions.Def_CK_CKLaneN4_OLeafKernel_q02

namespace CKLaneN4
open GeneralCK CKLaneD CKLaneD.OCompact
theorem checkL4_sound {p : List ℕ} {w : L4Witness} (h : checkL4 p w = true) :
    OLeafOK (uvtBox p) := by
  intro k μ hab hsum hb ha _ _ _ hin hact
  unfold checkL4 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨himg, hbox⟩, hpa⟩, hpb⟩, hEle⟩, hq25⟩, hd8⟩ := h
  unfold l4BoxOK at hbox
  simp only [decide_eq_true_eq] at hbox
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9⟩ := hbox
  obtain ⟨ha0, ha1, hb0, hb1, _, hE1⟩ := inBox_of_imageCheck himg hin
  obtain ⟨_, _, _, hHa, _, _⟩ := checkPt_bounds hpa
  obtain ⟨_, _, _, hHb, _, _⟩ := checkPt_bounds hpb
  have rB1 : (0 : ℝ) < w.box.alo := by exact_mod_cast hB1
  have rB3 : 2 * (w.box.ahi : ℝ) ≤ 1 := by exact_mod_cast hB3
  have rB4 : 1 ≤ 2 * (w.box.blo : ℝ) := by exact_mod_cast hB4
  have rB6 : (w.box.bhi : ℝ) < 1 := by exact_mod_cast hB6
  have rB7 : (0 : ℝ) ≤ w.box.t0 := by exact_mod_cast hB7
  have rB8 : (w.box.t0 : ℝ) ≤ w.box.t1 := by exact_mod_cast hB8
  -- mean entropy upper bound
  have hHa' : H μ.a ≤ H (w.box.ahi : ℝ) :=
    H_mono_left (by linarith [μ.a_interior.1]) ha1 (by linarith)
  have hHb' : H μ.b ≤ H (w.box.blo : ℝ) := H_anti_right (by linarith) hb0 (by linarith)
  have eE : ((l4EHi w : ℚ) : ℝ) = (EMIN : ℝ) + (w.box.t1 : ℝ) *
      (((Hhi w.box.ahi w.pa : ℚ) : ℝ) / 2 + ((Hhi w.box.blo w.pb : ℚ) : ℝ) / 2 - (EMIN : ℝ)) := by
    unfold l4EHi; push_cast; ring
  have hEup : μ.meanEntropy ≤ ((l4EHi w : ℚ) : ℝ) := by
    rw [eE]
    have ht1 : (0 : ℝ) ≤ w.box.t1 := rB7.trans rB8
    have := mul_le_mul_of_nonneg_left
      (show (H μ.a + H μ.b) / 2 - (EMIN : ℝ) ≤ ((Hhi w.box.ahi w.pa : ℚ) : ℝ) / 2 +
        ((Hhi w.box.blo w.pb : ℚ) : ℝ) / 2 - (EMIN : ℝ) by linarith) ht1
    linarith
  have rEle : ((l4EHi w : ℚ) : ℝ) ≤ 11 / 200 := by
    have := (Rat.cast_le (K := ℝ)).mpr hEle
    push_cast at this
    linarith
  have rq25 : 1 - (w.box.alo : ℝ) - (w.box.blo : ℝ) ≤ 2 / 5 := by
    have := (Rat.cast_le (K := ℝ)).mpr hq25
    push_cast at this
    linarith
  have rd8 : 8 * ((l4EHi w : ℚ) : ℝ) ≤ (w.box.blo : ℝ) - (w.box.ahi : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hd8
    push_cast at this
    linarith
  -- the law's parameters
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hEi : μ.meanEntropy ≤ 11 / 200 := hEup.trans rEle
  have hd : 8 * μ.meanEntropy ≤ μ.b - μ.a := by linarith
  have hq25' : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  have hact' : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy <
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmid]
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  rcases hq0.eq_or_lt with hz | hqpos
  · exfalso
    have h2 : (1 - (1 - μ.a - μ.b)) / 2 = 1 / 2 := by rw [← hz]; norm_num
    rw [h2, phi_eq_psi_half] at hact'
    exact lt_irrefl _ hact'
  by_cases h8 : 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b
  · exact absurd (parent8 _ _ hE hqpos hq25' h8) (not_lt.mpr hact'.le)
  · exact globalEightPsi_law μ hsum hEi hd (lt_of_not_ge h8).le hact.le

/-- A list of label-4 witnesses, all accepted, gives the obligation on every listed leaf. -/
theorem l4_list_sound (L : List (List ℕ × L4Witness))
    (h : (L.all fun x => checkL4 x.1 x.2) = true) : ∀ x ∈ L, OLeafOK (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkL4_sound (h x hx)

end CKLaneN4


