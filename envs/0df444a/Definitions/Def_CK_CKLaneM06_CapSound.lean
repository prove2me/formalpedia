-- Prove2me | Definitions.Def_CK_CKLaneM06_CapSound
-- name    : CK_CKLaneM06_CapSound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:20:23.722013+00:00
-- url     : https://prove2.me/theorems/ec0672db-8705-46dc-8db2-873699928134
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapSound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapSound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapSound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapSound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapSound.lean)

import Definitions.Def_CK_CKLaneM06_CapChecker

-- ===== source module CKLaneM06.CapSound =====
section

/-!
# Lane M06: soundness of the cap box checker

`check_sound : check B S w = true → CapOn B S` — the only hypotheses are the Boolean check and the
law's membership in the box (canonical order, deficit `≤ S`).  No numerical fact is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK CKLaneE.FP

theorem qle {x y : ℚ} (h : x ≤ y) : (x : ℝ) ≤ (y : ℝ) := Rat.cast_le.mpr h

theorem qlt {x y : ℚ} (h : x < y) : (x : ℝ) < (y : ℝ) := Rat.cast_lt.mpr h

theorem H_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) : H x ≤ H y :=
  H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

theorem boxOk_facts {B : CBox} (h : B.boxOk = true) :
    0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ B.a1 ≤ 1 / 2 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 < 1 ∧
      (B.b1 ≤ 1 / 2 ∨ 1 / 2 ≤ B.b0) ∧ ptOk B.a0 = true ∧ ptOk B.a1 = true ∧ ptOk B.b0 = true ∧
      ptOk B.b1 = true ∧ (1 / 2 < B.mq ∨ ptOk B.mq = true) := by
  simpa only [CBox.boxOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc] using h

/-- Real box facts. -/
theorem box_real {B : CBox} (h : B.boxOk = true) :
    (0 : ℝ) < B.a0 ∧ (B.a0 : ℝ) ≤ B.a1 ∧ (B.a1 : ℝ) ≤ 1 / 2 ∧ (0 : ℝ) < B.b0 ∧ (B.b0 : ℝ) ≤ B.b1 ∧
      (B.b1 : ℝ) < 1 := by
  obtain ⟨q1, q2, q3, q4, q5, q6, -⟩ := boxOk_facts h
  refine ⟨by exact_mod_cast q1, qle q2, ?_, by exact_mod_cast q4, qle q5, ?_⟩
  · have := qle q3; push_cast at this; exact this
  · have := qlt q6; push_cast at this; exact this

section Bounds

variable {B : CBox} {a b : ℝ}

/-- Entropy-drop upper bound on the box. -/
theorem drop_le_DHi (hbox : B.boxOk = true) (ha0 : (B.a0 : ℝ) ≤ a) (ha1 : a ≤ B.a1)
    (hb0 : (B.b0 : ℝ) ≤ b) (hb1 : b ≤ B.b1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((B.DHi : ℚ) : ℝ) := by
  obtain ⟨_, _, _, _, _, _, hside, pa0, _, pb0, pb1, pm⟩ := boxOk_facts hbox
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < a := lt_of_lt_of_le A0 ha0
  -- H a ≥ Hlo a0
  have hHa : ((B.HaLo : ℚ) : ℝ) ≤ H a := by
    unfold CBox.HaLo
    exact (H_bounds pa0).1.trans (H_mono A0.le ha0 (ha1.trans A1))
  -- H b ≥ HbLo
  have hHb : ((B.HbLo : ℚ) : ℝ) ≤ H b := by
    unfold CBox.HbLo
    split_ifs with hs
    · have hs' : (B.b1 : ℝ) ≤ 1 / 2 := by have := qle hs; push_cast at this; exact this
      exact (H_bounds pb0).1.trans (H_mono B0.le hb0 (hb1.trans hs'))
    · have hs2 : 1 / 2 ≤ B.b0 := by
        rcases hside with h | h
        · exact absurd h hs
        · exact h
      have hs2' : (1 / 2 : ℝ) ≤ B.b0 := by have := qle hs2; push_cast at this; exact this
      have e1 : H b = H (1 - b) := (H_complement b).symm
      have e2 : H (B.b1 : ℝ) = H (1 - (B.b1 : ℝ)) := (H_complement _).symm
      have hmono : H (1 - (B.b1 : ℝ)) ≤ H (1 - b) :=
        H_mono (by linarith) (by linarith) (by linarith)
      rw [e1]
      exact (H_bounds pb1).1.trans (e2 ▸ hmono)
  -- H m ≤ HmHi
  have hHm : H ((a + b) / 2) ≤ ((B.HmHi : ℚ) : ℝ) := by
    unfold CBox.HmHi
    split_ifs with hm
    · have pmq : ptOk B.mq = true := by
        rcases pm with h | h
        · exact absurd h (not_lt.mpr hm)
        · exact h
      have hm' : ((B.mq : ℚ) : ℝ) ≤ 1 / 2 := by have := qle hm; push_cast at this; exact this
      have hmq : ((B.mq : ℚ) : ℝ) = ((B.a1 : ℝ) + B.b1) / 2 := by
        unfold CBox.mq; push_cast; ring
      have hle : (a + b) / 2 ≤ ((B.mq : ℚ) : ℝ) := by rw [hmq]; linarith
      exact (H_mono (by linarith) hle hm').trans (H_bounds pmq).2
    · push_cast
      exact H_le_one _
  have hD : ((B.DHi : ℚ) : ℝ) = ((B.HmHi : ℚ) : ℝ) - (((B.HaLo : ℚ) : ℝ) + ((B.HbLo : ℚ) : ℝ)) / 2 := by
    unfold CBox.DHi; push_cast; ring
  rw [hD]
  linarith

theorem dLo_facts (ha1 : a ≤ B.a1) (hb0 : (B.b0 : ℝ) ≤ b) (hab : a < b) :
    (0 : ℝ) ≤ ((B.dLo : ℚ) : ℝ) ∧ ((B.dLo : ℚ) : ℝ) ≤ b - a := by
  unfold CBox.dLo
  split_ifs with h
  · have h' : (B.a1 : ℝ) < B.b0 := qlt h
    push_cast
    constructor <;> linarith
  · push_cast
    constructor <;> linarith

theorem K_bound (hbox : B.boxOk = true) (hK : 0 ≤ B.K) (ha0 : (B.a0 : ℝ) ≤ a) (ha1 : a ≤ B.a1)
    (hb0 : (B.b0 : ℝ) ≤ b) (hb1 : b ≤ B.b1) (hab : a < b) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((B.K : ℚ) : ℝ) * (b - a) ^ 2 := by
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < a := lt_of_lt_of_le A0 ha0
  have hDHi := drop_le_DHi hbox ha0 ha1 hb0 hb1
  obtain ⟨hd0, hd⟩ := dLo_facts ha1 hb0 hab
  unfold CBox.K
  unfold CBox.K at hK
  split_ifs with hk
  · rw [if_pos hk] at hK
    have hK' : (0 : ℝ) ≤ ((B.K1 : ℚ) : ℝ) := by exact_mod_cast hK
    have hdpos : (0 : ℝ) < ((B.dLo : ℚ) : ℝ) := by exact_mod_cast hk.1
    have hK1 : ((B.K1 : ℚ) : ℝ) = ((B.DHi : ℚ) : ℝ) / (((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ)) := by
      unfold CBox.K1; push_cast; ring
    have heq : ((B.DHi : ℚ) : ℝ) = ((B.K1 : ℚ) : ℝ) * (((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ)) := by
      rw [hK1]; field_simp
    have hsq : ((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ) ≤ (b - a) ^ 2 := by nlinarith
    calc H ((a + b) / 2) - (H a + H b) / 2 ≤ ((B.DHi : ℚ) : ℝ) := hDHi
      _ = ((B.K1 : ℚ) : ℝ) * (((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ)) := heq
      _ ≤ ((B.K1 : ℚ) : ℝ) * (b - a) ^ 2 := mul_le_mul_of_nonneg_left hsq hK'
  · have hL := log_two_mem
    have hLq : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := LqLo_pos
    have cK6 : ((B.K6 : ℚ) : ℝ) =
        ((1 + ((B.rhoH : ℚ) : ℝ) ^ 2 / 6 + 2 / 5 * ((B.rhoH : ℚ) : ℝ) ^ 4) / ((B.mL : ℚ) : ℝ) +
          (1 + ((B.kapH : ℚ) : ℝ) ^ 2 / 6 + 2 / 5 * ((B.kapH : ℚ) : ℝ) ^ 4) / (1 - ((B.mH : ℚ) : ℝ))) /
          (8 * ((LqLo : ℚ) : ℝ)) := by
      unfold CBox.K6; push_cast; ring
    have cRho : ((B.rhoH : ℚ) : ℝ) = ((B.b1 : ℝ) - B.a0) / ((B.a0 : ℝ) + B.b0) := by
      unfold CBox.rhoH CBox.dHi; push_cast; ring
    have cKap : ((B.kapH : ℚ) : ℝ) = ((B.b1 : ℝ) - B.a0) / (2 - (B.a1 : ℝ) - B.b1) := by
      unfold CBox.kapH CBox.dHi; push_cast; ring
    have cmL : ((B.mL : ℚ) : ℝ) = ((B.a0 : ℝ) + B.b0) / 2 := by unfold CBox.mL; push_cast; ring
    have cmH : ((B.mH : ℚ) : ℝ) = ((B.a1 : ℝ) + B.b1) / 2 := by unfold CBox.mH; push_cast; ring
    rw [cK6]
    apply K6_bound hapos hab (by linarith)
    · rw [cRho]
      exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
    · rw [cKap]
      exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
    · rw [cmL]; linarith
    · rw [cmL]; linarith
    · rw [cmH]; linarith
    · rw [cmH]; linarith
    · exact hLq
    · exact hL.1

theorem W_bound (hbox : B.boxOk = true) (ha0 : (B.a0 : ℝ) ≤ a) (ha1 : a ≤ B.a1)
    (hb0 : (B.b0 : ℝ) ≤ b) (hb1 : b ≤ B.b1) (hab : a < b) :
    4 * (H ((a + b) / 2) - (H a + H b) / 2) + (b - a) ^ 2 * ((B.W : ℚ) : ℝ) ≤ interiorCost a b := by
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < a := lt_of_lt_of_le A0 ha0
  obtain ⟨hd0, hd⟩ := dLo_facts ha1 hb0 hab
  have hL := log_two_mem
  have cW : ((B.W : ℚ) : ℝ) =
      ((((B.rhoL : ℚ) : ℝ) ^ 2 + 4 / 5 * ((B.rhoL : ℚ) : ℝ) ^ 4) / ((B.mH : ℚ) : ℝ) +
        (((B.kapL : ℚ) : ℝ) ^ 2 + 4 / 5 * ((B.kapL : ℚ) : ℝ) ^ 4) / (1 - ((B.mL : ℚ) : ℝ))) /
        (12 * ((LqHi : ℚ) : ℝ)) := by
    unfold CBox.W; push_cast; ring
  have cRho : ((B.rhoL : ℚ) : ℝ) = ((B.dLo : ℚ) : ℝ) / ((B.a1 : ℝ) + B.b1) := by
    unfold CBox.rhoL; push_cast; ring
  have cKap : ((B.kapL : ℚ) : ℝ) = ((B.dLo : ℚ) : ℝ) / (2 - (B.a0 : ℝ) - B.b0) := by
    unfold CBox.kapL; push_cast; ring
  have cmL : ((B.mL : ℚ) : ℝ) = ((B.a0 : ℝ) + B.b0) / 2 := by unfold CBox.mL; push_cast; ring
  have cmH : ((B.mH : ℚ) : ℝ) = ((B.a1 : ℝ) + B.b1) / 2 := by unfold CBox.mH; push_cast; ring
  rw [cW]
  apply W6_bound hapos hab (by linarith)
  · rw [cRho]; exact div_nonneg hd0 (by linarith)
  · rw [cRho]; exact div_le_div₀ (by linarith) hd (by linarith) (by linarith)
  · rw [cKap]; exact div_nonneg hd0 (by linarith)
  · rw [cKap]; exact div_le_div₀ (by linarith) hd (by linarith) (by linarith)
  · rw [cmH]; linarith
  · rw [cmL]; linarith
  · rw [cmL]; linarith
  · exact hL.2

end Bounds

section Slopes

variable {ι : Type*} [Fintype ι]

/-- Log enclosures of the four plane logarithms from the checked corner points. -/
theorem plane_logs {B : CBox} (hbox : B.boxOk = true) {a b : ℝ} (ha0 : (B.a0 : ℝ) ≤ a)
    (ha1 : a ≤ B.a1) (hb0 : (B.b0 : ℝ) ≤ b) (hb1 : b ≤ B.b1) :
    ((B.m11l : ℚ) : ℝ) ≤ -Real.log a ∧ -Real.log a ≤ ((B.m11h : ℚ) : ℝ) ∧
      ((B.m12l : ℚ) : ℝ) ≤ -Real.log b ∧ -Real.log b ≤ ((B.m12h : ℚ) : ℝ) ∧
      ((B.m21l : ℚ) : ℝ) ≤ -Real.log (1 - a) ∧ -Real.log (1 - a) ≤ ((B.m21h : ℚ) : ℝ) ∧
      ((B.m22l : ℚ) : ℝ) ≤ -Real.log (1 - b) ∧ -Real.log (1 - b) ≤ ((B.m22h : ℚ) : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, pa0, pa1, pb0, pb1, _⟩ := boxOk_facts hbox
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < a := lt_of_lt_of_le A0 ha0
  have hbpos : 0 < b := lt_of_lt_of_le B0 hb0
  obtain ⟨la0, ua0, la0', ua0'⟩ := ptOk_sound pa0
  obtain ⟨la1, ua1, la1', ua1'⟩ := ptOk_sound pa1
  obtain ⟨lb0, ub0, lb0', ub0'⟩ := ptOk_sound pb0
  obtain ⟨lb1, ub1, lb1', ub1'⟩ := ptOk_sound pb1
  have g1 : Real.log a ≤ Real.log (B.a1 : ℝ) := Real.log_le_log hapos ha1
  have g2 : Real.log (B.a0 : ℝ) ≤ Real.log a := Real.log_le_log A0 ha0
  have g3 : Real.log b ≤ Real.log (B.b1 : ℝ) := Real.log_le_log hbpos hb1
  have g4 : Real.log (B.b0 : ℝ) ≤ Real.log b := Real.log_le_log B0 hb0
  have g5 : Real.log (1 - a) ≤ Real.log (1 - (B.a0 : ℝ)) := Real.log_le_log (by linarith) (by linarith)
  have g6 : Real.log (1 - (B.a1 : ℝ)) ≤ Real.log (1 - a) := Real.log_le_log (by linarith) (by linarith)
  have g7 : Real.log (1 - b) ≤ Real.log (1 - (B.b0 : ℝ)) := Real.log_le_log (by linarith) (by linarith)
  have g8 : Real.log (1 - (B.b1 : ℝ)) ≤ Real.log (1 - b) := Real.log_le_log (by linarith) (by linarith)
  simp only [CBox.m11l, CBox.m11h, CBox.m12l, CBox.m12h, CBox.m21l, CBox.m21h, CBox.m22l, CBox.m22h,
    Rat.cast_neg]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The certified plane coefficient. -/
theorem plane_coeffs {B : CBox} (hbox : B.boxOk = true) (hp : B.planeOk = true) {a b : ℝ}
    (ha0 : (B.a0 : ℝ) ≤ a) (ha1 : a ≤ B.a1) (hb0 : (B.b0 : ℝ) ≤ b) (hb1 : b ≤ B.b1) :
    0 < pDet a b ∧ 0 < ((B.planeL : ℚ) : ℝ) ∧ ((B.planeL : ℚ) : ℝ) ≤ pA0 a b ∧
      ((B.planeL : ℚ) : ℝ) ≤ pD0 a b := by
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  simp only [CBox.planeOk, decide_eq_true_eq] at hp
  obtain ⟨p11, p12, p21, p22, pdet, pnA, pnD⟩ := hp
  obtain ⟨l11, h11, l12, h12, l21, h21, l22, h22⟩ := plane_logs hbox ha0 ha1 hb0 hb1
  have cnA : ((B.nAL : ℚ) : ℝ) = ((B.m22l : ℚ) : ℝ) / (2 * (B.a1 : ℝ) * B.b1) -
      ((B.m12h : ℚ) : ℝ) / (2 * (1 - (B.a1 : ℝ)) * (1 - B.b1)) := by
    unfold CBox.nAL; push_cast; ring
  have cnD : ((B.nDL : ℚ) : ℝ) = ((B.m11l : ℚ) : ℝ) / (2 * (1 - (B.a0 : ℝ)) * (1 - B.b0)) -
      ((B.m21h : ℚ) : ℝ) / (2 * (B.a0 : ℝ) * B.b0) := by
    unfold CBox.nDL; push_cast; ring
  have cdL : ((B.detL : ℚ) : ℝ) = ((B.m11l : ℚ) : ℝ) * ((B.m22l : ℚ) : ℝ) -
      ((B.m12h : ℚ) : ℝ) * ((B.m21h : ℚ) : ℝ) := by
    unfold CBox.detL; push_cast; ring
  have cdH : ((B.detH : ℚ) : ℝ) = ((B.m11h : ℚ) : ℝ) * ((B.m22h : ℚ) : ℝ) -
      ((B.m12l : ℚ) : ℝ) * ((B.m21l : ℚ) : ℝ) := by
    unfold CBox.detH; push_cast; ring
  have hp11 : (0 : ℝ) ≤ ((B.m11l : ℚ) : ℝ) := by exact_mod_cast p11
  have hp12 : (0 : ℝ) ≤ ((B.m12l : ℚ) : ℝ) := by exact_mod_cast p12
  have hp21 : (0 : ℝ) ≤ ((B.m21l : ℚ) : ℝ) := by exact_mod_cast p21
  have hp22 : (0 : ℝ) ≤ ((B.m22l : ℚ) : ℝ) := by exact_mod_cast p22
  have hdL : (0 : ℝ) < ((B.detL : ℚ) : ℝ) := by exact_mod_cast pdet
  have hnA : (0 : ℝ) < ((B.nAL : ℚ) : ℝ) := by exact_mod_cast pnA
  have hnD : (0 : ℝ) < ((B.nDL : ℚ) : ℝ) := by exact_mod_cast pnD
  rw [cdL] at hdL
  rw [cnA] at hnA
  rw [cnD] at hnD
  obtain ⟨hdet, hA, hD⟩ := plane_box A0 ha0 ha1 B0 hb0 hb1 (by linarith) B1
    l11 h11 l12 h12 l21 h21 l22 h22 hp11 hp12 hp21 hp22 hdL hnA hnD
  rw [← cnA, ← cdH] at hA
  rw [← cnD, ← cdH] at hD
  -- detH > 0
  have hdH : (0 : ℝ) < ((B.detH : ℚ) : ℝ) := by
    rw [cdH]
    have e1 : ((B.m11l : ℚ) : ℝ) * ((B.m22l : ℚ) : ℝ) ≤ ((B.m11h : ℚ) : ℝ) * ((B.m22h : ℚ) : ℝ) :=
      mul_le_mul (l11.trans h11) (l22.trans h22) hp22 ((hp11.trans l11).trans h11)
    have e2 : ((B.m12l : ℚ) : ℝ) * ((B.m21l : ℚ) : ℝ) ≤ ((B.m12h : ℚ) : ℝ) * ((B.m21h : ℚ) : ℝ) :=
      mul_le_mul (l12.trans h12) (l21.trans h21) hp21 ((hp12.trans l12).trans h12)
    linarith
  -- the certified coefficient
  have hl_le : ((B.planeL : ℚ) : ℝ) ≤ pA0 a b ∧ ((B.planeL : ℚ) : ℝ) ≤ pD0 a b := by
    unfold CBox.planeL
    split_ifs with hc
    · have hc' : ((B.nAL : ℚ) : ℝ) ≤ ((B.nDL : ℚ) : ℝ) := qle hc
      push_cast
      exact ⟨hA, (div_le_div_of_nonneg_right hc' hdH.le).trans hD⟩
    · have hc' : ((B.nDL : ℚ) : ℝ) ≤ ((B.nAL : ℚ) : ℝ) := qle (le_of_lt (lt_of_not_ge hc))
      push_cast
      exact ⟨(div_le_div_of_nonneg_right hc' hdH.le).trans hA, hD⟩
  have hl_pos : (0 : ℝ) < ((B.planeL : ℚ) : ℝ) := by
    have hnA' : (0 : ℝ) < ((B.nAL : ℚ) : ℝ) := by exact_mod_cast pnA
    have hnD' : (0 : ℝ) < ((B.nDL : ℚ) : ℝ) := by exact_mod_cast pnD
    unfold CBox.planeL
    split_ifs
    · push_cast; exact div_pos hnA' hdH
    · push_cast; exact div_pos hnD' hdH
  exact ⟨hdet, hl_pos, hl_le.1, hl_le.2⟩

/-- The certified plane slope. -/
theorem plane_slope_box {B : CBox} (hbox : B.boxOk = true) (hp : B.planeOk = true)
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (ha0 : (B.a0 : ℝ) ≤ μ.a) (ha1 : μ.a ≤ B.a1)
    (hb0 : (B.b0 : ℝ) ≤ μ.b) (hb1 : μ.b ≤ B.b1) :
    interiorCost μ.a μ.b + 2 * ((B.planeL : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * μ.meanDeficit ≤ μ.cost := by
  obtain ⟨hdet, hl_pos, hA, hD⟩ := plane_coeffs hbox hp ha0 ha1 hb0 hb1
  exact slope_plane μ hab hl_pos hA hD hdet.ne'

/-- The certified kappa log-sum slope. -/
theorem kappa_slope_box {B : CBox} (hbox : B.boxOk = true) {κ : ℚ} (hk : B.kapOk κ = true)
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (ha0 : (B.a0 : ℝ) ≤ μ.a) (ha1 : μ.a ≤ B.a1)
    (hb0 : (B.b0 : ℝ) ≤ μ.b) (hb1 : μ.b ≤ B.b1) :
    interiorCost μ.a μ.b + (κ : ℝ) * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) * μ.meanDeficit ≤
      μ.cost := by
  obtain ⟨_, _, _, _, _, _, _, pa0, pa1, pb0, pb1, _⟩ := boxOk_facts hbox
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < μ.a := lt_of_lt_of_le A0 ha0
  have hbpos : 0 < μ.b := lt_of_lt_of_le B0 hb0
  have ha1' : μ.a < 1 := by linarith
  have hb1' : μ.b < 1 := by linarith
  simp only [CBox.kapOk, decide_eq_true_eq] at hk
  obtain ⟨k0, k2, c1, c2, c3, c4⟩ := hk
  have hk0 : (0 : ℝ) ≤ κ := by exact_mod_cast k0
  have hk2 : (κ : ℝ) ≤ 2 := by have := qle k2; push_cast at this; exact this
  obtain ⟨la0, ua0, la0', ua0'⟩ := ptOk_sound pa0
  obtain ⟨la1, ua1, la1', ua1'⟩ := ptOk_sound pa1
  obtain ⟨lb0, ub0, lb0', ub0'⟩ := ptOk_sound pb0
  obtain ⟨lb1, ub1, lb1', ub1'⟩ := ptOk_sound pb1
  -- x/(1-x) increasing, (1-x)/x decreasing
  have inc {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : x / (1 - x) ≤ y / (1 - y) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have dec {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : (1 - y) / y ≤ (1 - x) / x := by
    rw [div_le_div_iff₀ (by linarith) hx]; nlinarith
  have C1 : (κ : ℝ) * -Real.log (1 - μ.a) ≤ μ.a / (1 - μ.a) := by
    have h := qle c1
    push_cast at h
    have g : -Real.log (1 - μ.a) ≤ -Real.log (1 - (B.a1 : ℝ)) :=
      neg_le_neg (Real.log_le_log (by linarith) (by linarith))
    have g' : -Real.log (1 - (B.a1 : ℝ)) ≤ -((l1Lo B.a1 : ℚ) : ℝ) := by linarith
    calc (κ : ℝ) * -Real.log (1 - μ.a) ≤ (κ : ℝ) * -((l1Lo B.a1 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left (g.trans g') hk0
      _ ≤ (B.a0 : ℝ) / (1 - B.a0) := h
      _ ≤ μ.a / (1 - μ.a) := inc A0.le ha0 ha1'
  have C2 : (κ : ℝ) * -Real.log μ.a ≤ (1 - μ.a) / μ.a := by
    have h := qle c2
    push_cast at h
    have g : -Real.log μ.a ≤ -Real.log (B.a0 : ℝ) := neg_le_neg (Real.log_le_log A0 ha0)
    have g' : -Real.log (B.a0 : ℝ) ≤ -((lLo B.a0 : ℚ) : ℝ) := by linarith
    calc (κ : ℝ) * -Real.log μ.a ≤ (κ : ℝ) * -((lLo B.a0 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left (g.trans g') hk0
      _ ≤ (1 - (B.a1 : ℝ)) / B.a1 := h
      _ ≤ (1 - μ.a) / μ.a := dec hapos ha1
  have C3 : (κ : ℝ) * -Real.log (1 - μ.b) ≤ μ.b / (1 - μ.b) := by
    have h := qle c3
    push_cast at h
    have g : -Real.log (1 - μ.b) ≤ -Real.log (1 - (B.b1 : ℝ)) :=
      neg_le_neg (Real.log_le_log (by linarith) (by linarith))
    have g' : -Real.log (1 - (B.b1 : ℝ)) ≤ -((l1Lo B.b1 : ℚ) : ℝ) := by linarith
    calc (κ : ℝ) * -Real.log (1 - μ.b) ≤ (κ : ℝ) * -((l1Lo B.b1 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left (g.trans g') hk0
      _ ≤ (B.b0 : ℝ) / (1 - B.b0) := h
      _ ≤ μ.b / (1 - μ.b) := inc B0.le hb0 hb1'
  have C4 : (κ : ℝ) * -Real.log μ.b ≤ (1 - μ.b) / μ.b := by
    have h := qle c4
    push_cast at h
    have g : -Real.log μ.b ≤ -Real.log (B.b0 : ℝ) := neg_le_neg (Real.log_le_log B0 hb0)
    have g' : -Real.log (B.b0 : ℝ) ≤ -((lLo B.b0 : ℚ) : ℝ) := by linarith
    calc (κ : ℝ) * -Real.log μ.b ≤ (κ : ℝ) * -((lLo B.b0 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left (g.trans g') hk0
      _ ≤ (1 - (B.b1 : ℝ)) / B.b1 := h
      _ ≤ (1 - μ.b) / μ.b := dec hbpos hb1
  exact slope_kappa μ hab hk0 hk2 C1 C2 C3 C4

end Slopes

set_option maxHeartbeats 1000000 in
/-- **Soundness of the cap box checker.** -/
theorem check_sound {B : CBox} {S : ℚ} {w : CWit} (hc : check B S w = true) : CapOn B S := by
  intro k μ hab hsum ha0 ha1 hb0 hb1 hs
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  obtain ⟨hbox, hS0, hSI, hvS, hvI, hslope, hK0, hfin⟩ := hc
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < μ.a := lt_of_lt_of_le A0 ha0
  have hS0R : (0 : ℝ) ≤ S := by exact_mod_cast hS0
  -- scalar quantities
  set Δ := μ.entropyDrop with hΔ
  set s := μ.meanDeficit with hsd
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  have hsS : s ≤ (S : ℝ) := by rw [hsd, meanDeficit_eq]; exact hs
  have hDHi := drop_le_DHi hbox ha0 ha1 hb0 hb1
  rw [← hΔdef] at hDHi
  have hSIR : (S : ℝ) + ((B.DHi : ℚ) : ℝ) < 1 := by have := qlt hSI; push_cast at this; exact this
  have hI : Δ + (S : ℝ) < 1 := by linarith
  -- increment bound (trapezoid + anchors)
  have htrap := CKLaneE.P_trapezoid hS0R (le_add_of_nonneg_left hΔ0) hI
  have hPS := anchorOk_sound hvS hS0R le_rfl
  have hPI := anchorOk_sound hvI (x := Δ + (S : ℝ)) (by linarith) (by push_cast; linarith)
  have hpbar : ((pbar w : ℚ) : ℝ) = (((P1up w.vS : ℚ) : ℝ) + ((P1up w.vI : ℚ) : ℝ)) / 2 := by
    unfold pbar; push_cast; ring
  have hinc : Scalar.P (Δ + S) - Scalar.P S ≤ Δ * ((pbar w : ℚ) : ℝ) := by
    rw [hpbar]
    have h1 : Δ + (S : ℝ) - S = Δ := by ring
    rw [h1] at htrap
    have := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith
  -- K, W bounds
  have hKb := K_bound hbox hK0 ha0 ha1 hb0 hb1 hab
  rw [← hΔdef] at hKb
  have hWb := W_bound hbox ha0 ha1 hb0 hb1 hab
  rw [← hΔdef] at hWb
  have hK0R : (0 : ℝ) ≤ ((B.K : ℚ) : ℝ) := by exact_mod_cast hK0
  set d2 := (μ.b - μ.a) ^ 2 with hd2
  have hd20 : 0 ≤ d2 := sq_nonneg _
  -- excess
  have hexc : Δ * (((pbar w : ℚ) : ℝ) - 4) ≤ ((B.K : ℚ) : ℝ) * d2 * ((excess w : ℚ) : ℝ) := by
    unfold excess
    split_ifs with hp
    · have hp' : (0 : ℝ) ≤ ((pbar w : ℚ) : ℝ) - 4 := by
        have := qle hp; push_cast at this; linarith
      push_cast
      exact mul_le_mul_of_nonneg_right hKb hp'
    · have hp' : ((pbar w : ℚ) : ℝ) - 4 < 0 := by
        have := qlt (lt_of_not_ge hp); push_cast at this; linarith
      push_cast
      have := mul_nonpos_of_nonneg_of_nonpos hΔ0 hp'.le
      have := mul_nonneg (mul_nonneg hK0R hd20) (le_refl (0 : ℝ))
      nlinarith
  have hfinR : ((B.K : ℚ) : ℝ) * ((excess w : ℚ) : ℝ) ≤ ((B.W : ℚ) : ℝ) + ((w.lam B : ℚ) : ℝ) * S := by
    have := qle hfin; push_cast at this; exact this
  -- the slope, in both branches: ζ ≥ j + lamAct s with d2 * lam ≤ lamAct
  obtain ⟨lamAct, hslopeAct, hlamAct⟩ : ∃ lamAct : ℝ,
      interiorCost μ.a μ.b + lamAct * s ≤ μ.cost ∧ d2 * ((w.lam B : ℚ) : ℝ) ≤ lamAct := by
    unfold CWit.slopeOk at hslope
    unfold CWit.lam
    split_ifs at hslope ⊢ with hpl
    · refine ⟨2 * ((B.planeL : ℚ) : ℝ) * d2, ?_, ?_⟩
      · exact plane_slope_box hbox hslope μ hab ha0 ha1 hb0 hb1
      · push_cast; linarith
    · refine ⟨(w.kap : ℝ) * d2 / (2 * (μ.b * (1 - μ.a))), ?_, ?_⟩
      · exact kappa_slope_box hbox hslope μ hab ha0 ha1 hb0 hb1
      · simp only [CBox.kapOk, decide_eq_true_eq] at hslope
        have hk0 : (0 : ℝ) ≤ w.kap := by exact_mod_cast hslope.1
        push_cast
        have hbpos : 0 < μ.b := lt_of_lt_of_le B0 hb0
        have hV : 0 < μ.b * (1 - μ.a) := mul_pos hbpos (by linarith)
        have hV1 : 0 < 2 * (B.b1 : ℝ) * (1 - B.a0) := by nlinarith
        have hVle : 2 * (μ.b * (1 - μ.a)) ≤ 2 * (B.b1 : ℝ) * (1 - B.a0) := by nlinarith
        have h1 : (w.kap : ℝ) / (2 * (B.b1 : ℝ) * (1 - B.a0)) ≤ (w.kap : ℝ) / (2 * (μ.b * (1 - μ.a))) :=
          div_le_div_of_nonneg_left hk0 (by positivity) hVle
        calc d2 * ((w.kap : ℝ) / (2 * (B.b1 : ℝ) * (1 - B.a0)))
            ≤ d2 * ((w.kap : ℝ) / (2 * (μ.b * (1 - μ.a)))) := mul_le_mul_of_nonneg_left h1 hd20
          _ = (w.kap : ℝ) * d2 / (2 * (μ.b * (1 - μ.a))) := by ring
  -- the lam used by the checker is nonnegative
  have hlam0 : (0 : ℝ) ≤ ((w.lam B : ℚ) : ℝ) := by
    unfold CWit.slopeOk at hslope
    unfold CWit.lam
    split_ifs at hslope ⊢ with hpl
    · have hl := (plane_coeffs hbox hslope ha0 ha1 hb0 hb1).2.1
      push_cast
      linarith
    · simp only [CBox.kapOk, decide_eq_true_eq] at hslope
      have hk0 : (0 : ℚ) ≤ w.kap := hslope.1
      obtain ⟨q1, q2, q3, q4, q5, -⟩ := boxOk_facts hbox
      have : (0 : ℚ) ≤ w.kap / (2 * B.b1 * (1 - B.a0)) := by
        apply div_nonneg hk0
        exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      exact_mod_cast this
  -- endpoint G(S) ≥ 0
  have hend : 0 ≤ Scalar.gap (interiorCost μ.a μ.b) lamAct Δ S := by
    unfold Scalar.gap
    have e1 : Δ * ((pbar w : ℚ) : ℝ) = 4 * Δ + Δ * (((pbar w : ℚ) : ℝ) - 4) := by ring
    have h2 : d2 * (((B.K : ℚ) : ℝ) * ((excess w : ℚ) : ℝ)) ≤
        d2 * (((B.W : ℚ) : ℝ) + ((w.lam B : ℚ) : ℝ) * S) := mul_le_mul_of_nonneg_left hfinR hd20
    have h3 : d2 * ((w.lam B : ℚ) : ℝ) * S ≤ lamAct * S := mul_le_mul_of_nonneg_right hlamAct hS0R
    have e2 : ((B.K : ℚ) : ℝ) * d2 * ((excess w : ℚ) : ℝ) = d2 * (((B.K : ℚ) : ℝ) * ((excess w : ℚ) : ℝ)) := by
      ring
    have e3 : d2 * (((B.W : ℚ) : ℝ) + ((w.lam B : ℚ) : ℝ) * S) =
        d2 * ((B.W : ℚ) : ℝ) + d2 * ((w.lam B : ℚ) : ℝ) * S := by ring
    have hWb' : 4 * Δ + d2 * ((B.W : ℚ) : ℝ) ≤ interiorCost μ.a μ.b := hWb
    linarith
  exact psi_gap_le_cost_of_endpoint μ hslopeAct hsS hI hend

end CKLaneM06.Cap

end


