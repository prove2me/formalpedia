-- Prove2me | Definitions.Def_CK_CKLaneN1_R3Excl
-- name    : CK_CKLaneN1_R3Excl
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:03:28.678931+00:00
-- url     : https://prove2.me/theorems/199639e1-c75d-4c19-b360-125f9bacd77e
-- title:
--   Courtade–Kumar proof module `CKLaneN1.R3Excl` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.R3Excl` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.R3Excl` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.R3Excl (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/R3Excl.lean)

import Definitions.Def_CK_CKLaneN1_R3Leaf
import Definitions.Def_CK_CKLaneN1_EdgeSound

-- ===== source module CKLaneN1.R3Excl =====
section

/-!
# Lane N1 — CE-stat row 3: domain exclusions

* `a_lower`: the retained cutoff `a + c > 1/10000` together with `A ≤ 1/20` forces `a ≥ 2^-17`
  (tangent line of the concave `H` at `c_lo = 1/10000 − 2^-17`).
* `y_upper`: on an octave `a ≤ a₁`, `A ≤ 1/20` forces `y = c − a ≤ Y` whenever the rational side
  conditions `yupOK a₁ Y` hold (tangent line of `H` at `p = a₁ + Y`).
-/

set_option autoImplicit false

namespace CKLaneN1.R3

open GeneralCK CKLaneN1 CKLaneE.FP

/-- the tangent line of the concave `H` at `p` lies above `H` on `(0,1)` -/
theorem H_tangent {p c : ℝ} (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c) (hc1 : c < 1) :
    H c ≤ H p + J p * (c - p) := by
  rcases le_total p c with h | h
  · have := CKLaneN1.Edge.H_sub_le_J hp h hc1
    linarith
  · have := CKLaneN1.Edge.H_sub_ge_J hc h hp1
    linarith

/-! ## (ii) the octave height -/

/-- rational side conditions of the height exclusion on an octave `a ≤ a₁` -/
def yupOK (a1 Y : ℚ) : Bool :=
  decide (0 < a1) && decide (0 < Y) && ptOk a1 && ptOk (a1 + Y) && decide (a1 + Y < 1 / 2) &&
    decide (lamHi (a1 + Y) / LqLo ≤ 20) && decide (Hhi a1 + Hhi (a1 + Y) < 20 * Y)

theorem y_upper {a1 Y : ℚ} (hok : yupOK a1 Y = true) {a b y : ℝ} (ha : 0 < a)
    (ha1 : a ≤ (a1 : ℝ)) (hy : 0 < y) (hab : a < b) (hby : b ≤ a + y) (hc : a + y < 1 / 2)
    (hA : y ≤ (H a + H b) / 20) : y ≤ (Y : ℝ) := by
  simp only [yupOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨_h0, _hY0⟩, hpa⟩, hpp⟩, hp2⟩, hJ⟩, hH⟩ := hok
  by_contra hn
  push Not at hn
  have hp2R : ((a1 + Y : ℚ) : ℝ) < 1 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hp2
    push_cast at this ⊢
    linarith
  have hpR : ((a1 + Y : ℚ) : ℝ) = (a1 : ℝ) + (Y : ℝ) := by push_cast; ring
  have hp0 : (0 : ℝ) < ((a1 + Y : ℚ) : ℝ) := by
    have := (ptOk_pos hpp).1
    exact_mod_cast this
  have ha12 : (a1 : ℝ) ≤ 1 / 2 := by
    have hY : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast _hY0
    linarith
  -- entropy bounds
  have hHa : H a ≤ ((Hhi a1 : ℚ) : ℝ) := (CKLaneN1.Edge.H_mono ha.le ha1 ha12).trans (H_bounds hpa).2
  have hHb : H b ≤ H (a + y) := CKLaneN1.Edge.H_mono (ha.trans hab).le hby hc.le
  have hHc := H_tangent hp0 (by linarith) (by linarith : 0 < a + y) (by linarith : a + y < 1)
  have hHp : H ((a1 + Y : ℚ) : ℝ) ≤ ((Hhi (a1 + Y) : ℚ) : ℝ) := (H_bounds hpp).2
  have hJp : J ((a1 + Y : ℚ) : ℝ) ≤ ((lamHi (a1 + Y) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
    CKLaneN1.Capital.J_le hpp hp2R.le
  have hJ0 : 0 ≤ J ((a1 + Y : ℚ) : ℝ) := (J_pos hp0 hp2R).le
  have hJR : ((lamHi (a1 + Y) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) ≤ 20 := by
    have := (Rat.cast_le (K := ℝ)).mpr hJ
    push_cast at this
    linarith
  have hHR : ((Hhi a1 : ℚ) : ℝ) + ((Hhi (a1 + Y) : ℚ) : ℝ) < 20 * (Y : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hH
    push_cast at this
    linarith
  set Jp := J ((a1 + Y : ℚ) : ℝ) with hJpdef
  set Jh := ((lamHi (a1 + Y) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) with hJhdef
  have hd : a + y - ((a1 + Y : ℚ) : ℝ) ≤ y - Y := by rw [hpR]; linarith
  have m1 : Jp * (a + y - ((a1 + Y : ℚ) : ℝ)) ≤ Jp * (y - Y) := mul_le_mul_of_nonneg_left hd hJ0
  have m2 : Jp * (y - Y) ≤ Jh * (y - Y) := mul_le_mul_of_nonneg_right hJp (by linarith)
  have m3 : 0 ≤ (20 - Jh) * (y - Y) := mul_nonneg (by linarith) (by linarith)
  nlinarith [m1, m2, m3, hHa, hHb, hHc, hHp, hHR, hA]

/-! ## (i) the lower end of `a` -/

/-- `a_lo = 2^-17` -/
def alo : ℚ := 1 / 131072
/-- `c_lo = 1/10000 − 2^-17` -/
def clo : ℚ := 1 / 10000 - 1 / 131072

def aloOK : Bool :=
  ptOk alo && ptOk clo && decide (clo < 1 / 2) && decide (lamHi clo / LqLo ≤ 20) &&
    decide (Hhi alo + Hhi clo < 20 * (clo - alo))

theorem aloOK_true : aloOK = true := by decide +kernel

theorem a_lower {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 1 / 2)
    (hret : 1 / 10000 < a + c) (hA : c - a ≤ (H a + H b) / 20) : ((alo : ℚ) : ℝ) ≤ a := by
  have hok := aloOK_true
  simp only [aloOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hpa, hpc⟩, hc2⟩, hJ⟩, hH⟩ := hok
  by_contra hn
  push Not at hn
  have halo : ((alo : ℚ) : ℝ) = 1 / 131072 := by simp [alo]
  have hcloR : ((clo : ℚ) : ℝ) = 1 / 10000 - 1 / 131072 := by simp [clo]
  have hc2R : ((clo : ℚ) : ℝ) < 1 / 2 := by rw [hcloR]; norm_num
  have hclo0 : (0 : ℝ) < ((clo : ℚ) : ℝ) := by rw [hcloR]; norm_num
  have hcc : ((clo : ℚ) : ℝ) < c := by rw [hcloR]; rw [halo] at hn; linarith
  have hHa : H a ≤ ((Hhi alo : ℚ) : ℝ) :=
    (CKLaneN1.Edge.H_mono ha.le hn.le (by rw [halo]; norm_num)).trans (H_bounds hpa).2
  have hHb : H b ≤ H c := CKLaneN1.Edge.H_mono (ha.trans hab).le hbc.le hc.le
  have hHc := H_tangent hclo0 (by linarith) (by linarith : 0 < c) (by linarith : c < 1)
  have hHp : H ((clo : ℚ) : ℝ) ≤ ((Hhi clo : ℚ) : ℝ) := (H_bounds hpc).2
  have hJp : J ((clo : ℚ) : ℝ) ≤ ((lamHi clo : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
    CKLaneN1.Capital.J_le hpc hc2R.le
  have hJR : ((lamHi clo : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) ≤ 20 := by
    have := (Rat.cast_le (K := ℝ)).mpr hJ
    push_cast at this
    linarith
  have hHR : ((Hhi alo : ℚ) : ℝ) + ((Hhi clo : ℚ) : ℝ) < 20 * (((clo : ℚ) : ℝ) - ((alo : ℚ) : ℝ)) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hH
    push_cast at this
    linarith
  set Jc := J ((clo : ℚ) : ℝ) with hJcdef
  set Jh := ((lamHi clo : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) with hJhdef
  have m2 : Jc * (c - clo) ≤ Jh * (c - clo) := mul_le_mul_of_nonneg_right hJp (by linarith)
  have m3 : 0 ≤ (20 - Jh) * (c - clo) := mul_nonneg (by linarith) (by linarith)
  nlinarith [m2, m3, hHa, hHb, hHc, hHp, hHR, hA]

end CKLaneN1.R3

end


