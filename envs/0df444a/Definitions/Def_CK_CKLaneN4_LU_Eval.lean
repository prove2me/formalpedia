-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Eval
-- name    : CK_CKLaneN4_LU_Eval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:25:34.063473+00:00
-- url     : https://prove2.me/theorems/8c8a57bc-144e-4aa8-bddc-4ac20e229f99
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Eval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Eval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Eval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Eval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Eval.lean)

import Definitions.Def_CK_CKLaneN4_LU_FastLog
import Definitions.Def_CK_CKLaneN4_LU_Tangent
import Definitions.Def_CK_GeneralCK_Certificates_DyadicInterval
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge

-- ===== source module CKLaneN4.LU.Eval =====
section
/-
Lane N4b — certified point evaluations at dyadic points `v = N / 2^128`.

Dyadic intervals at scale `2^128` (corpus `GeneralCK.Certificates.DyadicInterval`), logarithms by the
snapshot of Lane P's fixed-point `lnDy` (CKLaneN4.LU.FastLog).  For a point record `q = mkPt N`
(`1 ≤ N < 2^128`) the fields enclose `v`, `1 - v`, `log v`, `log (1 - v)`; derived enclosures:
`hn`, `H`, `J`, `kap`, `radialSlope` and `Jd v = -1/(log 2 · v (1-v))`.
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK GeneralCK.Certificates DyadicInterval

abbrev P : ℕ := 128
abbrev DI := DyadicInterval P

def NT : ℕ := 48
def L2c : ℕ × ℕ := ln2Q P 72

theorem L2c_sound : ((L2c.1 : ℕ) : ℝ) ≤ 2 ^ P * Real.log 2 ∧
    2 ^ P * Real.log 2 ≤ ((L2c.2 : ℕ) : ℝ) := ln2Q_sound P 72

theorem scale_cast : ((scale P : ℤ) : ℝ) = 2 ^ P := by simp [scale]

theorem two_pow_P_pos : (0 : ℝ) < 2 ^ P := by positivity

theorem contains_iff {a : DI} {x : ℝ} :
    a.Contains x ↔ ((a.lo : ℝ) ≤ 2 ^ P * x ∧ 2 ^ P * x ≤ (a.hi : ℝ)) := by
  unfold Contains; rw [scale_cast]

theorem lo_le {a : DI} {x : ℝ} (h : a.Contains x) : (a.lo : ℝ) ≤ 2 ^ P * x :=
  (contains_iff.1 h).1

theorem le_hi {a : DI} {x : ℝ} (h : a.Contains x) : 2 ^ P * x ≤ (a.hi : ℝ) :=
  (contains_iff.1 h).2

theorem pos_of_lo {a : DI} {x : ℝ} (h : a.Contains x) (hl : 0 < a.lo) : 0 < x := by
  have h1 := lo_le h
  have : (0 : ℝ) < (a.lo : ℝ) := by exact_mod_cast hl
  have hp := two_pow_P_pos
  nlinarith

theorem nonneg_of_lo {a : DI} {x : ℝ} (h : a.Contains x) (hl : 0 ≤ a.lo) : 0 ≤ x := by
  have h1 := lo_le h
  have : (0 : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast hl
  have hp := two_pow_P_pos
  nlinarith

/-! ### Basic intervals -/

def pt (N : ℤ) : DI := ⟨N, N⟩

theorem pt_contains (N : ℤ) : (pt N).Contains ((N : ℝ) / 2 ^ P) := by
  rw [contains_iff]
  have hp := two_pow_P_pos
  unfold pt
  constructor <;> (field_simp; rfl)

def cst (z : ℤ) : DI := ofInt P z

theorem cst_contains (z : ℤ) : (cst z).Contains (z : ℝ) := ofInt_sound P z

def halfI : DI := pt (2 ^ (P - 1))

theorem halfI_contains : halfI.Contains (1 / 2) := by
  have h := pt_contains (2 ^ (P - 1))
  have e : (((2 ^ (P - 1) : ℤ)) : ℝ) / 2 ^ P = 1 / 2 := by
    push_cast
    rw [show P = (P - 1) + 1 by decide, pow_succ]
    field_simp
    norm_num
  rw [e] at h
  exact h

def L2box : DI := ⟨L2c.1, L2c.2⟩

theorem L2box_contains : L2box.Contains (Real.log 2) := by
  rw [contains_iff]
  exact ⟨by exact_mod_cast L2c_sound.1, by exact_mod_cast L2c_sound.2⟩

theorem L2box_pos : 0 < L2box.lo := by decide +kernel

def L2inv : DI := L2box.recip

theorem L2inv_contains : L2inv.Contains (Real.log 2)⁻¹ := recip_sound L2box_pos L2box_contains

def logN (N : ℕ) : DI := ⟨(lnDy P P NT L2c N).1, (lnDy P P NT L2c N).2⟩

theorem logN_contains {N : ℕ} (hN : 1 ≤ N) : (logN N).Contains (Real.log ((N : ℝ) / 2 ^ P)) := by
  have h := lnDy_sound (P := P) (Q := P) (n := NT) L2c_sound hN
  rw [contains_iff]
  exact h

/-! ### Point records -/

structure PtI where
  v : DI
  w : DI
  lv : DI
  lw : DI

def mkPt (N : ℕ) : PtI := ⟨pt N, pt ((2 ^ P - N : ℕ) : ℤ), logN N, logN (2 ^ P - N)⟩

/-- Semantic content of a point record at the real point `x`. -/
def PtI.Sem (q : PtI) (x : ℝ) : Prop :=
  q.v.Contains x ∧ q.w.Contains (1 - x) ∧ q.lv.Contains (Real.log x) ∧
    q.lw.Contains (Real.log (1 - x))

theorem cast_sub_P {N : ℕ} (h : N < 2 ^ P) :
    (((2 ^ P - N : ℕ) : ℤ) : ℝ) / 2 ^ P = 1 - (N : ℝ) / 2 ^ P := by
  have hle : N ≤ 2 ^ P := h.le
  have hp := two_pow_P_pos
  rw [Int.cast_natCast, Nat.cast_sub hle]
  push_cast
  field_simp

theorem mkPt_sem {N : ℕ} (h1 : 1 ≤ N) (h2 : N < 2 ^ P) :
    (mkPt N).Sem ((N : ℝ) / 2 ^ P) := by
  have hM : 1 ≤ 2 ^ P - N := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := pt_contains (N : ℤ)
    simpa [mkPt] using this
  · have := pt_contains (((2 ^ P - N : ℕ) : ℤ))
    rw [cast_sub_P h2] at this
    exact this
  · exact logN_contains h1
  · have := logN_contains hM
    have e : ((2 ^ P - N : ℕ) : ℝ) / 2 ^ P = 1 - (N : ℝ) / 2 ^ P := by
      have := cast_sub_P h2
      rwa [Int.cast_natCast] at this
    rw [e] at this
    exact this

def PtI.hn (q : PtI) : DI := (q.v.mul q.lv).neg.sub (q.w.mul q.lw)
def PtI.HH (q : PtI) : DI := q.hn.mul L2inv
def PtI.JJ (q : PtI) : DI := (q.lw.sub q.lv).mul L2inv
def PtI.kp (q : PtI) : DI := (q.lv.add q.lw).neg.mul halfI
def PtI.rsDen (q : PtI) : DI := (cst 2).mul (L2box.mul ((q.v.mul q.w).mul q.kp))
def PtI.RS (q : PtI) : DI :=
  q.JJ.add ((((cst 1).sub ((cst 2).mul q.v)).mul q.hn).mul q.rsDen.recip)
def PtI.jdDen (q : PtI) : DI := L2box.mul (q.v.mul q.w)
def PtI.Jd (q : PtI) : DI := q.jdDen.recip.neg

section Sem

variable {q : PtI} {x : ℝ}

theorem PtI.hn_contains (hq : q.Sem x) : q.hn.Contains (Certificates.Mixed.hn x) := by
  obtain ⟨hv, hw, hlv, hlw⟩ := hq
  have h := sub_sound (neg_sound (mul_sound hv hlv)) (mul_sound hw hlw)
  unfold PtI.hn
  have e : Certificates.Mixed.hn x = -(x * Real.log x) - (1 - x) * Real.log (1 - x) := by
    unfold Certificates.Mixed.hn; ring
  rw [e]; exact h

theorem PtI.HH_contains (hq : q.Sem x) : q.HH.Contains (H x) := by
  have h := mul_sound (PtI.hn_contains hq) L2inv_contains
  have e : H x = Certificates.Mixed.hn x * (Real.log 2)⁻¹ := by
    rw [Certificates.Mixed.hn_eq_H_mul_log, mul_assoc,
      mul_inv_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one]
  unfold PtI.HH; rw [e]; exact h

theorem PtI.JJ_contains (hq : q.Sem x) (hx : 0 < x) (hx1 : x < 1) : q.JJ.Contains (J x) := by
  obtain ⟨_, _, hlv, hlw⟩ := hq
  have h := mul_sound (sub_sound hlw hlv) L2inv_contains
  have e : J x = (Real.log (1 - x) - Real.log x) * (Real.log 2)⁻¹ := by
    unfold J; rw [Real.log_div (by linarith) hx.ne', div_eq_mul_inv]
  unfold PtI.JJ; rw [e]; exact h

theorem PtI.kp_contains (hq : q.Sem x) (hx : 0 < x) (hx1 : x < 1) :
    q.kp.Contains (Certificates.Mixed.kap x) := by
  obtain ⟨_, _, hlv, hlw⟩ := hq
  have h := mul_sound (neg_sound (add_sound hlv hlw)) halfI_contains
  have e : Certificates.Mixed.kap x = -(Real.log x + Real.log (1 - x)) * (1 / 2) := by
    unfold Certificates.Mixed.kap; rw [Real.log_mul hx.ne' (by linarith)]; ring
  unfold PtI.kp; rw [e]; exact h

theorem PtI.RS_contains (hq : q.Sem x) (hx : 0 < x) (hx1 : x < 1) (hden : 0 < q.rsDen.lo) :
    q.RS.Contains (radialSlope x) := by
  have hJ := PtI.JJ_contains hq hx hx1
  have hhn := PtI.hn_contains hq
  have hk := PtI.kp_contains hq hx hx1
  obtain ⟨hv, hw, _, _⟩ := hq
  have hD := mul_sound (cst_contains 2) (mul_sound L2box_contains (mul_sound (mul_sound hv hw) hk))
  have hR := recip_sound hden hD
  have hN := mul_sound (sub_sound (cst_contains 1) (mul_sound (cst_contains 2) hv)) hhn
  have h := add_sound hJ (mul_sound hN hR)
  unfold PtI.RS
  have e : radialSlope x = J x + ((((1 : ℤ) : ℝ) - ((2 : ℤ) : ℝ) * x) * Certificates.Mixed.hn x) *
      (((2 : ℤ) : ℝ) * (Real.log 2 * ((x * (1 - x)) * Certificates.Mixed.kap x)))⁻¹ := by
    unfold radialSlope
    push_cast
    rw [div_eq_mul_inv]
    congr 2
    ring
  rw [e]
  exact h

theorem PtI.Jd_contains (hq : q.Sem x) (hden : 0 < q.jdDen.lo) :
    q.Jd.Contains (CKLaneN4.LU.Jd x) := by
  obtain ⟨hv, hw, _, _⟩ := hq
  have hD := mul_sound L2box_contains (mul_sound hv hw)
  have h := neg_sound (recip_sound hden hD)
  unfold PtI.Jd
  have e : CKLaneN4.LU.Jd x = -((Real.log 2 * (x * (1 - x)))⁻¹) := by
    unfold CKLaneN4.LU.Jd; rw [neg_div, one_div]; congr 2; ring
  rw [e]; exact h

end Sem

end CKLaneN4.LU

end


