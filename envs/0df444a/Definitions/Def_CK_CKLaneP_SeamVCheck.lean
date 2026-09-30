-- Prove2me | Definitions.Def_CK_CKLaneP_SeamVCheck
-- name    : CK_CKLaneP_SeamVCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:12:30.362414+00:00
-- url     : https://prove2.me/theorems/c2a42593-9c76-4788-bf8c-d5e433034d16
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamVCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamVCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamVCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamVCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamVCheck.lean)

import Definitions.Def_CK_CKLaneP_SeamWBase

-- ===== source module CKLaneP.SeamVCheck =====
section
/-
Lane P — the vacuity (V-mode) seam cell checker: no stationary seam point exists in the cell.

Cell: `p ∈ [p0, p1]` (`p0 = 0` allowed), `t = (q−p)/(S/2−p) ∈ [t0, t1]` (`0 ≤ t0 ≤ t1`, any case).
At a stationary point `Θ(y*/E) = Δ(y*)` (`seamD_eq_sub`); `Δ(y) ≥ (Pmin/2)·log(f/e)` (`seamDelta_ge`)
and `Θ(y*/E) ≤ Θ((S−2p0)/E_lo) ≤ Shi(nxv)`.  The check `Shi(nxv) < (Pmin/2)·logDnQ(fL/eH)` is a
contradiction (`seam_no_stat`).  `Pmin` is either the unbracketed `Pmin0(vb)` (`nva = 0`) or the
bracketed `PminQ(va, vb)` (needs a positive entropy lower bound `eL = Hlo(np0)`, `np0 ≠ 0`).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

structure VCell where
  p0 : ℚ
  p1 : ℚ
  np0 : ℕ
  np1 : ℕ
  t0 : ℚ
  t1 : ℚ
  nql : ℕ
  nq : ℕ
  nvb : ℕ
  nva : ℕ
  nxv : ℕ
deriving Repr

namespace VCell

def blo (c : VCell) : ℚ := c.t0 * (Sq / 2 - c.p1)
def bhi (c : VCell) : ℚ := c.t1 * (Sq / 2 - c.p0)
def eLv (c : VCell) : ℚ := if c.np0 = 0 then 0 else (dy c.np0).Hlo
def eH (c : VCell) : ℚ := (dy c.np1).Hhi
def fL (c : VCell) : ℚ := (dy c.nql).Hlo
def fH (c : VCell) : ℚ := (dy c.nq).Hhi
def EL (c : VCell) : ℚ := c.eLv + c.fL
def Xmin (c : VCell) : ℚ := (1 - 2 * Sq + 2 * c.p0) / (2 * c.fH)
def Wmax (c : VCell) : ℚ := 1 / (2 * c.eLv)
def vb (c : VCell) : ℚ := (dy c.nvb).v
def Pmin (c : VCell) : ℚ :=
  if c.nva = 0 then (1 - 2 * c.vb) / ((1 + c.vb / 2) ^ 3 * L2hiD) else PminQ (dy c.nva) (dy c.nvb)
def xv (c : VCell) : ℚ := (Sq - 2 * c.p0) / c.EL
def lfe (c : VCell) : ℚ := logDnQ (c.fL / c.eH)

end VCell

/-- The Boolean check of a V-cell. -/
def vcheck (c : VCell) : Bool := decide (
  VD.okDy 60 c.np1 = true ∧ VD.okDy 60 c.nql = true ∧ VD.okDy 60 c.nq = true ∧
  VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nxv = true ∧
  (c.np0 = 0 ∨ (VD.okDy 60 c.np0 = true ∧ dyq c.np0 ≤ c.p0)) ∧
  0 ≤ c.p0 ∧ c.p0 < c.p1 ∧ c.p1 ≤ dyq c.np1 ∧ 0 ≤ c.t0 ∧ c.t0 ≤ c.t1 ∧
  dyq c.nql ≤ c.p0 + c.blo ∧ c.p1 + c.bhi ≤ dyq c.nq ∧
  0 < c.fL ∧ 0 ≤ c.eLv ∧
  dyq c.nvb ≤ 1 / 1000 ∧ 4 ≤ (dy c.nvb).a1 ∧
  0 < c.Xmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Xmin * (dy c.nvb).Hlo ∧
  (c.nva = 0 ∨ (VD.okDy 60 c.nva = true ∧ 0 < c.eLv ∧
    2 * c.Wmax * (dy c.nva).Hhi ≤ 1 - 2 * (dy c.nva).v ∧ 1 < (dy c.nva).b1)) ∧
  0 ≤ c.Pmin ∧ 1 ≤ ⌊c.fL / c.eH * 2 ^ 60⌋₊ ∧
  0 < Sq - 2 * c.p0 ∧ (dy c.nxv).v < 1 / 2 ∧ 0 < (dy c.nxv).a1 + (dy c.nxv).a2 ∧
  2 * c.xv * (dy c.nxv).Hhi ≤ 1 - 2 * (dy c.nxv).v ∧
  (dy c.nxv).Shi < c.Pmin / 2 * c.lfe)

set_option maxHeartbeats 2000000 in
/-- Soundness of the V-cell check: there is no stationary seam point in the cell. -/
theorem vcheck_sound (c : VCell) (hc : vcheck c = true) {p q ys : ℝ}
    (hp : 0 < p) (hpq : p < q)
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (ht0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p)
    (ht1 : q - p ≤ ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) : False := by
  unfold vcheck at hc
  obtain ⟨ok1, okql, okq, okvb, okxv, hnp0, hp00, hp01, hnp1, ht00, ht01, hql, hqhi, hfL, heLv0,
    hvb, hvba1, hXmin, hbrX, hnva, hPmin0, hfl1, hS2p, hxvv, hxva, hbrxv, hmain⟩ :=
    of_decide_eq_true hc
  have d1 := dy_sound ok1
  have dql := dy_sound okql
  have dq := dy_sound okq
  have dvb := dy_sound okvb
  have dxv := dy_sound okxv
  have hHmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → H a ≤ H b :=
    fun ha hab hb => H_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, hb⟩ hab
  -- cell geometry
  have ht00R : (0 : ℝ) ≤ ((c.t0 : ℚ) : ℝ) := by exact_mod_cast ht00
  have ht1nn : (0 : ℝ) ≤ ((c.t1 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ c.t1 := le_trans ht00 ht01
    exact_mod_cast this
  have eblo : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
    unfold VCell.blo; push_cast; rw [Sq_cast]
  have ebhi : ((c.bhi : ℚ) : ℝ) = ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p0 : ℚ) : ℝ)) := by
    unfold VCell.bhi; push_cast; rw [Sq_cast]
  have hqlo : ((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ) ≤ q := by
    rw [eblo]
    have h1 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) ≤
        ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) :=
      mul_le_mul_of_nonneg_left (by linarith) ht00R
    linarith
  have hqhi' : q ≤ ((c.p1 : ℚ) : ℝ) + ((c.bhi : ℚ) : ℝ) := by
    rw [ebhi]
    have h1 : ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤
        ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p0 : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) ht1nn
    linarith
  have hqlR : ((dy c.nql).v : ℝ) ≤ q := by
    rw [dy_v]
    have h := (Rat.cast_le (K := ℝ)).mpr hql
    push_cast at h
    linarith
  have hqqd : q ≤ ((dy c.nq).v : ℝ) := by
    rw [dy_v]
    have h := (Rat.cast_le (K := ℝ)).mpr hqhi
    push_cast at h
    linarith
  have hvqh : ((dy c.nq).v : ℝ) ≤ 1 / 2 := VD.cast_le_half dq.2.1
  have hq0 : 0 < q := hp.trans hpq
  have hq12 : q ≤ 1 / 2 := le_trans hqqd hvqh
  have hv1 : p ≤ ((dy c.np1).v : ℝ) := by
    rw [dy_v]
    have h := (Rat.cast_le (K := ℝ)).mpr hnp1
    exact le_trans hp1 h
  have hv1h : ((dy c.np1).v : ℝ) ≤ 1 / 2 := VD.cast_le_half d1.2.1
  have hvl0 : (0 : ℝ) < ((dy c.nql).v : ℝ) := by exact_mod_cast dql.1
  -- entropy data
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q := hHmono hp.le hpq.le hq12
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have heHR : H p ≤ ((c.eH : ℚ) : ℝ) := le_trans (hHmono hp.le hv1 hv1h) (VD.le_Hhi d1)
  have hfLR : ((c.fL : ℚ) : ℝ) ≤ H q :=
    le_trans (VD.Hlo_le dql) (hHmono hvl0.le hqlR hq12)
  have hfHR : H q ≤ ((c.fH : ℚ) : ℝ) := le_trans (hHmono hq0.le hqqd hvqh) (VD.le_Hhi dq)
  have heLR : ((c.eLv : ℚ) : ℝ) ≤ H p := by
    rcases hnp0 with h0 | ⟨ok0, hn0⟩
    · have e : c.eLv = 0 := by unfold VCell.eLv; rw [if_pos h0]
      rw [e]; push_cast; exact hHp.le
    · have hne : c.np0 ≠ 0 := by
        intro h; rw [h] at ok0; exact absurd ok0 (by decide)
      have e : c.eLv = (dy c.np0).Hlo := by unfold VCell.eLv; rw [if_neg hne]
      rw [e]
      have d0 := dy_sound ok0
      have hv00 : (0 : ℝ) < ((dy c.np0).v : ℝ) := by exact_mod_cast d0.1
      have hv0 : ((dy c.np0).v : ℝ) ≤ p := by
        rw [dy_v]
        have h := (Rat.cast_le (K := ℝ)).mpr hn0
        exact le_trans h hp0
      exact le_trans (VD.Hlo_le d0) (hHmono hv00.le hv0 (by linarith))
  have hfL0 : (0 : ℝ) < ((c.fL : ℚ) : ℝ) := by exact_mod_cast hfL
  have heLv0R : (0 : ℝ) ≤ ((c.eLv : ℚ) : ℝ) := by exact_mod_cast heLv0
  have hE : 0 < H p + H q := by linarith
  have eEL : ((c.EL : ℚ) : ℝ) = ((c.eLv : ℚ) : ℝ) + ((c.fL : ℚ) : ℝ) := by
    unfold VCell.EL; push_cast; ring
  have hELR : ((c.EL : ℚ) : ℝ) ≤ H p + H q := by rw [eEL]; linarith
  have hEL0 : (0 : ℝ) < ((c.EL : ℚ) : ℝ) := by rw [eEL]; linarith
  -- profile lower bound on the Δ-range
  have hvbv : (dy c.nvb).v ≤ 1 / 1000 := by rw [dy_v]; exact hvb
  have hvbR : ((dy c.nvb).v : ℝ) ≤ 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).mpr hvbv
    rw [show ((1 / 1000 : ℚ) : ℝ) = 1 / 1000 by norm_num] at this
    exact this
  have hL4 : (4 : ℝ) ≤ -Real.log ((dy c.nvb).v : ℝ) :=
    le_trans (by exact_mod_cast hvba1) dvb.2.2.1
  have eXmin : ((c.Xmin : ℚ) : ℝ) = (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) /
      (2 * ((c.fH : ℚ) : ℝ)) := by
    unfold VCell.Xmin; push_cast; rw [Sq_cast]
  have hp00R : (0 : ℝ) ≤ ((c.p0 : ℚ) : ℝ) := by exact_mod_cast hp00
  have hA0 : (0 : ℝ) ≤ 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  have hPmin0R : (0 : ℝ) ≤ ((c.Pmin : ℚ) : ℝ) := by exact_mod_cast hPmin0
  have hPall : ∀ t ∈ Icc ((1 - 1 / 10000 - ys) / (2 * H q)) ((1 - 1 / 10000 + ys) / (2 * H p)),
      ((c.Pmin : ℚ) : ℝ) ≤ profile (radialContact (2 * t) 1) := by
    intro x hx
    have hXx : ((c.Xmin : ℚ) : ℝ) ≤ x := by
      refine le_trans ?_ hx.1
      rw [eXmin]; exact xmin_le_of hHq hfHR hA0 (by linarith)
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hXx
    have hcb := contact_le_of_bracket dvb hXmin hbrX hXx
    rcases hnva with h0 | ⟨okva, heLpos, hbrW, hvab1⟩
    · have e : ((c.Pmin : ℚ) : ℝ) = (1 - 2 * ((dy c.nvb).v : ℝ)) /
          ((1 + ((dy c.nvb).v : ℝ) / 2) ^ 3 * ((L2hiD : ℚ) : ℝ)) := by
        unfold VCell.Pmin VCell.vb; rw [if_pos h0]; push_cast; ring
      rw [e]
      have h := profile_ge_bracket0 (radialContact_pos (by linarith) one_pos) hcb hvbR hL4
      have hl2 := log2D_bounds
      have hvb0 : (0 : ℝ) < ((dy c.nvb).v : ℝ) := by exact_mod_cast dvb.1
      refine le_trans ?_ h
      apply div_le_div_of_nonneg_left (by linarith) (by have := log_two_pos; positivity)
      exact mul_le_mul_of_nonneg_left hl2.2 (by positivity)
    · have dva := dy_sound okva
      have hne : c.nva ≠ 0 := by
        intro h; rw [h] at okva; exact absurd okva (by decide)
      have e : c.Pmin = PminQ (dy c.nva) (dy c.nvb) := by unfold VCell.Pmin; rw [if_neg hne]
      rw [e]
      have heLposR : (0 : ℝ) < ((c.eLv : ℚ) : ℝ) := by exact_mod_cast heLpos
      have eW : ((c.Wmax : ℚ) : ℝ) = 1 / (2 * ((c.eLv : ℚ) : ℝ)) := by
        unfold VCell.Wmax; push_cast; ring
      have hxW : x ≤ ((c.Wmax : ℚ) : ℝ) := by
        rw [eW]
        refine le_trans hx.2 ?_
        have h1 : (1 - 1 / 10000 + ys) / (2 * H p) ≤ 1 / (2 * H p) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        have h2 : 1 / (2 * H p) ≤ 1 / (2 * ((c.eLv : ℚ) : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
        linarith
      exact PminQ_sound dva dvb hvbv hvba1 hvab1 (contact_ge_of_bracket dva hbrW hx0 hxW) hcb
  have hΔ := seamDelta_ge (S := 1 / 10000) (y := ys) (P := ((c.Pmin : ℚ) : ℝ)) hHp hHpq hys0.le
    (by linarith) hPmin0R hPall
  -- log(fL/eH) ≤ log(f/e)
  have heH0 : (0 : ℝ) < ((c.eH : ℚ) : ℝ) := lt_of_lt_of_le hHp heHR
  have hlog : ((c.lfe : ℚ) : ℝ) ≤ Real.log (H q / H p) := by
    unfold VCell.lfe
    refine le_trans (logDnQ_sound hfl1) (Real.log_le_log ?_ ?_)
    · push_cast; positivity
    · push_cast
      rw [div_le_div_iff₀ heH0 hHp]
      exact mul_le_mul hfLR heHR hHp.le hHq.le
  have hB0 : ((c.Pmin : ℚ) : ℝ) / 2 * ((c.lfe : ℚ) : ℝ) ≤ seamDelta (1 / 10000) (H p) (H q) ys := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ((c.Pmin : ℚ) : ℝ) / 2)
    linarith
  -- Θ at the top of the range
  have hS2pR : (0 : ℝ) < 1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hS2p
    push_cast at h
    rw [Sq_cast] at h
    linarith
  have exv : ((c.xv : ℚ) : ℝ) = (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) / ((c.EL : ℚ) : ℝ) := by
    unfold VCell.xv; push_cast; rw [Sq_cast]
  have hxle : (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) / (H p + H q) ≤ ((c.xv : ℚ) : ℝ) := by
    rw [exv]; exact div_le_div_of_nonneg_left hS2pR.le hEL0 hELR
  have hθ := theta_le_Shi dxv hxvv hxva (div_pos hS2pR hE) hxle hbrxv
  have hmainR : (((dy c.nxv).Shi : ℚ) : ℝ) < ((c.Pmin : ℚ) : ℝ) / 2 * ((c.lfe : ℚ) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hmain
    push_cast at h
    exact h
  exact seam_no_stat (S := 1 / 10000) (yhi := 1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) hHp hHq hstat
    hys0.le (by linarith) hB0 (lt_of_le_of_lt hθ hmainR)

end CKLaneP

end


