-- Prove2me | Definitions.Def_CK_CKLaneP_SeamNCheck
-- name    : CK_CKLaneP_SeamNCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:58:17.992092+00:00
-- url     : https://prove2.me/theorems/d7d959e7-7c78-41a7-9212-e4cd680100c1
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamNCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamNCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamNCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamNCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamNCheck.lean)

import Definitions.Def_CK_CKLaneP_SeamArith

-- ===== source module CKLaneP.SeamNCheck =====
section
/-
Lane P — the normalized (N-mode) seam cell checkers.

Cell: `p ∈ [p0, p1]`, `t = (q−p)/(S/2−p) ∈ [t0, t1]`, dyadic witnesses (`v = n/2^60`):
`np0 ≤ p0`, `np1 ≥ p1` (entropy data), `nq ≥ q_hi`, contact brackets `nvb`, `nva`,
Θ-ratio point `xb` (`Θ(xb) ≥ Slo(nxb)`), slope bracket `nx2` on `(0, xb]`.

* `ncell_facts`   : the common real consequences of `ncommon c = true` for a stationary seam point.
* `ncheckA_sound` : case A (`t1 ≤ 1`, so `q ≤ S/2`), base point `y = 0`.
* `ncheckB_sound` : case B (`1 ≤ t0`, `q > S/2`), base point `y_lo = 2q − S`, with two vacuity tests.
All soundness theorems are conditional on the double-cap scalar owner (used only for `DC ≥ 0`).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

def Sq : ℚ := 1 / 10000

theorem Sq_cast : ((Sq : ℚ) : ℝ) = 1 / 10000 := by unfold Sq; norm_num

structure NCell where
  p0 : ℚ
  p1 : ℚ
  np0 : ℕ
  np1 : ℕ
  t0 : ℚ
  t1 : ℚ
  nq : ℕ
  nvb : ℕ
  nva : ℕ
  xb : ℚ
  nxb : ℕ
  nx2 : ℕ
deriving Repr

namespace NCell

def bhi (c : NCell) : ℚ := c.t1 * (Sq / 2 - c.p0)
def qd (c : NCell) : ℚ := dyq c.nq
def eL (c : NCell) : ℚ := (dy c.np0).Hlo
def eH (c : NCell) : ℚ := (dy c.np1).Hhi
def fH (c : NCell) : ℚ := (dy c.nq).Hhi
def EL (c : NCell) : ℚ := 2 * c.eL
def EH (c : NCell) : ℚ := c.eH + c.fH
def Jq (c : NCell) : ℚ := (dy c.nq).Jlo
def Jp (c : NCell) : ℚ := (dy c.np0).Jhi
def rs0 (c : NCell) : ℚ := (dy c.np0).Shi
def Pmax (c : NCell) : ℚ := PmaxQ (dy c.nvb)
def Pmin (c : NCell) : ℚ := PminQ (dy c.nva) (dy c.nvb)
def lam (c : NCell) : ℚ := c.Pmax / (1 - 2 * Sq + 2 * c.p0)
def thb (c : NCell) : ℚ := (dy c.nxb).Slo
def M (c : NCell) : ℚ := PsiUB (dy c.nx2) (dy dhN)
def DCraw (c : NCell) : ℚ :=
  1 / (c.p1 * (2 + c.bhi / c.p0) * L2hiD) - c.rs0 / (4 * L2loD * (c.p0 * (1 - c.p0)) * c.Jq)
def DCn (c : NCell) : ℚ := max 0 c.DCraw
def c1n (c : NCell) : ℚ := c.Pmin * (2 * c.Jq / (3 * c.eH + c.fH))
def c2 (c : NCell) : ℚ := 12 / c.EL
def Bn (c : NCell) : ℚ := max 0 (Sq / 2 - c.qd) * (9 / 40 * c.Jq ^ 2 / c.fH ^ 2)
def A0n (c : NCell) : ℚ := c.Pmax / 2 * (c.Jp * c.EH / (2 * c.eL * c.eL))
def Yn (c : NCell) : ℚ := c.A0n * c.EH / (c.thb / c.xb - c.lam * c.EH)
def Xmin (c : NCell) : ℚ := (1 - 2 * Sq + 2 * c.p0) / (2 * c.fH)
def Vmin (c : NCell) : ℚ := (1 - 2 * c.qd) / c.EH
def Wmax (c : NCell) : ℚ := 1 / (2 * c.eL)
def Pl (c : NCell) : ℚ := min c.Xmin c.Vmin

end NCell

/-- Conditions shared by all N-cells. -/
def ncommon (c : NCell) : Bool := decide (
  VD.okDy 60 c.np0 = true ∧ VD.okDy 60 c.np1 = true ∧ VD.okDy 60 c.nq = true ∧
  VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nva = true ∧ VD.okDy 60 c.nxb = true ∧
  VD.okDy 60 c.nx2 = true ∧ dyq c.np0 ≤ c.p0 ∧ c.p1 ≤ dyq c.np1 ∧
  0 < c.p0 ∧ c.p0 < c.p1 ∧ c.p1 ≤ Sq / 2 ∧ 0 ≤ c.t1 ∧
  c.p1 + c.bhi ≤ c.qd ∧ c.qd ≤ 1 / 10000 ∧
  0 < (dy c.np0).a1 + (dy c.np0).a2 ∧ 0 < c.eL ∧ 0 < c.Jq ∧
  dyq c.nvb ≤ 1 / 10000 ∧ 4 ≤ (dy c.nvb).a1 ∧
  0 < c.Pl ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Pl * (dy c.nvb).Hlo ∧
  2 * c.Wmax * (dy c.nva).Hhi ≤ 1 - 2 * (dy c.nva).v ∧ 1 < (dy c.nva).b1 ∧
  0 < c.xb ∧ (dy c.nxb).v < 1 / 2 ∧ 1 - 2 * (dy c.nxb).v ≤ 2 * c.xb * (dy c.nxb).Hlo ∧
  2 * c.xb * (dy c.nx2).Hhi ≤ 1 - 2 * (dy c.nx2).v ∧ 0 < (dy dhN).kapLo ∧ 0 ≤ c.M ∧
  0 ≤ c.Pmin ∧ 0 ≤ c.Pmax ∧
  c.A0n * c.bhi + c.lam * (Sq - 2 * c.p0) < c.thb ∧ c.lam * c.EH < c.thb / c.xb)

/-- Case-A N-cell check. -/
def ncheckA (c : NCell) : Bool :=
  ncommon c && decide (0 ≤ c.t0 ∧ c.t0 < c.t1 ∧ c.t1 ≤ 1 ∧
    0 ≤ c.DCn + c.c1n - c.c2 / 2 + c.Bn - c.M * c.Yn ^ 2 / (2 * c.EL))

set_option maxHeartbeats 2000000 in
/-- Real consequences of the common N-cell conditions at a stationary seam point. -/
theorem ncell_facts (hdouble : CanonicalDoubleCapEntropyEndpoints) (c : NCell)
    (hc : ncommon c = true) {p q ys : ℝ}
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (hβ0 : 0 < q - p) (hbhi : q - p ≤ ((c.bhi : ℚ) : ℝ))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    (q - p) ^ 2 * ((c.DCn : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) ∧
    (∀ t ∈ Ioo p q, ((c.c1n : ℚ) : ℝ) * (q - p) - ((c.c2 : ℚ) : ℝ) * (q - t) ≤
      rightD q (H p) (H q) t) ∧
    (∀ m ∈ Icc q (1 / 10000 / 2), (q - p) ^ 2 * ((c.Bn : ℚ) : ℝ) ≤
      (1 / 10000 / 2 - q) * jdef (H p) (H q) m) ∧
    (∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      ((c.M : ℚ) : ℝ) * ((ys - t) / (H p + H q))) ∧
    0 ≤ ((c.M : ℚ) : ℝ) ∧ ys ≤ (q - p) * ((c.Yn : ℚ) : ℝ) ∧
    ((c.EL : ℚ) : ℝ) ≤ H p + H q ∧ 0 < ((c.EL : ℚ) : ℝ) ∧ q ≤ ((c.qd : ℚ) : ℝ) ∧
    ((c.Pmin : ℚ) : ℝ) * (((c.Jq : ℚ) : ℝ) * (q - p) / ((c.fH : ℚ) : ℝ)) / 2 ≤
      e8Theta (ys / (H p + H q)) := by
  unfold ncommon at hc
  obtain ⟨ok0, ok1, okq, okvb, okva, okxb, okx2, hnp0, hnp1, hp0pos, hp01, hp1S, ht1nn,
    hqhi, hqd, ha12, heL, hJq, hvb, hvba1, hPl, hbrP, hbrW, hvab1, hxb, hxbv, hbrxb,
    hbrx2, hdhk, hM0, hPmin0, hPmax0, hneed, hden⟩ := of_decide_eq_true hc
  have d0 := dy_sound ok0
  have d1 := dy_sound ok1
  have dq := dy_sound okq
  have dvb := dy_sound okvb
  have dva := dy_sound okva
  have dxb := dy_sound okxb
  have dx2 := dy_sound okx2
  have dh := dy_sound dh_ok
  -- basic real facts
  have hp0R : (0 : ℝ) < ((c.p0 : ℚ) : ℝ) := by exact_mod_cast hp0pos
  have hp : 0 < p := lt_of_lt_of_le hp0R hp0
  have hp1SR : ((c.p1 : ℚ) : ℝ) ≤ 1 / 10000 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hp1S
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have hqhiR : ((c.p1 : ℚ) : ℝ) + ((c.bhi : ℚ) : ℝ) ≤ ((c.qd : ℚ) : ℝ) := by exact_mod_cast hqhi
  have hqqd : q ≤ ((c.qd : ℚ) : ℝ) := by linarith
  have hqdR : ((c.qd : ℚ) : ℝ) ≤ 1 / 10000 := by
    have := (Rat.cast_le (K := ℝ)).mpr hqd
    rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at this
    exact this
  have hpq : p < q := by linarith
  have hq0 : 0 < q := by linarith
  -- H, J, rs bounds
  have hv0 : ((dy c.np0).v : ℝ) ≤ (c.p0 : ℝ) := by rw [dy_v]; exact_mod_cast hnp0
  have hv1 : (c.p1 : ℝ) ≤ ((dy c.np1).v : ℝ) := by rw [dy_v]; exact_mod_cast hnp1
  have hvq : ((dy c.nq).v : ℝ) = (c.qd : ℝ) := by rw [dy_v]; rfl
  have hv00 : (0 : ℝ) < ((dy c.np0).v : ℝ) := by exact_mod_cast d0.1
  have hv1h : ((dy c.np1).v : ℝ) ≤ 1 / 2 := VD.cast_le_half d1.2.1
  have hHmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → H a ≤ H b :=
    fun ha hab hb => H_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, hb⟩ hab
  have heLR : ((c.eL : ℚ) : ℝ) ≤ H p :=
    le_trans (VD.Hlo_le d0) (hHmono hv00.le (hv0.trans hp0) (by linarith))
  have heHR : H p ≤ ((c.eH : ℚ) : ℝ) :=
    le_trans (hHmono hp.le (hp1.trans hv1) hv1h) (VD.le_Hhi d1)
  have hfHR : H q ≤ ((c.fH : ℚ) : ℝ) := by
    have h := VD.le_Hhi dq
    rw [hvq] at h
    exact le_trans (hHmono hq0.le hqqd (by linarith)) h
  have hHpq : H p ≤ H q := hHmono hp.le hpq.le (by linarith)
  have hJqR : ((c.Jq : ℚ) : ℝ) ≤ J q := by
    have h := VD.Jlo_le dq
    rw [hvq] at h
    exact le_trans h (J_antitone hq0 (by linarith) hqqd)
  have hJpR : J p ≤ ((c.Jp : ℚ) : ℝ) :=
    le_trans (J_antitone hv00 (by linarith) (hv0.trans hp0)) (VD.le_Jhi d0)
  have hrsR : radialSlope p ≤ ((c.rs0 : ℚ) : ℝ) :=
    le_trans (ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ⟨hv00, by linarith⟩
      ⟨hp, by linarith⟩ (hv0.trans hp0)) (VD.le_Shi d0 ha12)
  have heL0 : (0 : ℝ) < ((c.eL : ℚ) : ℝ) := by exact_mod_cast heL
  have hJq0 : (0 : ℝ) < ((c.Jq : ℚ) : ℝ) := by exact_mod_cast hJq
  have hHp : 0 < H p := lt_of_lt_of_le heL0 heLR
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hELR : ((c.EL : ℚ) : ℝ) ≤ H p + H q := by
    have e : ((c.EL : ℚ) : ℝ) = 2 * ((c.eL : ℚ) : ℝ) := by unfold NCell.EL; push_cast; ring
    rw [e]; linarith
  have hEHR : H p + H q ≤ ((c.EH : ℚ) : ℝ) := by
    have e : ((c.EH : ℚ) : ℝ) = ((c.eH : ℚ) : ℝ) + ((c.fH : ℚ) : ℝ) := by
      unfold NCell.EH; push_cast; ring
    rw [e]; linarith
  have hEL0 : (0 : ℝ) < ((c.EL : ℚ) : ℝ) := by
    have e : ((c.EL : ℚ) : ℝ) = 2 * ((c.eL : ℚ) : ℝ) := by unfold NCell.EL; push_cast; ring
    rw [e]; linarith
  have hEH0 : (0 : ℝ) < ((c.EH : ℚ) : ℝ) := lt_of_lt_of_le hE hEHR
  -- profile brackets
  have hvbv : (dy c.nvb).v ≤ 1 / 1000 := by rw [dy_v]; exact le_trans hvb (by norm_num)
  have hPmaxAll : ∀ x : ℝ, ((c.Pl : ℚ) : ℝ) ≤ x →
      profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ) := by
    intro x hx
    have hcb := contact_le_of_bracket dvb hPl hbrP hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hPl) hx
    exact PmaxQ_sound dvb hvbv hvba1 (radialContact_pos (by linarith) one_pos) hcb
  have hPminAll : ∀ x : ℝ, ((c.Pl : ℚ) : ℝ) ≤ x → x ≤ ((c.Wmax : ℚ) : ℝ) →
      ((c.Pmin : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx1 hx2
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hPl) hx1
    exact PminQ_sound dva dvb hvbv hvba1 hvab1 (contact_ge_of_bracket dva hbrW hx0 hx2)
      (contact_le_of_bracket dvb hPl hbrP hx1)
  have hPlX : ((c.Pl : ℚ) : ℝ) ≤ ((c.Xmin : ℚ) : ℝ) := by
    have : c.Pl ≤ c.Xmin := min_le_left _ _
    exact_mod_cast this
  have hPlV : ((c.Pl : ℚ) : ℝ) ≤ ((c.Vmin : ℚ) : ℝ) := by
    have : c.Pl ≤ c.Vmin := min_le_right _ _
    exact_mod_cast this
  have hPmax0R : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by exact_mod_cast hPmax0
  have hPmin0R : (0 : ℝ) ≤ ((c.Pmin : ℚ) : ℝ) := by exact_mod_cast hPmin0
  have eXmin : ((c.Xmin : ℚ) : ℝ) = (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) /
      (2 * ((c.fH : ℚ) : ℝ)) := by
    unfold NCell.Xmin; push_cast; rw [Sq_cast]
  have eVmin : ((c.Vmin : ℚ) : ℝ) = (1 - 2 * ((c.qd : ℚ) : ℝ)) / ((c.EH : ℚ) : ℝ) := by
    unfold NCell.Vmin; push_cast; ring
  have eWmax : ((c.Wmax : ℚ) : ℝ) = 1 / (2 * ((c.eL : ℚ) : ℝ)) := by
    unfold NCell.Wmax; push_cast; ring
  have hA0 : (0 : ℝ) ≤ 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  -- Xmin below the relevant arguments
  have hXf : ∀ y : ℝ, 0 ≤ y → y < 1 / 10000 - 2 * p →
      ((c.Pl : ℚ) : ℝ) ≤ (1 - 1 / 10000 - y) / (2 * H q) := by
    intro y hy0 hy
    refine le_trans hPlX ?_
    rw [eXmin]
    exact xmin_le_of hHq hfHR hA0 (by linarith)
  -- (1) DC
  have hDC : (q - p) ^ 2 * ((c.DCn : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
    unfold NCell.DCn
    rcases le_total c.DCraw 0 with hneg | hpos
    · rw [max_eq_left hneg]
      have h := canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints hdouble hp hpq.le
        (by linarith : q ≤ 1 / 2)
      push_cast
      linarith
    · rw [max_eq_right hpos]
      have h := dc_cell_lower (p0 := ((c.p0 : ℚ) : ℝ)) (p1 := ((c.p1 : ℚ) : ℝ))
        (βhi := ((c.bhi : ℚ) : ℝ)) (Jq := ((c.Jq : ℚ) : ℝ)) (rs0 := ((c.rs0 : ℚ) : ℝ))
        (l2hi := ((L2hiD : ℚ) : ℝ)) (l2lo := ((L2loD : ℚ) : ℝ)) hp0R hp0 hp1 hpq
        (by linarith) hbhi hJqR hJq0 hrsR log2D_bounds.2 log2D_bounds.1 VD.L2lo_pos
      unfold NCell.DCraw
      push_cast
      exact h
  -- (2) right fiber
  have hR : ∀ t ∈ Ioo p q, ((c.c1n : ℚ) : ℝ) * (q - p) - ((c.c2 : ℚ) : ℝ) * (q - t) ≤
      rightD q (H p) (H q) t := by
    intro t ht
    have h := rightD_cell_lower (Pmin := ((c.Pmin : ℚ) : ℝ)) (eH := ((c.eH : ℚ) : ℝ))
      (fH := ((c.fH : ℚ) : ℝ)) (Jq := ((c.Jq : ℚ) : ℝ)) (EL := ((c.EL : ℚ) : ℝ))
      hp ht.1.le ht.2 (by linarith) hPmin0R
      (fun x hx => hPminAll x
        (le_trans hPlV (by rw [eVmin]; exact le_trans (vmin_le_of (by linarith) hE hEHR
          (by linarith [ht.2])) hx.1))
        (by rw [eWmax]; exact le_trans hx.2 (w_le_wmax_of (by linarith [ht.1]) heL0 heLR)))
      heHR hfHR hJqR hJq0.le hELR hEL0
    have e1 : ((c.c1n : ℚ) : ℝ) = ((c.Pmin : ℚ) : ℝ) *
        (2 * ((c.Jq : ℚ) : ℝ) / (3 * ((c.eH : ℚ) : ℝ) + ((c.fH : ℚ) : ℝ))) := by
      unfold NCell.c1n; push_cast; ring
    have e2 : ((c.c2 : ℚ) : ℝ) = 12 / ((c.EL : ℚ) : ℝ) := by
      unfold NCell.c2; push_cast; ring
    rw [e1, e2]
    exact h
  -- (3) bulk
  have hfe : ((c.Jq : ℚ) : ℝ) * (q - p) ≤ H q - H p := by
    have h1 := J_mul_le_H_sub hp.le hpq.le (by linarith)
    have h2 := mul_le_mul_of_nonneg_right hJqR hβ0.le
    linarith
  have hB : ∀ m ∈ Icc q (1 / 10000 / 2), (q - p) ^ 2 * ((c.Bn : ℚ) : ℝ) ≤
      (1 / 10000 / 2 - q) * jdef (H p) (H q) m := by
    intro m hm
    have hm12 : m < 1 / 2 := by linarith [hm.2]
    have hcap : radialContact ((1 - 2 * m) / H q) 1 ≤ 1 / 10000 := by
      have e : (1 - 2 * m) / H q = 2 * ((1 - 2 * m) / (2 * H q)) := by field_simp
      rw [e]
      have hx : ((c.Pl : ℚ) : ℝ) ≤ (1 - 2 * m) / (2 * H q) := by
        refine le_trans hPlX ?_
        rw [eXmin]; exact xmin_le_of hHq hfHR hA0 (by linarith [hm.2])
      have hcb := contact_le_of_bracket dvb hPl hbrP hx
      have : ((dy c.nvb).v : ℝ) ≤ 1 / 10000 := by
        have h' : ((dy c.nvb).v : ℚ) ≤ 1 / 10000 := by rw [dy_v]; exact hvb
        have h2 := (Rat.cast_le (K := ℝ)).mpr h'
        rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at h2
        exact h2
      linarith
    have hjl := jdef_lower hHp hHpq hm12 hcap
    have hj0 : 0 ≤ jdef (H p) (H q) m := le_trans (by positivity) hjl
    have hjB := bulk_term_of hJq0.le hβ0.le hfe hHq hfHR hjl
    have eB : ((c.Bn : ℚ) : ℝ) = max 0 (1 / 10000 / 2 - ((c.qd : ℚ) : ℝ)) *
        (9 / 40 * ((c.Jq : ℚ) : ℝ) ^ 2 / ((c.fH : ℚ) : ℝ) ^ 2) := by
      unfold NCell.Bn; push_cast; rw [Sq_cast]
    rw [eB]
    rcases le_total (1 / 10000 / 2 - ((c.qd : ℚ) : ℝ)) 0 with hneg | hpos
    · rw [max_eq_left hneg, zero_mul, mul_zero]
      exact mul_nonneg (by linarith [hm.1, hm.2]) hj0
    · rw [max_eq_right hpos]
      have h1 : 1 / 10000 / 2 - ((c.qd : ℚ) : ℝ) ≤ 1 / 10000 / 2 - q := by linarith
      have h2 : 0 ≤ 9 / 40 * ((c.Jq : ℚ) : ℝ) ^ 2 / ((c.fH : ℚ) : ℝ) ^ 2 := by positivity
      calc (q - p) ^ 2 * ((1 / 10000 / 2 - ((c.qd : ℚ) : ℝ)) *
            (9 / 40 * ((c.Jq : ℚ) : ℝ) ^ 2 / ((c.fH : ℚ) : ℝ) ^ 2))
          = (1 / 10000 / 2 - ((c.qd : ℚ) : ℝ)) *
            (9 / 40 * ((c.Jq : ℚ) : ℝ) ^ 2 / ((c.fH : ℚ) : ℝ) ^ 2 * (q - p) ^ 2) := by ring
        _ ≤ (1 / 10000 / 2 - q) * jdef (H p) (H q) m :=
          mul_le_mul h1 hjB (by positivity) (by linarith [hm.2])
  -- stationary point location
  have hden0 : (0 : ℝ) < 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  have hlamR : ((c.lam : ℚ) : ℝ) = ((c.Pmax : ℚ) : ℝ) / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) := by
    unfold NCell.lam; push_cast; rw [Sq_cast]
  have hlam0 : (0 : ℝ) ≤ ((c.lam : ℚ) : ℝ) := by rw [hlamR]; positivity
  have hJp0 : (0 : ℝ) ≤ ((c.Jp : ℚ) : ℝ) := le_trans (J_nonneg hp (by linarith)) hJpR
  have eA : ((c.A0n : ℚ) : ℝ) = ((c.Pmax : ℚ) : ℝ) / 2 *
      (((c.Jp : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) / (2 * ((c.eL : ℚ) : ℝ) * ((c.eL : ℚ) : ℝ))) := by
    unfold NCell.A0n; push_cast; ring
  have hA0n0 : (0 : ℝ) ≤ ((c.A0n : ℚ) : ℝ) := by rw [eA]; positivity
  have hΔ : seamDelta (1 / 10000) (H p) (H q) ys ≤
      (q - p) * ((c.A0n : ℚ) : ℝ) + ((c.lam : ℚ) : ℝ) * ys := by
    have h := seamDelta_le (S := 1 / 10000) (y := ys) (P := ((c.Pmax : ℚ) : ℝ)) hHp hHpq hys0.le
      (by linarith) hPmax0R (fun t ht => hPmaxAll t (le_trans (hXf ys hys0.le hysS) ht.1))
    have hfe2 : H q - H p ≤ ((c.Jp : ℚ) : ℝ) * (q - p) := by
      have h1 := H_sub_le_J hp hpq.le (by linarith)
      have h2 := mul_le_mul_of_nonneg_right hJpR hβ0.le
      linarith
    have hA := a0_bound_of hHp hHpq heL0 heLR hEHR hfe2 hJp0 hβ0.le
    have hA2 : ((c.Pmax : ℚ) : ℝ) / 2 * ((H q ^ 2 - H p ^ 2) / (2 * H p * H q)) ≤
        (q - p) * ((c.A0n : ℚ) : ℝ) := by
      rw [eA]
      have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) / 2)
      linarith
    have hL : ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 1 / 10000 - ys)) ≤ ((c.lam : ℚ) : ℝ) * ys := by
      rw [hlamR]
      have h1 : 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) ≤ 1 - 1 / 10000 - ys := by linarith
      have h2 : ys / (1 - 1 / 10000 - ys) ≤ ys / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) :=
        div_le_div_of_nonneg_left hys0.le hden0 h1
      calc ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 1 / 10000 - ys))
          ≤ ((c.Pmax : ℚ) : ℝ) * (ys / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 hPmax0R
        _ = ((c.Pmax : ℚ) : ℝ) / (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) * ys := by ring
    linarith
  have hxbR : (0 : ℝ) < ((c.xb : ℚ) : ℝ) := by exact_mod_cast hxb
  have hθb : ((c.thb : ℚ) : ℝ) ≤ e8Theta ((c.xb : ℚ) : ℝ) := theta_ge_Slo dxb hxbv hxb le_rfl hbrxb
  have hneedR : (q - p) * ((c.A0n : ℚ) : ℝ) + ((c.lam : ℚ) : ℝ) * (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) <
      ((c.thb : ℚ) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hneed
    push_cast at h
    rw [Sq_cast] at h
    have h2 : (q - p) * ((c.A0n : ℚ) : ℝ) ≤ ((c.A0n : ℚ) : ℝ) * ((c.bhi : ℚ) : ℝ) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hbhi hA0n0
    linarith
  have hdenR' : ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hden
    push_cast at h
    exact h
  have hdenR : ((c.lam : ℚ) : ℝ) * (H p + H q) < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hEHR hlam0
    linarith
  have hyhi : ys ≤ 1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  have hTD : e8Theta (ys / (H p + H q)) = seamDelta (1 / 10000) (H p) (H q) ys := by
    have h := seamD_eq_sub (1 / 10000) (H p) (H q) ys
    rw [hstat] at h
    linarith
  have hyslt : ys / (H p + H q) < ((c.xb : ℚ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 := e8Theta_mono hxbR hcon
    have h2 : ((c.lam : ℚ) : ℝ) * ys ≤ ((c.lam : ℚ) : ℝ) * (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hyhi hlam0
    linarith
  have hxst := xstar_le (S := 1 / 10000) hHp hHq hstat hΔ hys0 hyhi hlam0 hxbR hθb hneedR hdenR
  have hYn : ys ≤ (q - p) * ((c.Yn : ℚ) : ℝ) := by
    have eY : ((c.Yn : ℚ) : ℝ) = ((c.A0n : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) /
        (((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ)) := by
      unfold NCell.Yn; push_cast; ring
    have hdpos : 0 < ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) := by
      linarith
    have hmono := ystar_mono_of (A := (q - p) * ((c.A0n : ℚ) : ℝ))
      (th := ((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ)) (lam := ((c.lam : ℚ) : ℝ))
      (mul_nonneg hβ0.le hA0n0) hE hEHR hlam0 hdpos
    rw [eY]
    have e2 : (q - p) * (((c.A0n : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) /
        (((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ))) =
        (q - p) * ((c.A0n : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ) /
        (((c.thb : ℚ) : ℝ) / ((c.xb : ℚ) : ℝ) - ((c.lam : ℚ) : ℝ) * ((c.EH : ℚ) : ℝ)) := by ring
    rw [e2]
    exact le_trans hxst hmono
  -- slope bound on (0, ys)
  have hM : ∀ t ∈ Ioo 0 ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      ((c.M : ℚ) : ℝ) * ((ys - t) / (H p + H q)) := by
    intro t ht
    have h := theta_slope_small dx2 dh hdhk dh_v hbrx2 (div_pos ht.1 hE)
      (div_le_div_of_nonneg_right ht.2.le hE.le) hyslt.le
    have e : ys / (H p + H q) - t / (H p + H q) = (ys - t) / (H p + H q) := by ring
    rw [e] at h
    exact h
  have hM0R : (0 : ℝ) ≤ ((c.M : ℚ) : ℝ) := by exact_mod_cast hM0
  -- Δ lower bound (for vacuity tests)
  have hΔlo : ((c.Pmin : ℚ) : ℝ) * (((c.Jq : ℚ) : ℝ) * (q - p) / ((c.fH : ℚ) : ℝ)) / 2 ≤
      e8Theta (ys / (H p + H q)) := by
    rw [hTD]
    have h := seamDelta_ge (S := 1 / 10000) (y := ys) (P := ((c.Pmin : ℚ) : ℝ)) hHp hHpq hys0.le
      (by linarith) hPmin0R
      (fun t ht => hPminAll t (le_trans (hXf ys hys0.le hysS) ht.1)
        (by
          rw [eWmax]
          refine le_trans ht.2 ?_
          have h1 : (1 - 1 / 10000 + ys) / (2 * H p) ≤ 1 / (2 * H p) :=
            div_le_div_of_nonneg_right (by linarith) (by linarith)
          have h2 : 1 / (2 * H p) ≤ 1 / (2 * ((c.eL : ℚ) : ℝ)) :=
            div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
          linarith))
    have hlog : ((c.Jq : ℚ) : ℝ) * (q - p) / ((c.fH : ℚ) : ℝ) ≤ Real.log (H q / H p) := by
      have h1 := log_ge_sub_div (show 0 < H q / H p by positivity)
      have e1 : (H q / H p - 1) / (H q / H p) = (H q - H p) / H q := by field_simp
      rw [e1] at h1
      have h2 : ((c.Jq : ℚ) : ℝ) * (q - p) / ((c.fH : ℚ) : ℝ) ≤ (H q - H p) / H q := by
        have h3 : ((c.Jq : ℚ) : ℝ) * (q - p) / ((c.fH : ℚ) : ℝ) ≤ ((c.Jq : ℚ) : ℝ) * (q - p) / H q :=
          div_le_div_of_nonneg_left (mul_nonneg hJq0.le hβ0.le) hHq hfHR
        have h4 : ((c.Jq : ℚ) : ℝ) * (q - p) / H q ≤ (H q - H p) / H q :=
          div_le_div_of_nonneg_right hfe hHq.le
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ((c.Pmin : ℚ) : ℝ) / 2)
    linarith
  exact ⟨hDC, hR, hB, hM, hM0R, hYn, hELR, hEL0, hqqd, hΔlo⟩

set_option maxHeartbeats 1000000 in
/-- Soundness of the case-A N-cell check. -/
theorem ncheckA_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (c : NCell)
    (hc : ncheckA c = true) {p q ys : ℝ}
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (ht0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p)
    (ht1 : q - p ≤ ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p))
    (hpq : p < q) (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    0 ≤ seamCurve (1 / 10000) (H p) (H q) ys := by
  unfold ncheckA at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hcom, hA⟩ := hc
  obtain ⟨ht0nn, ht01, ht1le, hfinal⟩ := of_decide_eq_true hA
  have hcom' := hcom
  unfold ncommon at hcom'
  obtain ⟨-, -, -, -, -, -, -, -, -, hp0pos, -, hp1S, -⟩ := of_decide_eq_true hcom'
  have hp0R : (0 : ℝ) < ((c.p0 : ℚ) : ℝ) := by exact_mod_cast hp0pos
  have hp : 0 < p := lt_of_lt_of_le hp0R hp0
  have hp1SR : ((c.p1 : ℚ) : ℝ) ≤ 1 / 10000 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hp1S
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have ht1R : ((c.t1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast ht1le
  have ht1nn : (0 : ℝ) ≤ ((c.t1 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ c.t1 := le_trans ht0nn ht01.le
    exact_mod_cast this
  have hqS : q ≤ 1 / 10000 / 2 := by
    have h1 : q - p ≤ 1 * (1 / 10000 / 2 - p) :=
      le_trans ht1 (mul_le_mul_of_nonneg_right ht1R (by linarith))
    linarith
  have hbhi : q - p ≤ ((c.bhi : ℚ) : ℝ) := by
    have e : ((c.bhi : ℚ) : ℝ) = ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p0 : ℚ) : ℝ)) := by
      unfold NCell.bhi; push_cast; rw [Sq_cast]
    rw [e]
    exact le_trans ht1 (mul_le_mul_of_nonneg_left (by linarith) ht1nn)
  obtain ⟨hDC, hR, hB, hM, hM0, hYn, hELR, hEL0, -, -⟩ :=
    ncell_facts hdouble c hcom hp0 hp1 (by linarith) hbhi hys0 hysS hstat
  have hcheck : 0 ≤ ((c.DCn : ℚ) : ℝ) + ((c.c1n : ℚ) : ℝ) - ((c.c2 : ℚ) : ℝ) / 2 +
      ((c.Bn : ℚ) : ℝ) - ((c.M : ℚ) : ℝ) * ((c.Yn : ℚ) : ℝ) ^ 2 / (2 * (H p + H q)) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hfinal
    push_cast at h
    have h2 := dip_mono_of (Y := ((c.Yn : ℚ) : ℝ)) hM0 hEL0 hELR
    linarith
  exact seam_master_A (by norm_num) le_rfl hp hpq hqS hys0 hysS hstat hDC hR hB hM hM0 hYn hcheck

end CKLaneP

end


