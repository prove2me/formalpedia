-- Prove2me | Definitions.Def_CK_CKLaneP_SeamTCheck_part00
-- name    : CK_CKLaneP_SeamTCheck_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T09:54:55.529031+00:00
-- url     : https://prove2.me/theorems/1643e0db-22fb-45ff-bfc4-29c1237dbbcd
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamTCheck (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamTCheck (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamTCheck (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamTCheck (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamTCheck (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneP_SeamWBase
import Definitions.Def_CK_CKLaneP_ThetaLip
/-
Lane P — the small-scale (T) seam lemma: all `(p, q)` with `q ≤ qT`, in κ-cells `κ = H p/H q`.

Uniform in the scale: `f = H q ≤ fT := Hhi(nqT)`, `E = f(1+κ) ≤ fT(1+κ1)`, contacts of all large
arguments `≤ vb` (`X ≥ (1−2S)/(2fT)`), `Pmin0 = (1−2vb)/((1+vb/2)³ log2⁺)` (no lower bracket).
Base = bulk only (DC ≥ 0 by the owner, right fiber ≥ 0 by `rightFiber_mono`):
    bulk ≥ (S/2 − qT)·max(0, Jv),  Jv = max(9/40 (1−κ1)², Pmin0·log((1+κ1)²/(4κ1)) − (Pmax−Pmin0)·log(2/(1+κ0))).
Kinds: 0 = middle cell (dip ≤ M A0² E_T/(2 D_T²), A0 = (Pmax/2) log(1/κ0));
       1 = last cell `[κ0, 1]` normalized by `(1−κ)²`;
       2 = first cell `(0, κ1]` with the slope-gap dip bound `dip ≤ S·(1 + 1/L_K)/log2⁻`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

structure TCell where
  qT : ℚ
  nqT : ℕ
  k0 : ℚ
  k1 : ℚ
  nvb : ℕ
  xb : ℚ
  nxb : ℕ
  nx2 : ℕ
  xK : ℚ
  nxK : ℕ
  nvK : ℕ
deriving Repr

namespace TCell

def fT (c : TCell) : ℚ := (dy c.nqT).Hhi
def ET (c : TCell) : ℚ := c.fT * (1 + c.k1)
def vb (c : TCell) : ℚ := (dy c.nvb).v
def Xmin (c : TCell) : ℚ := (1 - 2 * Sq) / (2 * c.fT)
def Pmax (c : TCell) : ℚ := PmaxQ (dy c.nvb)
def Pmin0 (c : TCell) : ℚ := (1 - 2 * c.vb) / ((1 + c.vb / 2) ^ 3 * L2hiD)
def lam (c : TCell) : ℚ := c.Pmax / (1 - 2 * Sq)
def thb (c : TCell) : ℚ := (dy c.nxb).Slo
def M (c : TCell) : ℚ := Mof c.xb c.nx2
def Jv (c : TCell) : ℚ :=
  max (9 / 40 * (1 - c.k1) ^ 2)
    (c.Pmin0 * logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) - (c.Pmax - c.Pmin0) * logUpQ (2 / (1 + c.k0)))
def B0 (c : TCell) : ℚ := (Sq / 2 - c.qT) * max 0 c.Jv
def A0 (c : TCell) : ℚ := c.Pmax / 2 * logUpQ (1 / c.k0)
def DT (c : TCell) : ℚ := c.thb / c.xb - c.lam * c.ET

end TCell

/-- Conditions shared by all T-cells. -/
def tcommon (c : TCell) : Bool := decide (
  VD.okDy 60 c.nqT = true ∧ VD.okDy 60 c.nvb = true ∧ VD.okDy 60 c.nxb = true ∧
  VD.okDy 60 c.nx2 = true ∧
  0 < c.qT ∧ c.qT ≤ dyq c.nqT ∧ c.qT < Sq / 2 ∧ 0 < c.fT ∧
  0 ≤ c.k0 ∧ c.k0 < c.k1 ∧ c.k1 ≤ 1 ∧
  dyq c.nvb ≤ 1 / 10000 ∧ 4 ≤ (dy c.nvb).a1 ∧
  0 < c.Xmin ∧ 1 - 2 * (dy c.nvb).v ≤ 2 * c.Xmin * (dy c.nvb).Hlo ∧
  0 < c.xb ∧ (dy c.nxb).v < 1 / 2 ∧ 1 - 2 * (dy c.nxb).v ≤ 2 * c.xb * (dy c.nxb).Hlo ∧
  2 * c.xb * (dy c.nx2).Hhi ≤ 1 - 2 * (dy c.nx2).v ∧ 0 < (dy dhN).kapLo ∧ 0 ≤ c.M ∧
  0 ≤ c.Pmin0 ∧ c.Pmin0 ≤ c.Pmax ∧ 0 < c.k1 ∧
  1 ≤ ⌊(1 + c.k1) ^ 2 / (4 * c.k1) * 2 ^ 60⌋₊)

/-- T-cell check by kind. -/
def tcheck (kind : ℕ) (c : TCell) : Bool :=
  tcommon c && (match kind with
  | 0 => decide (0 < c.k0 ∧ c.A0 + c.lam * Sq < c.thb ∧ 0 < c.DT ∧
      0 ≤ c.B0 - c.M * c.A0 ^ 2 * c.ET / (2 * c.DT ^ 2))
  | 1 => decide (0 < c.k0 ∧ c.k1 = 1 ∧
      c.Pmax / 2 * ((1 - c.k0) / c.k0) + c.lam * Sq < c.thb ∧ 0 < c.DT ∧
      0 ≤ (Sq / 2 - c.qT) * (9 / 40) - c.M * (c.Pmax / 2 / c.k0) ^ 2 * c.ET / (2 * c.DT ^ 2))
  | _ => decide (VD.okDy 60 c.nxK = true ∧ VD.okDy 60 c.nvK = true ∧ 0 < c.xK ∧
      2 * c.xK * (dy c.nxK).Hhi ≤ 1 - 2 * (dy c.nxK).v ∧ 0 < (dy c.nxK).a1 + (dy c.nxK).a2 ∧
      (dy c.nxK).v < 1 / 2 ∧
      1 ≤ ⌊1 / c.k1 * 2 ^ 60⌋₊ ∧ (dy c.nxK).Shi < c.Pmin0 / 2 * logDnQ (1 / c.k1) ∧
      1 - 2 * (dy c.nvK).v ≤ 2 * c.xK * (dy c.nvK).Hlo ∧ 0 < (dy c.nvK).a1 ∧
      0 ≤ c.B0 - Sq * (1 + 1 / (dy c.nvK).a1) / L2loD))

set_option maxHeartbeats 2000000 in
/-- Real consequences shared by the T-cells. -/
theorem tcell_facts (c : TCell) (hc : tcommon c = true) {p q ys : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqT : q ≤ ((c.qT : ℚ) : ℝ))
    (hk0 : ((c.k0 : ℚ) : ℝ) ≤ H p / H q) (hk1 : H p / H q ≤ ((c.k1 : ℚ) : ℝ))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p) :
    0 < H p ∧ H p ≤ H q ∧ H p + H q ≤ ((c.ET : ℚ) : ℝ) ∧ q ≤ 1 / 10000 / 2 ∧
    (∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x → profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ)) ∧
    (∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x → ((c.Pmin0 : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1)) ∧
    ((c.Xmin : ℚ) : ℝ) ≤ (1 - 1 / 10000 - ys) / (2 * H q) ∧
    (∀ m ∈ Icc q (1 / 10000 / 2), ((c.Xmin : ℚ) : ℝ) ≤ (1 - 2 * m) / (2 * H q)) ∧
    radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 ≤ 1 / 10000 ∧
    0 ≤ ((c.Pmin0 : ℚ) : ℝ) ∧ ((c.Pmin0 : ℚ) : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by
  unfold tcommon at hc
  obtain ⟨okT, okvb, okxb, okx2, hqT0, hqTd, hqTS, hfT, hk00, hk01, hk11, hvb, hvba1, hXmin, hbrX,
    -, -, -, -, -, -, hPmin00, hPmm, -, -⟩ := of_decide_eq_true hc
  have dT := dy_sound okT
  have dvb := dy_sound okvb
  have hq0 : 0 < q := hp.trans hpq
  have hqTSR : ((c.qT : ℚ) : ℝ) < 1 / 10000 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqTS
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have hqS : q ≤ 1 / 10000 / 2 := by linarith
  have hHmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → H a ≤ H b :=
    fun ha hab hb => H_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, hb⟩ hab
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q := hHmono hp.le hpq.le (by linarith)
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hqTdR : ((c.qT : ℚ) : ℝ) ≤ ((dy c.nqT).v : ℝ) := by rw [dy_v]; exact_mod_cast hqTd
  have hvTh : ((dy c.nqT).v : ℝ) ≤ 1 / 2 := VD.cast_le_half dT.2.1
  have hfTR : H q ≤ ((c.fT : ℚ) : ℝ) :=
    le_trans (hHmono hq0.le (hqT.trans hqTdR) hvTh) (VD.le_Hhi dT)
  have hk1R : ((c.k1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hk11
  have hET : H p + H q ≤ ((c.ET : ℚ) : ℝ) := by
    have e : ((c.ET : ℚ) : ℝ) = ((c.fT : ℚ) : ℝ) * (1 + ((c.k1 : ℚ) : ℝ)) := by
      unfold TCell.ET; push_cast; ring
    rw [e]
    have h1 : H p ≤ ((c.k1 : ℚ) : ℝ) * H q := by
      rw [div_le_iff₀ hHq] at hk1; linarith
    have h2 : ((c.k1 : ℚ) : ℝ) * H q ≤ ((c.k1 : ℚ) : ℝ) * ((c.fT : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hfTR (by linarith [div_pos hHp hHq])
    nlinarith
  have hvbv : (dy c.nvb).v ≤ 1 / 1000 := by rw [dy_v]; exact le_trans hvb (by norm_num)
  have hvbR : ((dy c.nvb).v : ℝ) ≤ 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).mpr hvbv
    rw [show ((1 / 1000 : ℚ) : ℝ) = 1 / 1000 by norm_num] at this
    exact this
  have hL4 : (4 : ℝ) ≤ -Real.log ((dy c.nvb).v : ℝ) :=
    le_trans (by exact_mod_cast hvba1) dvb.2.2.1
  have hPmaxAll : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x →
      profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx
    exact PmaxQ_sound dvb hvbv hvba1 (radialContact_pos (by linarith) one_pos)
      (contact_le_of_bracket dvb hXmin hbrX hx)
  have hPminAll : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x →
      ((c.Pmin0 : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx
    have hcb := contact_le_of_bracket dvb hXmin hbrX hx
    have h := profile_ge_bracket0 (radialContact_pos (by linarith) one_pos) hcb hvbR hL4
    have hl2 := log2D_bounds
    have e : ((c.Pmin0 : ℚ) : ℝ) = (1 - 2 * ((dy c.nvb).v : ℝ)) /
        ((1 + ((dy c.nvb).v : ℝ) / 2) ^ 3 * ((L2hiD : ℚ) : ℝ)) := by
      unfold TCell.Pmin0 TCell.vb; push_cast; ring
    rw [e]
    have hvb0 : (0 : ℝ) < ((dy c.nvb).v : ℝ) := by exact_mod_cast dvb.1
    refine le_trans ?_ h
    apply div_le_div_of_nonneg_left (by linarith) (by have := log_two_pos; positivity)
    exact mul_le_mul_of_nonneg_left hl2.2 (by positivity)
  have eX : ((c.Xmin : ℚ) : ℝ) = (1 - 2 * (1 / 10000)) / (2 * ((c.fT : ℚ) : ℝ)) := by
    unfold TCell.Xmin; push_cast; rw [Sq_cast]
  have hXf : ((c.Xmin : ℚ) : ℝ) ≤ (1 - 1 / 10000 - ys) / (2 * H q) := by
    rw [eX]; exact xmin_le_of hHq hfTR (by norm_num) (by linarith)
  have hXm : ∀ m ∈ Icc q (1 / 10000 / 2), ((c.Xmin : ℚ) : ℝ) ≤ (1 - 2 * m) / (2 * H q) := by
    intro m hm
    rw [eX]; exact xmin_le_of hHq hfTR (by norm_num) (by linarith [hm.2])
  have hcX : radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 ≤ 1 / 10000 := by
    have hcb := contact_le_of_bracket dvb hXmin hbrX (le_refl ((c.Xmin : ℚ) : ℝ))
    have : ((dy c.nvb).v : ℝ) ≤ 1 / 10000 := by
      have h' : ((dy c.nvb).v : ℚ) ≤ 1 / 10000 := by rw [dy_v]; exact hvb
      have h2 := (Rat.cast_le (K := ℝ)).mpr h'
      rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at h2
      exact h2
    linarith
  have hPmin0R : (0 : ℝ) ≤ ((c.Pmin0 : ℚ) : ℝ) := by exact_mod_cast hPmin00
  have hPmmR : ((c.Pmin0 : ℚ) : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by exact_mod_cast hPmm
  exact ⟨hHp, hHpq, hET, hqS, hPmaxAll, hPminAll, hXf, hXm, hcX, hPmin0R, hPmmR⟩

/-- Bulk lower bound for T-cells: `jdef ≥ max(0, Jv)` on `[q, S/2]`. -/
theorem tcell_bulk (c : TCell) (hc : tcommon c = true) {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqT : q ≤ ((c.qT : ℚ) : ℝ))
    (hk0 : ((c.k0 : ℚ) : ℝ) ≤ H p / H q) (hk1 : H p / H q ≤ ((c.k1 : ℚ) : ℝ)) :
    ∀ m ∈ Icc q (1 / 10000 / 2), max 0 ((c.Jv : ℚ) : ℝ) ≤ jdef (H p) (H q) m := by
  have hpS : p < 1 / 10000 / 2 := by
    have hc' := hc
    unfold tcommon at hc'
    obtain ⟨-, -, -, -, -, -, hqTS, -⟩ := of_decide_eq_true hc'
    have := (Rat.cast_lt (K := ℝ)).mpr hqTS
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    linarith
  obtain ⟨hHp, hHpq, -, hqS, hPmaxAll, hPminAll, -, hXm, hcX, hPmin0R, hPmmR⟩ :=
    tcell_facts c hc hp hpq hqT hk0 hk1 (ys := (1 / 10000 - 2 * p) / 2) (by linarith) (by linarith)
  have hc' := hc
  unfold tcommon at hc'
  obtain ⟨-, -, -, -, -, -, -, -, hk00, hk01, hk11, -, -, -, -, -, -, -, -, -, -, -, -, hk1pos,
    hfl⟩ := of_decide_eq_true hc'
  intro m hm
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hm12 : m < 1 / 2 := by linarith [hm.2]
  have hZ : 0 < 1 - 2 * m := by linarith
  have hXZ : ∀ x : ℝ, (1 - 2 * m) / (2 * H q) ≤ x → ((c.Xmin : ℚ) : ℝ) ≤ x :=
    fun x hx => le_trans (hXm m hm) hx
  have hcap : radialContact ((1 - 2 * m) / H q) 1 ≤ 1 / 10000 := by
    have e : (1 - 2 * m) / H q = 2 * ((1 - 2 * m) / (2 * H q)) := by field_simp
    rw [e]
    have hmono : radialContact (2 * ((1 - 2 * m) / (2 * H q))) 1 ≤
        radialContact (2 * ((c.Xmin : ℚ) : ℝ)) 1 := by
      have hX0 : (0 : ℝ) < ((c.Xmin : ℚ) : ℝ) := by
        have hc2 := hc
        unfold tcommon at hc2
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hX, -⟩ := of_decide_eq_true hc2
        exact_mod_cast hX
      apply (radialContact_le_iff_ratio (by positivity) (by positivity) one_pos one_pos).2
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [hXm m hm]
    linarith
  have hjl := jdef_lower hHp hHpq hm12 hcap
  have hj0 : 0 ≤ jdef (H p) (H q) m := le_trans (by positivity) hjl
  set κ := H p / H q with hκd
  have hkpos : 0 < κ := div_pos hHp hHq
  have hk1R : ((c.k1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hk11
  have hj1 : 9 / 40 * (1 - ((c.k1 : ℚ) : ℝ)) ^ 2 ≤ jdef (H p) (H q) m := by
    refine le_trans ?_ hjl
    have e : 9 / 10 * (H q - H p) ^ 2 / (4 * H q ^ 2) = 9 / 40 * (1 - κ) ^ 2 := by
      rw [hκd]; field_simp; ring
    rw [e]
    have h1 : 0 ≤ 1 - ((c.k1 : ℚ) : ℝ) := by linarith
    have h3 := pow_le_pow_left₀ h1 (show 1 - ((c.k1 : ℚ) : ℝ) ≤ 1 - κ by linarith) 2
    linarith
  have hj2 : ((c.Pmin0 : ℚ) : ℝ) * ((logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) : ℚ) : ℝ) -
      (((c.Pmax : ℚ) : ℝ) - ((c.Pmin0 : ℚ) : ℝ)) * ((logUpQ (2 / (1 + c.k0)) : ℚ) : ℝ) ≤
      jdef (H p) (H q) m := by
    have hjg := jdef_ge_log (Pm := ((c.Pmin0 : ℚ) : ℝ)) (PM := ((c.Pmax : ℚ) : ℝ)) hHp hHpq hm12
      (fun x hx => hPminAll x (hXZ x (le_trans (div_le_div_of_nonneg_left hZ.le hE
        (by linarith)) hx.1)))
      (fun x hx => hPmaxAll x (hXZ x hx.1))
    have hE2e : (H p + H q) / (2 * H p) = (1 + κ) / (2 * κ) := by
      rw [hκd]; field_simp; ring
    have h2fE : 2 * H q / (H p + H q) = 2 / (1 + κ) := by
      rw [hκd]; field_simp; ring
    rw [hE2e, h2fE] at hjg
    have hsplit : Real.log ((1 + κ) / (2 * κ)) = Real.log ((1 + κ) ^ 2 / (4 * κ)) +
        Real.log (2 / (1 + κ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    rw [hsplit] at hjg
    have hlog1 : ((logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) : ℚ) : ℝ) ≤
        Real.log ((1 + κ) ^ 2 / (4 * κ)) := by
      refine le_trans (logDnQ_sound hfl) ?_
      have hk1p : (0 : ℝ) < ((c.k1 : ℚ) : ℝ) := by exact_mod_cast hk1pos
      apply Real.log_le_log (by push_cast; positivity)
      push_cast
      exact kappa_ratio_mono hkpos hk1 hk1R
    have hk0R : (0 : ℝ) ≤ ((c.k0 : ℚ) : ℝ) := by exact_mod_cast hk00
    have hlog2 : Real.log (2 / (1 + κ)) ≤ ((logUpQ (2 / (1 + c.k0)) : ℚ) : ℝ) := by
      have hpos : (0 : ℚ) < 2 / (1 + c.k0) := by
        have : (0 : ℚ) ≤ c.k0 := hk00
        positivity
      refine le_trans (Real.log_le_log (by positivity) ?_) (by
        have := logUpQ_sound hpos
        push_cast at this
        exact this)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hPd : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) - ((c.Pmin0 : ℚ) : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog1 hPmin0R, mul_le_mul_of_nonneg_left hlog2 hPd]
  have eJv : ((c.Jv : ℚ) : ℝ) = max (9 / 40 * (1 - ((c.k1 : ℚ) : ℝ)) ^ 2)
      (((c.Pmin0 : ℚ) : ℝ) * ((logDnQ ((1 + c.k1) ^ 2 / (4 * c.k1)) : ℚ) : ℝ) -
        (((c.Pmax : ℚ) : ℝ) - ((c.Pmin0 : ℚ) : ℝ)) * ((logUpQ (2 / (1 + c.k0)) : ℚ) : ℝ)) := by
    unfold TCell.Jv; push_cast; ring_nf
  rw [eJv]
  exact max_le hj0 (max_le hj1 hj2)


end CKLaneP


