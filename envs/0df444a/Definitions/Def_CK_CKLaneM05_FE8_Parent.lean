-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_Parent
-- name    : CK_CKLaneM05_FE8_Parent
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:52:13.674473+00:00
-- url     : https://prove2.me/theorems/fe3f21e7-0644-43a6-ad25-a3599f909696
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.Parent` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.Parent` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.Parent` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.Parent (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/Parent.lean)

import Definitions.Def_CK_CKLaneM05_FE8_Base

-- ===== source module CKLaneM05.FE8.Parent =====
section

/-!
# Lane M05 / FE8: parent-dominance kernel on archived `(a, b, t)` boxes (`phi_parent`)

Archive (`FULL_ENTROPY_COVER.py`, owner `phi_parent`; PROOF.md §10): with `q = 1 - a - b`,
`eta(E_+) - F(q_+, E_+) - P(I_+) ≥ 0` (common feasible endpoint) or the independent interval
`eta(E) - F(q, E) - P(I) ≥ 0` certifies `psi(m, E) ≤ phi(m, E)` on the whole box.

`parentCheck B w = true` binds: box sanity (`0 < a0 ≤ a1 ≤ 1/2`, `0 < b0 ≤ b1 ≤ 1/2`,
`0 ≤ t0 ≤ t1 ≤ 1`), fixed-point log enclosures (`CKLaneE.FP.ptOk`) at `a0, a1, b0, b1, m_lo, m_hi` and
at the witness points `u0, v2, u1`, and the rational inequalities
* `E_lo = EMIN + t0 (C0lo - EMIN) > 0`, `E_up = EMIN + t1 (C0hi - EMIN)`, `q_hi = 1 - 2 m_lo > 0`;
* mode `true` (common endpoint): `E_up < Hlo(m_lo)`, contact `q_hi Hhi(v2) ≤ E_up (1 - 2 v2)`;
  mode `false` (decoupled): contact `q_hi Hhi(v2) ≤ E_lo (1 - 2 v2)`;
* `E_up ≤ Hlo(u0)`, `Hhi(u1) ≤ E_lo + 1 - Hhi(m_hi)`,
  `(1-2u1) Jh(u1) ≤ (1-2u0) Jl(u0) - q_hi Jh(v2)`.

Soundness (`parentCheck_sound`): `ParentBox B` (psi ≤ phi at the parent for every law in the box).
Mode `true` uses `GeneralCK.phi_entropy_convexOn` + `phi_at_entropy_cap` (via `convex_step`);
mode `false` uses only monotonicity of `eta` and of the radial contact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

open GeneralCK CKLaneE.FP

/-- Parent-dominance witness: three rational points and the mode. -/
structure PW where
  u0 : ℚ
  v2 : ℚ
  u1 : ℚ
  mode : Bool
  deriving Repr

def mLo (B : CKLaneD.Box) : ℚ := (B.alo + B.blo) / 2
def mHi (B : CKLaneD.Box) : ℚ := (B.ahi + B.bhi) / 2
def C0lo (B : CKLaneD.Box) : ℚ := (Hlo B.alo + Hlo B.blo) / 2
def C0hi (B : CKLaneD.Box) : ℚ := (Hhi B.ahi + Hhi B.bhi) / 2
def Eup (B : CKLaneD.Box) : ℚ := CKLaneD.EMIN + B.t1 * (C0hi B - CKLaneD.EMIN)
def Elo (B : CKLaneD.Box) : ℚ := CKLaneD.EMIN + B.t0 * (C0lo B - CKLaneD.EMIN)
def qHi (B : CKLaneD.Box) : ℚ := 1 - 2 * mLo B
def Eref (B : CKLaneD.Box) (w : PW) : ℚ := if w.mode then Eup B else Elo B

def boxSane (B : CKLaneD.Box) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ B.ahi ≤ 1 / 2 ∧ 0 < B.blo ∧ B.blo ≤ B.bhi ∧ B.bhi ≤ 1 / 2 ∧
    0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1)

def boxPts (B : CKLaneD.Box) : Bool :=
  ptOk B.alo && ptOk B.ahi && ptOk B.blo && ptOk B.bhi && ptOk (mLo B) && ptOk (mHi B)

def parentIneq (B : CKLaneD.Box) (w : PW) : Bool :=
  decide (0 < Elo B ∧ 0 < qHi B ∧ w.u0 < 1 / 2 ∧ w.v2 < 1 / 2 ∧ w.u1 < 1 / 2 ∧
    Eup B ≤ Hlo w.u0 ∧ 0 ≤ lamLo w.u0 ∧
    qHi B * Hhi w.v2 ≤ Eref B w * (1 - 2 * w.v2) ∧ 0 ≤ lamHi w.v2 ∧
    Hhi w.u1 ≤ Elo B + 1 - Hhi (mHi B) ∧
    (1 - 2 * w.u1) * Jh w.u1 ≤ (1 - 2 * w.u0) * Jl w.u0 - qHi B * Jh w.v2) &&
  (!w.mode || decide (Eup B < Hlo (mLo B)))

def parentCheck (B : CKLaneD.Box) (w : PW) : Bool :=
  boxSane B && boxPts B && ptOk w.u0 && ptOk w.v2 && ptOk w.u1 && parentIneq B w

/-! ## Box enclosures shared by the FE8 kernels -/

/-- Real-variable consequences of a sane box with certified corner points, for a law in the box. -/
theorem box_facts {B : CKLaneD.Box} (hs : boxSane B = true) (hp : boxPts B = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : CKLaneD.InBox B μ.a μ.b μ.meanEntropy) :
    ((mLo B : ℚ) : ℝ) ≤ μ.midpoint ∧ μ.midpoint ≤ ((mHi B : ℚ) : ℝ) ∧
    ((mHi B : ℚ) : ℝ) ≤ 1 / 2 ∧ 0 < μ.midpoint ∧
    ((Hlo (mLo B) : ℚ) : ℝ) ≤ H μ.midpoint ∧ H μ.midpoint ≤ ((Hhi (mHi B) : ℚ) : ℝ) ∧
    ((Elo B : ℚ) : ℝ) ≤ μ.meanEntropy ∧ μ.meanEntropy ≤ ((Eup B : ℚ) : ℝ) ∧
    μ.meanEntropy ≤ H μ.midpoint ∧ 0 < μ.meanEntropy ∧
    ((qHi B : ℚ) : ℝ) = 1 - 2 * ((mLo B : ℚ) : ℝ) := by
  simp only [boxSane, decide_eq_true_eq] at hs
  obtain ⟨sa0, sa1, sa2, sb0, sb1, sb2, st0, st1, st2⟩ := hs
  simp only [boxPts, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨pa0, pa1⟩, pb0⟩, pb1⟩, pm0⟩, pm1⟩ := hp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hin
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have hm_def : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  have c_mLo : ((mLo B : ℚ) : ℝ) = ((B.alo : ℚ) : ℝ) / 2 + ((B.blo : ℚ) : ℝ) / 2 := by
    unfold mLo; push_cast; ring
  have c_mHi : ((mHi B : ℚ) : ℝ) = ((B.ahi : ℚ) : ℝ) / 2 + ((B.bhi : ℚ) : ℝ) / 2 := by
    unfold mHi; push_cast; ring
  have rA2 : ((B.ahi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr sa2; push_cast at h; exact h
  have rB2 : ((B.bhi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr sb2; push_cast at h; exact h
  have rA0 : (0 : ℝ) < ((B.alo : ℚ) : ℝ) := by exact_mod_cast sa0
  have rB0 : (0 : ℝ) < ((B.blo : ℚ) : ℝ) := by exact_mod_cast sb0
  have rt0 : (0 : ℝ) ≤ ((B.t0 : ℚ) : ℝ) := by exact_mod_cast st0
  have rt1 : (0 : ℝ) ≤ ((B.t1 : ℚ) : ℝ) := by exact_mod_cast st0.trans st1
  have hmLo : ((mLo B : ℚ) : ℝ) ≤ μ.midpoint := by rw [c_mLo, hm_def]; linarith
  have hmHi : μ.midpoint ≤ ((mHi B : ℚ) : ℝ) := by rw [c_mHi, hm_def]; linarith
  have hmHh : ((mHi B : ℚ) : ℝ) ≤ 1 / 2 := by rw [c_mHi]; linarith
  have hm0 : 0 < μ.midpoint := by rw [hm_def]; linarith
  have hmLo0 : (0 : ℝ) ≤ ((mLo B : ℚ) : ℝ) := by rw [c_mLo]; linarith
  have hmh : μ.midpoint ≤ 1 / 2 := hmHi.trans hmHh
  obtain ⟨HmL, _⟩ := H_bounds pm0
  obtain ⟨_, HmH⟩ := H_bounds pm1
  obtain ⟨HA0, _⟩ := H_bounds pa0
  obtain ⟨_, HA1⟩ := H_bounds pa1
  obtain ⟨HB0, _⟩ := H_bounds pb0
  obtain ⟨_, HB1⟩ := H_bounds pb1
  have hHmL : ((Hlo (mLo B) : ℚ) : ℝ) ≤ H μ.midpoint := HmL.trans (H_le_H hmLo0 hmLo hmh)
  have hHmH : H μ.midpoint ≤ ((Hhi (mHi B) : ℚ) : ℝ) := (H_le_H hm0.le hmHi hmHh).trans HmH
  have ha2 : μ.a ≤ 1 / 2 := h2.trans rA2
  have hb2 : μ.b ≤ 1 / 2 := h4.trans rB2
  have hHa0 : ((Hlo B.alo : ℚ) : ℝ) ≤ H μ.a := HA0.trans (H_le_H rA0.le h1 ha2)
  have hHa1 : H μ.a ≤ ((Hhi B.ahi : ℚ) : ℝ) := (H_le_H ha0.le h2 rA2).trans HA1
  have hHb0 : ((Hlo B.blo : ℚ) : ℝ) ≤ H μ.b := HB0.trans (H_le_H rB0.le h3 hb2)
  have hHb1 : H μ.b ≤ ((Hhi B.bhi : ℚ) : ℝ) := (H_le_H hb0.le h4 rB2).trans HB1
  have c_C0lo : ((C0lo B : ℚ) : ℝ) = (((Hlo B.alo : ℚ) : ℝ) + ((Hlo B.blo : ℚ) : ℝ)) / 2 := by
    unfold C0lo; push_cast; ring
  have c_C0hi : ((C0hi B : ℚ) : ℝ) = (((Hhi B.ahi : ℚ) : ℝ) + ((Hhi B.bhi : ℚ) : ℝ)) / 2 := by
    unfold C0hi; push_cast; ring
  have c_Elo : ((Elo B : ℚ) : ℝ) = (CKLaneD.EMIN : ℝ) + ((B.t0 : ℚ) : ℝ) *
      (((C0lo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) := by unfold Elo; push_cast; ring
  have c_Eup : ((Eup B : ℚ) : ℝ) = (CKLaneD.EMIN : ℝ) + ((B.t1 : ℚ) : ℝ) *
      (((C0hi B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) := by unfold Eup; push_cast; ring
  have hElo : ((Elo B : ℚ) : ℝ) ≤ μ.meanEntropy := by
    rw [c_Elo]
    have hC : ((C0lo B : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by rw [c_C0lo]; linarith
    have := mul_le_mul_of_nonneg_left (show ((C0lo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ) ≤
      (H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ) by linarith) rt0
    linarith
  have hEup : μ.meanEntropy ≤ ((Eup B : ℚ) : ℝ) := by
    rw [c_Eup]
    have hC : (H μ.a + H μ.b) / 2 ≤ ((C0hi B : ℚ) : ℝ) := by rw [c_C0hi]; linarith
    have := mul_le_mul_of_nonneg_left (show (H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ) ≤
      ((C0hi B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ) by linarith) rt1
    linarith
  have hEC : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
  have hCm : (H μ.a + H μ.b) / 2 ≤ H μ.midpoint := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop at this
    linarith
  have hE0 : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  have c_qHi : ((qHi B : ℚ) : ℝ) = 1 - 2 * ((mLo B : ℚ) : ℝ) := by unfold qHi; push_cast; ring
  exact ⟨hmLo, hmHi, hmHh, hm0, hHmL, hHmH, hElo, hEup, hEC.trans hCm, hE0, c_qHi⟩

/-! ## Soundness -/

set_option maxHeartbeats 2000000 in
theorem parentCheck_sound {B : CKLaneD.Box} {w : PW} (hw : parentCheck B w = true) :
    ParentBox B := by
  intro k μ hin
  simp only [parentCheck, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨hs, hp⟩, pu0⟩, pv2⟩, pu1⟩, hineq⟩ := hw
  obtain ⟨hmLo, hmHi, hmHh, hm0, hHmL, hHmH, hElo, hEup, hEm, hE0, c_qHi⟩ :=
    box_facts hs hp μ hin
  simp only [parentIneq, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hineq
  obtain ⟨⟨cElo, cqHi, cu0, cv2, cu1, ceta, clam0, ccont, clam2, cpsi, cfin⟩, cmode⟩ := hineq
  have hmh : μ.midpoint ≤ 1 / 2 := hmHi.trans hmHh
  have cast_lt_half : ∀ {x : ℚ}, x < 1 / 2 → (x : ℝ) < 1 / 2 := by
    intro x hx
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    push_cast at h; linarith
  have hu0R := cast_lt_half cu0
  have hv2R := cast_lt_half cv2
  have hu1R := cast_lt_half cu1
  have hqHi_pos : (0 : ℝ) < ((qHi B : ℚ) : ℝ) := by exact_mod_cast cqHi
  have hq_eq : |1 - 2 * μ.midpoint| = 1 - 2 * μ.midpoint := abs_of_nonneg (by linarith)
  have hq_le : |1 - 2 * μ.midpoint| ≤ ((qHi B : ℚ) : ℝ) := by rw [hq_eq, c_qHi]; linarith
  have hEloPos : (0 : ℝ) < ((Elo B : ℚ) : ℝ) := by exact_mod_cast cElo
  -- psi side
  have i3 : psi μ.midpoint μ.meanEntropy ≤ (1 - 2 * (w.u1 : ℝ)) * ((Jh w.u1 : ℚ) : ℝ) := by
    obtain ⟨_, Hu1⟩ := H_bounds pu1
    have h := (Rat.cast_le (K := ℝ)).mpr cpsi
    push_cast at h
    unfold psi
    apply eta_le_of_pt (by linarith) pu1 hu1R
    linarith
  have hfin : (1 - 2 * (w.u1 : ℝ)) * ((Jh w.u1 : ℚ) : ℝ) ≤
      (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) -
        ((qHi B : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr cfin
    push_cast at h
    exact h
  have hpsi0 : 0 ≤ (1 - 2 * (w.u1 : ℝ)) * ((Jh w.u1 : ℚ) : ℝ) := by
    have hu1p : (0 : ℝ) < w.u1 := by exact_mod_cast (ptOk_pos pu1).1
    have hJ0 := J_nonneg hu1p hu1R.le
    have hJh := le_Jh pu1 hu1R.le
    have : (0 : ℝ) ≤ 1 - 2 * (w.u1 : ℝ) := by linarith
    exact mul_nonneg this (hJ0.trans hJh)
  obtain ⟨Hu0, _⟩ := H_bounds pu0
  obtain ⟨_, Hv2⟩ := H_bounds pv2
  have hEupU0 : ((Eup B : ℚ) : ℝ) ≤ H (w.u0 : ℝ) :=
    ((Rat.cast_le (K := ℝ)).mpr ceta).trans Hu0
  have hcontR : ((qHi B : ℚ) : ℝ) * H (w.v2 : ℝ) ≤
      ((Eref B w : ℚ) : ℝ) * (1 - 2 * (w.v2 : ℝ)) := by
    have h := (Rat.cast_le (K := ℝ)).mpr ccont
    push_cast at h
    exact (mul_le_mul_of_nonneg_left Hv2 hqHi_pos.le).trans h
  cases hmode : w.mode with
  | false =>
    -- decoupled: eta(E) ≥ eta(H u0), F(q,E) ≤ F(q_hi, E_lo)-contact bound
    have hEref : ((Eref B w : ℚ) : ℝ) = ((Elo B : ℚ) : ℝ) := by simp [Eref, hmode]
    rw [hEref] at hcontR
    have hcontE : ((qHi B : ℚ) : ℝ) * H (w.v2 : ℝ) ≤ μ.meanEntropy * (1 - 2 * (w.v2 : ℝ)) :=
      hcontR.trans (mul_le_mul_of_nonneg_right hElo (by linarith))
    have i1 : (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) ≤ eta μ.meanEntropy :=
      eta_ge_of_pt hE0 pu0 hu0R (hEup.trans hEupU0) clam0
    have i2 : F |1 - 2 * μ.midpoint| μ.meanEntropy ≤
        ((qHi B : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) :=
      F_le_of_contact (abs_nonneg _) hq_le hqHi_pos hE0 pv2 hv2R hcontE clam2
    have : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy := by
      unfold phi; linarith
    exact this
  | true =>
    have hEref : ((Eref B w : ℚ) : ℝ) = ((Eup B : ℚ) : ℝ) := by simp [Eref, hmode]
    rw [hEref] at hcontR
    have cfeas : Eup B < Hlo (mLo B) := cmode.resolve_left (by simp [hmode])
    have hEupPos : (0 : ℝ) < ((Eup B : ℚ) : ℝ) := hE0.trans_le hEup
    have hEup_lt : ((Eup B : ℚ) : ℝ) < H μ.midpoint :=
      ((Rat.cast_lt (K := ℝ)).mpr cfeas).trans_le hHmL
    have i1 : (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) ≤ eta ((Eup B : ℚ) : ℝ) :=
      eta_ge_of_pt hEupPos pu0 hu0R hEupU0 clam0
    have i2 : F |1 - 2 * μ.midpoint| ((Eup B : ℚ) : ℝ) ≤
        ((qHi B : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) :=
      F_le_of_contact (abs_nonneg _) hq_le hqHi_pos hEupPos pv2 hv2R hcontR clam2
    have hphiUp : (1 - 2 * (w.u0 : ℝ)) * ((Jl w.u0 : ℚ) : ℝ) -
        ((qHi B : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) ≤ phi μ.midpoint ((Eup B : ℚ) : ℝ) := by
      unfold phi; linarith
    have hphiUp0 : 0 ≤ phi μ.midpoint ((Eup B : ℚ) : ℝ) := by linarith
    have hconv := phi_entropy_convexOn hm0 (by linarith : μ.midpoint < 1)
    have hcap := phi_at_entropy_cap hm0 hmh
    have hmono : phi μ.midpoint ((Eup B : ℚ) : ℝ) ≤ phi μ.midpoint μ.meanEntropy :=
      convex_step hconv hE0 hEup hEup_lt hcap hphiUp0
    linarith

/-- Leaf form for the route row. -/
theorem leafOK_of_parentCheck {B : CKLaneD.Box} {w : PW} (hw : parentCheck B w = true) :
    LeafOK B :=
  leafOK_of_parentBox (parentCheck_sound hw)

end CKLaneM05.FE8

#check @CKLaneM05.FE8.parentCheck_sound
#check @CKLaneM05.FE8.leafOK_of_parentCheck
#print axioms CKLaneM05.FE8.parentCheck_sound
#print axioms CKLaneM05.FE8.leafOK_of_parentCheck

end


