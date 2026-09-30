-- Prove2me | Definitions.Def_CK_CKLaneN6_PLog
-- name    : CK_CKLaneN6_PLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:15:50.36137+00:00
-- url     : https://prove2.me/theorems/a813184a-4564-4760-810e-a9e88b80b236
-- title:
--   Courtade–Kumar proof module `CKLaneN6.PLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.PLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.PLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.PLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/PLog.lean)

import Definitions.Def_CK_CKLaneN6_Base
import Definitions.Def_CK_CKLaneN6_EtaBeta

-- ===== source module CKLaneN6.PLog =====
section

/-!
# Lane N6: the archive's logarithmic parent rule (13) on archived boxes (`plog`)

SMALL_RATIO PROOF.md §9 / `SMALL_DIFFERENCE_COVER.py` owner `phi_parent_log`: with `q = 1 - a - b`
(clipped below by `1/100 ≤ b - a ≤ q`), `E ∈ [E⁻, E⁺]`, `C(q) = 1 - H((1-q)/2)`,
`φ - ψ = η(E) - η(E + C(q)) - F(q,E) ≥ 2C(q) + β ln(1 + C(q)/E) - F(q,E)` (`eta_increment_ge_beta`),
and the checker certifies `q⁺ J(v2) ≤ 2 C(q⁻) + β · ln(1 + C(q⁻)/E⁺)` (lower log bound from
`CKLaneE.FP`), with `v2 ≤ radialContact(q⁺, E⁻)` so `F(q,E) ≤ q⁺ J(v2)` (`CKLaneM05.F_le_of_contact`).

`plogCheck_sound : plogCheck B w = true → ParentBoxD B` (no other hypothesis).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6.PLog

open GeneralCK CKLaneE.FP CKLaneN6
open CKLaneM05.FE8 (Eup Elo boxSane boxPts box_facts)
open CKLaneM05 (Jh le_Jh F_le_of_contact H_le_H)

/-- Witness: inverse-entropy brackets `vm ≤ H⁻¹(E⁻)`, `H⁻¹(h1) ≤ vp`, contact point `v2`. -/
structure PLW where
  vm : ℚ
  vp : ℚ
  v2 : ℚ
  deriving Repr, DecidableEq

section defs
variable (B : CKLaneD.Box) (w : PLW)

def pqLo : ℚ := max (1 / 100) (1 - B.ahi - B.bhi)
def pqHi : ℚ := 1 - B.alo - B.blo
def pmLo : ℚ := (1 - pqHi B) / 2
def pmHi : ℚ := (1 - pqLo B) / 2
def CqLo : ℚ := 1 - Hhi (pmHi B)
def CqHi : ℚ := 1 - Hlo (pmLo B)
def h1P : ℚ := Eup B + CqHi B
def lnArg : ℚ := Eup B / (Eup B + CqLo B)
def lnLo : ℚ := -lHi (lnArg B)
def betaP : ℚ := (1 - 2 * w.vp) / (LqHi * (1 - w.vp)) * (1 + 1 / lamHi w.vm)

end defs

def plogCheck (B : CKLaneD.Box) (w : PLW) : Bool :=
  boxSane B && boxPts B && ptOk (pmLo B) && ptOk (pmHi B) && ptOk w.vm && ptOk w.vp &&
  ptOk w.v2 && ptOk (lnArg B) &&
  decide (0 < Elo B ∧ 0 < CqLo B ∧ pmHi B ≤ 1 / 2 ∧
    Hhi w.vm ≤ Elo B ∧ w.vm < 1 / 2 ∧ 0 < lamHi w.vm ∧
    h1P B ≤ Hlo w.vp ∧ w.vp < 1 / 2 ∧ h1P B < 1 ∧
    w.v2 < 1 / 2 ∧ pqHi B * Hhi w.v2 ≤ Elo B * (1 - 2 * w.v2) ∧ 0 ≤ lamHi w.v2 ∧ 0 < pqHi B ∧
    pqHi B * Jh w.v2 ≤ 2 * CqLo B + betaP w * lnLo B)

set_option maxHeartbeats 4000000 in
theorem plogCheck_sound {B : CKLaneD.Box} {w : PLW} (h : plogCheck B w = true) : ParentBoxD B := by
  intro k μ hin hd
  simp only [plogCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hp⟩, pmL⟩, pmH⟩, pvm⟩, pvp⟩, pv2⟩, pln⟩,
    cElo, cCq, cpmH, cvm, cvm2, clam, cvp, cvp2, ch1, cv2, ccont, clam2, cqH, cfin⟩ := h
  obtain ⟨_, _, _, hm0, _, _, hElo, hEup, _, hE0, _⟩ := box_facts hs hp μ hin
  have hs' := hs
  simp only [boxSane, decide_eq_true_eq] at hs'
  obtain ⟨_, _, _, _, _, sb2, _, _, _⟩ := hs'
  obtain ⟨h1, h2, h3, h4, _, _⟩ := hin
  have rb2 : ((B.bhi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr sb2; push_cast at h'; exact h'
  have cast_lt_half : ∀ {x : ℚ}, x < 1 / 2 → (x : ℝ) < 1 / 2 := by
    intro x hx
    have h' := (Rat.cast_lt (K := ℝ)).mpr hx
    push_cast at h'; linarith
  -- the bias q and the parent mean
  set q : ℝ := 1 - μ.a - μ.b with hqdef
  set E : ℝ := μ.meanEntropy with hEdef
  have hq_lo : ((pqLo B : ℚ) : ℝ) ≤ q := by
    unfold pqLo
    rw [Rat.cast_max]
    push_cast
    apply max_le <;> linarith
  have hq_hi : q ≤ ((pqHi B : ℚ) : ℝ) := by unfold pqHi; push_cast; linarith
  have hq0 : (1 : ℝ) / 100 ≤ q := by
    have : ((1 / 100 : ℚ) : ℝ) ≤ ((pqLo B : ℚ) : ℝ) := by
      exact_mod_cast (le_max_left _ _ : (1 / 100 : ℚ) ≤ max (1 / 100) (1 - B.ahi - B.bhi))
    push_cast at this
    linarith
  have hqpos : 0 < q := by linarith
  have hmid : μ.midpoint = (1 - q) / 2 := by rw [hqdef]; unfold InteriorLaw.midpoint; ring
  have epmLo : ((pmLo B : ℚ) : ℝ) = (1 - ((pqHi B : ℚ) : ℝ)) / 2 := by unfold pmLo; push_cast; ring
  have epmHi : ((pmHi B : ℚ) : ℝ) = (1 - ((pqLo B : ℚ) : ℝ)) / 2 := by unfold pmHi; push_cast; ring
  have hpmH2 : ((pmHi B : ℚ) : ℝ) ≤ 1 / 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr cpmH; push_cast at h'; exact h'
  have hm_hi : μ.midpoint ≤ ((pmHi B : ℚ) : ℝ) := by rw [hmid, epmHi]; linarith
  have hm_lo : ((pmLo B : ℚ) : ℝ) ≤ μ.midpoint := by rw [hmid, epmLo]; linarith
  have hpmL0 : (0 : ℝ) ≤ ((pmLo B : ℚ) : ℝ) := by
    have := (ptOk_pos pmL).1; exact_mod_cast this.le
  -- C(q) = 1 - H(m) and its enclosure
  set Cq : ℝ := 1 - H μ.midpoint with hCqdef
  obtain ⟨_, HmH⟩ := H_bounds pmH
  obtain ⟨HmL, _⟩ := H_bounds pmL
  have hCq_lo : ((CqLo B : ℚ) : ℝ) ≤ Cq := by
    have hH := (H_le_H hm0.le hm_hi hpmH2).trans HmH
    unfold CqLo; push_cast; rw [hCqdef]; linarith
  have hCq_hi : Cq ≤ ((CqHi B : ℚ) : ℝ) := by
    have hH := HmL.trans (H_le_H hpmL0 hm_lo (hm_hi.trans hpmH2))
    unfold CqHi; push_cast; rw [hCqdef]; linarith
  have hCqLo_pos : (0 : ℝ) < ((CqLo B : ℚ) : ℝ) := by exact_mod_cast cCq
  have hCq0 : 0 ≤ Cq := by linarith
  -- entropy increment with beta
  have hEloPos : (0 : ℝ) < ((Elo B : ℚ) : ℝ) := by exact_mod_cast cElo
  have hh1 : ((h1P B : ℚ) : ℝ) < 1 := by exact_mod_cast ch1
  have eh1 : ((h1P B : ℚ) : ℝ) = ((Eup B : ℚ) : ℝ) + ((CqHi B : ℚ) : ℝ) := by
    unfold h1P; push_cast; ring
  have hvm0 : (0 : ℝ) < w.vm := by exact_mod_cast (ptOk_pos pvm).1
  have hvp0 : (0 : ℝ) < w.vp := by exact_mod_cast (ptOk_pos pvp).1
  obtain ⟨_, Hvm⟩ := H_bounds pvm
  obtain ⟨Hvp, _⟩ := H_bounds pvp
  have hvmH : H (w.vm : ℝ) ≤ ((Elo B : ℚ) : ℝ) :=
    Hvm.trans ((Rat.cast_le (K := ℝ)).mpr cvm)
  have hvpH : ((h1P B : ℚ) : ℝ) ≤ H (w.vp : ℝ) :=
    ((Rat.cast_le (K := ℝ)).mpr cvp).trans Hvp
  obtain ⟨_, hLq⟩ := log_two_mem
  obtain ⟨_, hlamv⟩ := lam_bounds pvm
  have hlam0 : (0 : ℝ) < ((lamHi w.vm : ℚ) : ℝ) := by exact_mod_cast clam
  have hinc := eta_increment_ge_beta (a := E) (c := Cq) hEloPos hh1 hvm0
    (cast_lt_half cvm2).le hvmH hvp0.le hvpH (cast_lt_half cvp2).le hLq hlamv hlam0 hElo hCq0
    (by rw [eh1]; linarith)
  have ebeta : ((betaP w : ℚ) : ℝ) = (1 - 2 * (w.vp : ℝ)) / (((LqHi : ℚ) : ℝ) * (1 - (w.vp : ℝ))) *
      (1 + 1 / ((lamHi w.vm : ℚ) : ℝ)) := by
    unfold betaP; push_cast; ring
  have hbeta0 : (0 : ℝ) ≤ ((betaP w : ℚ) : ℝ) := by
    rw [ebeta]
    have hvp12 := cast_lt_half cvp2
    have hLqpos : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := lt_of_lt_of_le (Real.log_pos (by norm_num)) hLq
    apply mul_nonneg (div_nonneg (by linarith) (mul_nonneg hLqpos.le (by linarith)))
    positivity
  -- logarithm lower bound
  have eArg : ((lnArg B : ℚ) : ℝ) = ((Eup B : ℚ) : ℝ) / (((Eup B : ℚ) : ℝ) + ((CqLo B : ℚ) : ℝ)) := by
    unfold lnArg; push_cast; ring
  have hEupPos : (0 : ℝ) < ((Eup B : ℚ) : ℝ) := hE0.trans_le hEup
  obtain ⟨_, hlArg, _, _⟩ := ptOk_sound pln
  have hlog1 : ((lnLo B : ℚ) : ℝ) ≤ Real.log (1 + ((CqLo B : ℚ) : ℝ) / ((Eup B : ℚ) : ℝ)) := by
    have e : 1 + ((CqLo B : ℚ) : ℝ) / ((Eup B : ℚ) : ℝ) =
        (((lnArg B : ℚ) : ℝ))⁻¹ := by
      rw [eArg, inv_div]; field_simp
    rw [e, Real.log_inv]
    unfold lnLo; push_cast; linarith
  have hlog2 : Real.log (1 + ((CqLo B : ℚ) : ℝ) / ((Eup B : ℚ) : ℝ)) ≤ Real.log (1 + Cq / E) := by
    apply Real.log_le_log (by positivity)
    have : ((CqLo B : ℚ) : ℝ) / ((Eup B : ℚ) : ℝ) ≤ Cq / E := by
      rw [div_le_div_iff₀ hEupPos hE0]
      have k1 : ((CqLo B : ℚ) : ℝ) * E ≤ ((CqLo B : ℚ) : ℝ) * ((Eup B : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hEup hCqLo_pos.le
      have k2 : ((CqLo B : ℚ) : ℝ) * ((Eup B : ℚ) : ℝ) ≤ Cq * ((Eup B : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hCq_lo hEupPos.le
      linarith
    linarith
  have hbl := mul_le_mul_of_nonneg_left (hlog1.trans hlog2) hbeta0
  -- the radial term
  have hqHpos : (0 : ℝ) < ((pqHi B : ℚ) : ℝ) := by exact_mod_cast cqH
  obtain ⟨_, Hv2⟩ := H_bounds pv2
  have hv2R := cast_lt_half cv2
  have hcontE : ((pqHi B : ℚ) : ℝ) * H (w.v2 : ℝ) ≤ E * (1 - 2 * (w.v2 : ℝ)) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr ccont
    push_cast at hc
    have k1 := mul_le_mul_of_nonneg_left Hv2 hqHpos.le
    have k2 : ((Elo B : ℚ) : ℝ) * (1 - 2 * (w.v2 : ℝ)) ≤ E * (1 - 2 * (w.v2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hElo (by linarith)
    linarith
  have hF := F_le_of_contact hqpos.le hq_hi hqHpos hE0 pv2 hv2R hcontE clam2
  have hfinR : ((pqHi B : ℚ) : ℝ) * ((Jh w.v2 : ℚ) : ℝ) ≤
      2 * ((CqLo B : ℚ) : ℝ) + ((betaP w : ℚ) : ℝ) * ((lnLo B : ℚ) : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr cfin
    push_cast at hc
    exact hc
  -- assemble
  have habs : |1 - 2 * μ.midpoint| = q := by rw [hmid]; rw [abs_of_pos (by linarith)]; ring
  unfold phi psi
  rw [habs]
  have hpsiarg : E + 1 - H μ.midpoint = E + Cq := by rw [hCqdef]; ring
  rw [hpsiarg]
  rw [← ebeta] at hinc
  linarith

/-- Leaf form for the Thm 3 row. -/
theorem leafOK_of_plogCheck {B : CKLaneD.Box} {w : PLW} (h : plogCheck B w = true) : LeafOK B :=
  leafOK_of_parentBoxD (plogCheck_sound h)

end CKLaneN6.PLog

end


