-- Prove2me | Definitions.Def_CK_CKLaneN6_Rad
-- name    : CK_CKLaneN6_Rad
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:59:20.011655+00:00
-- url     : https://prove2.me/theorems/21837c76-1c7c-41f0-8cca-60a250116699
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Rad` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Rad` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Rad` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Rad (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Rad.lean)

import Definitions.Def_CK_CKLaneN6_Base
import Definitions.Def_CK_CKLaneM03_Kernel

-- ===== source module CKLaneN6.Rad =====
section

/-!
# Lane N6: native radial kernel on `(a, b, t)` boxes (`rad`)

Port of Lane M03's same-side `endpoint` kernel (`CKLaneM03.epCheck`, archive
`R_psi ≤ Δ·p̄ ≤ K d² p̄ ≤ d² F(D,E⁺)/D² ≤ F(d,E) ≤ ζ`) to the archive boxes of SMALL_RATIO Thm 3
(`CKLaneD.Box`, entropy fraction over `EMIN = 10^-6`), where the means are box coordinates.
It is the archived `sum_normalized` inequality (`F(d,E)/d² ≥ K·pp` with `v = contact(d,E)`)
with the sharp entropy-drop coefficient `Δ/d² ≤ K` of M03 (`Cn(z)/z²` monotonicity).

For a law in the box with `a < b`:
* `Δ ≤ K d²` with `ρ = (b-a)/(a+b) ≤ (b1-a0)/(b1+a0)`, `κ = (b-a)/(2-a-b) ≤ D/(2(1-m1))`
  (`CKLaneM03.ep_drop_le`), `D = b1 - a0`;
* `s ≤ (1-t0)(C0hi - EMIN)`, `E ≤ EMIN + t1 (C0hi - EMIN)`, `I = Δ + s ≤ I⁺`;
* `P(Δ+s) - P(s) ≤ Δ (P'(s)+P'(I))/2 ≤ Δ p̄` (trapezoid, slope anchors);
* `F(d,E) ≥ d² J(vc)/D` from `E⁺ (1-2vc) ≤ D H(vc)` (`CKLaneM03.ep_F_lower`) and `F ≤ cost`.

`radCheck_sound : radCheck B w = true → RadSem B` has no other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6.Rad

open GeneralCK CKLaneE.FP CKLaneN6
open CKLaneM03 (ep_drop_le ep_F_lower ep_Jlo_le ep_H_mono ep_kap_le epJlo)

/-- Untrusted radial certificate: two slope anchors, a contact bracket, the information mode. -/
structure RW where
  vS : ℚ
  vI : ℚ
  vc : ℚ
  useHm : Bool
  deriving Repr, DecidableEq

section Derived
variable (B : CKLaneD.Box) (w : RW)

def rD : ℚ := B.bhi - B.alo
def rMlo : ℚ := (B.alo + B.blo) / 2
def rMhi : ℚ := (B.ahi + B.bhi) / 2
def rRho : ℚ := (B.bhi - B.alo) / (B.bhi + B.alo)
def rQR : ℚ := (1 - rRho B) / 2
def rKap : ℚ := rD B / (2 * (1 - rMhi B))
def rQK : ℚ := (1 - rKap B) / 2
def rCR : ℚ := (1 - Hlo (rQR B)) / (rRho B * rRho B)
def rCK : ℚ := (1 - Hlo (rQK B)) / (rKap B * rKap B)
def rK : ℚ := (rCR B / rMlo B + rCK B / (1 - rMhi B)) / 4
def rChi : ℚ := (Hhi B.ahi + Hhi B.bhi) / 2
def rClo : ℚ := (Hlo B.alo + Hlo B.blo) / 2
def rSHi : ℚ := (1 - B.t0) * (rChi B - CKLaneD.EMIN)
def rEHi : ℚ := CKLaneD.EMIN + B.t1 * (rChi B - CKLaneD.EMIN)
def rELo : ℚ := CKLaneD.EMIN + B.t0 * (rClo B - CKLaneD.EMIN)
def rIHi : ℚ := if w.useHm then Hhi (rMhi B) - rELo B else rSHi B + rK B * (rD B * rD B)
def rPbar : ℚ := (P1up w.vS + P1up w.vI) / 2

end Derived

/-- Entropy points needed only for the `H(m)` branch of the information bound. -/
def rHmOK (B : CKLaneD.Box) (w : RW) : Bool :=
  if w.useHm then ptOk B.alo && ptOk B.blo && ptOk (rMhi B) else true

/-- The Boolean radial checker. -/
def radCheck (B : CKLaneD.Box) (w : RW) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ B.ahi ≤ 1 / 2 ∧ 0 < B.blo ∧ B.blo ≤ B.bhi ∧ B.bhi ≤ 1 / 2 ∧
    0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  ptOk B.ahi && ptOk B.bhi && ptOk (rQR B) && ptOk (rQK B) &&
  rHmOK B w &&
  decide (0 < rD B ∧ 0 < rKap B ∧ rKap B ≤ 1 ∧ 0 ≤ rK B ∧ rIHi B w < 1) &&
  anchorOk w.vS (rSHi B) && anchorOk w.vI (rIHi B w) &&
  decide (0 ≤ rPbar w) &&
  ptOk w.vc &&
  decide (w.vc < 1 / 2 ∧ 0 ≤ lamLo w.vc) &&
  decide (rEHi B * (1 - 2 * w.vc) ≤ rD B * Hlo w.vc) &&
  decide (rK B * rPbar w * rD B ≤ epJlo w.vc)

/-- `ρ = (b-a)/(a+b)` is maximal at `(a0, b1)`. -/
theorem rho_le {a b a0 b1 : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a) (hb : b ≤ b1) (hab : a < b) :
    (b - a) / (a + b) ≤ (b1 - a0) / (b1 + a0) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b1 + a0 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  have hb0 : 0 < b := by linarith
  have k1 : b * a0 ≤ b1 * a0 := mul_le_mul_of_nonneg_right hb ha0.le
  have k2 : b1 * a0 ≤ b1 * a := mul_le_mul_of_nonneg_left ha (by linarith)
  nlinarith

set_option maxHeartbeats 4000000 in
theorem radCheck_sound {B : CKLaneD.Box} {w : RW} (h : radCheck B w = true) : RadSem B := by
  intro k μ hbox hab
  unfold radCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨qa0, qaa, qa2, qb0, qbb, qb2, qt0, qtt, qt1, hpA, hpB, hpR, hpK, hhm,
    qD0, qkap0, qkap1, qK0, hI1, hvS, hvI, hpbar, hpc, qvc2, qlam, hcont, hfin⟩ := h
  obtain ⟨hx1, hx2, hy1, hy2, hE1, hE2⟩ := hbox
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have hb1' : μ.b < 1 := μ.b_interior.2
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  -- casts of the box facts
  have ra0 : (0 : ℝ) < B.alo := by exact_mod_cast qa0
  have ra2 : (B.ahi : ℝ) ≤ 1 / 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr qa2; push_cast at h'; exact h'
  have rb0 : (0 : ℝ) < B.blo := by exact_mod_cast qb0
  have rb2 : (B.bhi : ℝ) ≤ 1 / 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr qb2; push_cast at h'; exact h'
  have rt0 : (0 : ℝ) ≤ B.t0 := by exact_mod_cast qt0
  have rtt : (B.t0 : ℝ) ≤ B.t1 := by exact_mod_cast qtt
  have rt1 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast qt1
  have ha2 : μ.a ≤ 1 / 2 := hx2.trans ra2
  have hb2 : μ.b ≤ 1 / 2 := hy2.trans rb2
  -- geometry
  have eD : ((rD B : ℚ) : ℝ) = (B.bhi : ℝ) - B.alo := by unfold rD; push_cast; ring
  have eMlo : ((rMlo B : ℚ) : ℝ) = ((B.alo : ℝ) + B.blo) / 2 := by unfold rMlo; push_cast; ring
  have eMhi : ((rMhi B : ℚ) : ℝ) = ((B.ahi : ℝ) + B.bhi) / 2 := by unfold rMhi; push_cast; ring
  have hd_hi : μ.b - μ.a ≤ ((rD B : ℚ) : ℝ) := by rw [eD]; linarith
  have hm_lo : ((rMlo B : ℚ) : ℝ) ≤ (μ.a + μ.b) / 2 := by rw [eMlo]; linarith
  have hm_hi : (μ.a + μ.b) / 2 ≤ ((rMhi B : ℚ) : ℝ) := by rw [eMhi]; linarith
  have hmhi_half : ((rMhi B : ℚ) : ℝ) ≤ 1 / 2 := by rw [eMhi]; linarith
  have hmlo0 : (0 : ℝ) < ((rMlo B : ℚ) : ℝ) := by rw [eMlo]; linarith
  -- entropy enclosures
  obtain ⟨_, hHA⟩ := H_bounds hpA
  obtain ⟨_, hHB⟩ := H_bounds hpB
  have hHa : H μ.a ≤ ((Hhi B.ahi : ℚ) : ℝ) := (ep_H_mono ha0.le hx2 ra2).trans hHA
  have hHb : H μ.b ≤ ((Hhi B.bhi : ℚ) : ℝ) := (ep_H_mono hb0.le hy2 rb2).trans hHB
  have eChi : ((rChi B : ℚ) : ℝ) = (((Hhi B.ahi : ℚ) : ℝ) + ((Hhi B.bhi : ℚ) : ℝ)) / 2 := by
    unfold rChi; push_cast; ring
  have hC_hi : (H μ.a + H μ.b) / 2 ≤ ((rChi B : ℚ) : ℝ) := by rw [eChi]; linarith
  have hEM : ((CKLaneD.EMIN : ℚ) : ℝ) = 1 / 1000000 := by
    simp only [CKLaneD.EMIN]; push_cast; ring
  -- deficit, entropy, information
  have hsdef : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔdef : μ.entropyDrop = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hs0 : 0 ≤ μ.meanDeficit := μ.meanDeficit_mem.1
  have hΔ0 : 0 ≤ μ.entropyDrop := μ.entropyDrop_nonneg
  have esHi : ((rSHi B : ℚ) : ℝ) = (1 - (B.t0 : ℝ)) * (((rChi B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) := by
    unfold rSHi; push_cast; ring
  have eEhi : ((rEHi B : ℚ) : ℝ) = (CKLaneD.EMIN : ℝ) + (B.t1 : ℝ) * (((rChi B : ℚ) : ℝ) -
      (CKLaneD.EMIN : ℝ)) := by
    unfold rEHi; push_cast; ring
  have hs_hi : μ.meanDeficit ≤ ((rSHi B : ℚ) : ℝ) := by
    rw [hsdef, esHi]
    have k1 : (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) ≤
        (1 - (B.t0 : ℝ)) * (((rChi B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hE_hi : μ.meanEntropy ≤ ((rEHi B : ℚ) : ℝ) := by
    rw [eEhi]
    have k1 : (B.t1 : ℝ) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) ≤
        (B.t1 : ℝ) * (((rChi B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- the entropy-drop coefficient
  have erho : ((rRho B : ℚ) : ℝ) = ((B.bhi : ℝ) - B.alo) / ((B.bhi : ℝ) + B.alo) := by
    unfold rRho; push_cast; ring
  have eqR : ((rQR B : ℚ) : ℝ) = (1 - ((rRho B : ℚ) : ℝ)) / 2 := by unfold rQR; push_cast; ring
  have ekap : ((rKap B : ℚ) : ℝ) = ((rD B : ℚ) : ℝ) / (2 * (1 - ((rMhi B : ℚ) : ℝ))) := by
    unfold rKap; push_cast; ring
  have eqK : ((rQK B : ℚ) : ℝ) = (1 - ((rKap B : ℚ) : ℝ)) / 2 := by unfold rQK; push_cast; ring
  have ecR : ((rCR B : ℚ) : ℝ) =
      (1 - ((Hlo (rQR B) : ℚ) : ℝ)) / (((rRho B : ℚ) : ℝ) * ((rRho B : ℚ) : ℝ)) := by
    unfold rCR; push_cast; ring
  have ecK : ((rCK B : ℚ) : ℝ) =
      (1 - ((Hlo (rQK B) : ℚ) : ℝ)) / (((rKap B : ℚ) : ℝ) * ((rKap B : ℚ) : ℝ)) := by
    unfold rCK; push_cast; ring
  have eK : ((rK B : ℚ) : ℝ) =
      (((rCR B : ℚ) : ℝ) / ((rMlo B : ℚ) : ℝ) + ((rCK B : ℚ) : ℝ) / (1 - ((rMhi B : ℚ) : ℝ))) / 4 := by
    unfold rK; push_cast; ring
  have rK0 : (0 : ℝ) ≤ ((rK B : ℚ) : ℝ) := by exact_mod_cast qK0
  have rkap1 : ((rKap B : ℚ) : ℝ) ≤ 1 := by exact_mod_cast qkap1
  have hdrop : μ.entropyDrop ≤ ((rK B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 := by
    have hρ : (μ.b - μ.a) / (μ.a + μ.b) ≤ ((rRho B : ℚ) : ℝ) := by
      rw [erho]; exact rho_le ra0 hx1 hy2 hab
    have hρh1 : ((rRho B : ℚ) : ℝ) ≤ 1 := by
      rw [erho, div_le_one (by linarith)]; linarith
    have hκ : (μ.b - μ.a) / (2 - μ.a - μ.b) ≤ ((rKap B : ℚ) : ℝ) := by
      rw [ekap]; exact ep_kap_le hab hb1' hd_hi hm_hi (by linarith)
    obtain ⟨hHR, _⟩ := H_bounds hpR
    obtain ⟨hHK, _⟩ := H_bounds hpK
    have hc1 : (1 - H ((1 - ((rRho B : ℚ) : ℝ)) / 2)) / ((rRho B : ℚ) : ℝ) ^ 2 ≤
        ((rCR B : ℚ) : ℝ) := by
      rw [ecR, ← eqR, sq]
      apply div_le_div_of_nonneg_right _ (mul_self_nonneg _)
      linarith
    have hc2 : (1 - H ((1 - ((rKap B : ℚ) : ℝ)) / 2)) / ((rKap B : ℚ) : ℝ) ^ 2 ≤
        ((rCK B : ℚ) : ℝ) := by
      rw [ecK, ← eqK, sq]
      apply div_le_div_of_nonneg_right _ (mul_self_nonneg _)
      linarith
    have hd := ep_drop_le ha0 hab hb1' hρ hρh1 hκ rkap1 hc1 hc2 hmlo0 hm_lo hm_hi (by linarith)
    rw [hΔdef, eK]
    exact hd
  -- information range
  have hI_hi : μ.entropyDrop + μ.meanDeficit ≤ ((rIHi B w : ℚ) : ℝ) := by
    unfold rIHi
    split_ifs with hu
    · simp only [rHmOK, if_pos hu, Bool.and_eq_true] at hhm
      obtain ⟨⟨hpal, hpbl⟩, hpm⟩ := hhm
      obtain ⟨hHal, _⟩ := H_bounds hpal
      obtain ⟨hHbl, _⟩ := H_bounds hpbl
      obtain ⟨_, hHm⟩ := H_bounds hpm
      have hHa_lo : ((Hlo B.alo : ℚ) : ℝ) ≤ H μ.a := hHal.trans (ep_H_mono ra0.le hx1 ha2)
      have hHb_lo : ((Hlo B.blo : ℚ) : ℝ) ≤ H μ.b := hHbl.trans (ep_H_mono rb0.le hy1 hb2)
      have hHm_hi : H ((μ.a + μ.b) / 2) ≤ ((Hhi (rMhi B) : ℚ) : ℝ) :=
        (ep_H_mono (by linarith) hm_hi hmhi_half).trans hHm
      have eClo : ((rClo B : ℚ) : ℝ) = (((Hlo B.alo : ℚ) : ℝ) + ((Hlo B.blo : ℚ) : ℝ)) / 2 := by
        unfold rClo; push_cast; ring
      have eElo : ((rELo B : ℚ) : ℝ) = (CKLaneD.EMIN : ℝ) + (B.t0 : ℝ) * (((rClo B : ℚ) : ℝ) -
          (CKLaneD.EMIN : ℝ)) := by
        unfold rELo; push_cast; ring
      have hElo : ((rELo B : ℚ) : ℝ) ≤ μ.meanEntropy := by
        rw [eElo]
        have k1 : (B.t0 : ℝ) * (((rClo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) ≤
            (B.t0 : ℝ) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) :=
          mul_le_mul_of_nonneg_left (by rw [eClo]; linarith) rt0
        linarith
      push_cast
      rw [hΔdef, hsdef]
      linarith
    · push_cast
      have hd0 : 0 ≤ μ.b - μ.a := by linarith
      have hsq : (μ.b - μ.a) ^ 2 ≤ ((rD B : ℚ) : ℝ) * ((rD B : ℚ) : ℝ) := by
        rw [sq]; exact mul_le_mul hd_hi hd_hi hd0 (hd0.trans hd_hi)
      have h' := mul_le_mul_of_nonneg_left hsq rK0
      linarith
  have rI1 : ((rIHi B w : ℚ) : ℝ) < 1 := by exact_mod_cast hI1
  have hI1' : μ.entropyDrop + μ.meanDeficit < 1 := lt_of_le_of_lt hI_hi rI1
  -- split bound via trapezoid and slope anchors
  have htrap := CKLaneE.P_trapezoid hs0 (le_add_of_nonneg_left hΔ0) hI1'
  have hPS := anchorOk_sound hvS hs0 hs_hi
  have hPI := anchorOk_sound hvI (add_nonneg hΔ0 hs0) hI_hi
  have epbar : ((rPbar w : ℚ) : ℝ) = (((P1up w.vS : ℚ) : ℝ) + ((P1up w.vI : ℚ) : ℝ)) / 2 := by
    unfold rPbar; push_cast; ring
  have rpbar : (0 : ℝ) ≤ ((rPbar w : ℚ) : ℝ) := by exact_mod_cast hpbar
  have hsplit : μ.splitBound ≤ μ.entropyDrop * ((rPbar w : ℚ) : ℝ) := by
    have e : μ.splitBound = Scalar.P (μ.entropyDrop + μ.meanDeficit) - Scalar.P μ.meanDeficit :=
      rfl
    rw [e, epbar]
    have h1 : μ.entropyDrop + μ.meanDeficit - μ.meanDeficit = μ.entropyDrop := by ring
    rw [h1] at htrap
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith
  have hgap := μ.psi_gap_le_splitBound
  -- radial endpoint bound
  have hcostF := PsiEndpointPlane.law_radial_lower μ hab
  have hd0 : 0 < μ.b - μ.a := by linarith
  have hvc0 : (0 : ℝ) < w.vc := by exact_mod_cast (ptOk_pos hpc).1
  have hvc12 : (w.vc : ℝ) ≤ 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr qvc2
    push_cast at h'; linarith
  obtain ⟨hHvc, _⟩ := H_bounds hpc
  have rd0 : (0 : ℝ) < ((rD B : ℚ) : ℝ) := by exact_mod_cast qD0
  have hcontR : ((rEHi B : ℚ) : ℝ) * (1 - 2 * (w.vc : ℝ)) ≤
      ((rD B : ℚ) : ℝ) * H (w.vc : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hcont
    push_cast at h'
    have h'' := mul_le_mul_of_nonneg_left hHvc rd0.le
    linarith
  have hF := ep_F_lower hd0 hd_hi hEpos hE_hi hvc0.le hvc12 hcontR
  have hJ := ep_Jlo_le hpc qlam
  have hfinR : ((rK B : ℚ) : ℝ) * ((rPbar w : ℚ) : ℝ) * ((rD B : ℚ) : ℝ) ≤
      ((epJlo w.vc : ℚ) : ℝ) := by exact_mod_cast hfin
  have hKp : ((rK B : ℚ) : ℝ) * ((rPbar w : ℚ) : ℝ) ≤ J (w.vc : ℝ) / ((rD B : ℚ) : ℝ) := by
    rw [le_div_iff₀ rd0]; linarith
  have hd2 : 0 ≤ (μ.b - μ.a) ^ 2 := sq_nonneg _
  have hmain : μ.entropyDrop * ((rPbar w : ℚ) : ℝ) ≤ μ.cost := by
    calc μ.entropyDrop * ((rPbar w : ℚ) : ℝ)
        ≤ ((rK B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * ((rPbar w : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdrop rpbar
      _ = (μ.b - μ.a) ^ 2 * (((rK B : ℚ) : ℝ) * ((rPbar w : ℚ) : ℝ)) := by ring
      _ ≤ (μ.b - μ.a) ^ 2 * (J (w.vc : ℝ) / ((rD B : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hKp hd2
      _ ≤ F (μ.b - μ.a) μ.meanEntropy := hF
      _ ≤ μ.cost := hcostF
  exact hgap.trans (hsplit.trans hmain)

/-- Leaf form for the Thm 3 row. -/
theorem leafOK_of_radCheck {B : CKLaneD.Box} {w : RW} (h : radCheck B w = true) : LeafOK B :=
  leafOK_of_radSem (radCheck_sound h)

end CKLaneN6.Rad

end


