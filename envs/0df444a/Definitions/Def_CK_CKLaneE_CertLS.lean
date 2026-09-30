-- Prove2me | Definitions.Def_CK_CKLaneE_CertLS
-- name    : CK_CKLaneE_CertLS
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:39:24.304466+00:00
-- url     : https://prove2.me/theorems/71ca6f75-bab5-4bbd-8286-7be98a4f4574
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertLS` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertLS` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertLS` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertLS (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertLS.lean)

import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneE_NLSChecker
import Definitions.Def_CK_CKLaneE_EntropyDropSharp
import Definitions.Def_CK_CKLaneE_Chart

-- ===== source module CKLaneE.CertLS =====
section

/-!
# Lane E: log-sum certificate for population leaves (fast enclosures, two acceptance forms)

For a leaf box `B` (ratio `r1..r2`, mean `b1..b2`, entropy `E1..E2`) the certificate proves the
owner's conclusion for all chart laws with `(a/b, b) ∈ box` and `E ≥ E1` (the upper entropy end is
irrelevant): the log-sum gap `G(S) = j + β(b-a)^2 S - P(Δ+S) + P(S)` is certified nonnegative at the
maximal deficit `S = (H a + H b)/2 - E1`, and the corpus concavity lemma
`Scalar.gap_endpoint_criterion` with `deterministic_cap_bound` propagates it to every `E ≥ E1`.

Acceptance: `normOk` (archive `normalized_logsum`, `W = 0`, divided by `(b-a)^2`) or `meanOk`
(archive `mean_logsum`, unnormalized, `j` bounded below from `log(b/a) + log(1-a) - log(1-b)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.LS

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart
open CKLaneE.NLS (H_le_H box_geometry K1_bound)

section defs
variable (B : Box3)

def aLo : ℚ := B.r1 * B.b1
def aHi : ℚ := B.r2 * B.b2
def mLo : ℚ := B.b1 * (1 + B.r1) / 2
def mHi : ℚ := B.b2 * (1 + B.r2) / 2
def dLo : ℚ := B.b1 * (1 - B.r2)
def dHi : ℚ := B.b2 * (1 - B.r1)
def CLo : ℚ := (Hlo (aLo B) + Hlo B.b1) / 2
def CHi : ℚ := (Hhi (aHi B) + Hhi B.b2) / 2
def sLo : ℚ := CLo B - B.E1
def sHi : ℚ := CHi B - B.E1
def IHi : ℚ := Hhi (mHi B) - B.E1
def DHi : ℚ := Hhi (mHi B) - CLo B
def K1 : ℚ := DHi B / (dLo B * dLo B)
def rhoHi : ℚ := (1 - B.r1) / (1 + B.r1)
def kapHi : ℚ := dHi B / (2 * (1 - mHi B))
def K2 : ℚ :=
  ((1 + rhoHi B * rhoHi B / 6 + 2 / 5 * (rhoHi B * rhoHi B * (rhoHi B * rhoHi B))) / mLo B +
    (1 + kapHi B * kapHi B / 6 + 2 / 5 * (kapHi B * kapHi B * (kapHi B * kapHi B))) /
      (1 - mHi B)) / (8 * LqLo)
def rhoLo : ℚ := (1 - B.r2) / (1 + B.r2)
def kapLo : ℚ := dLo B / (2 * (1 - mLo B))
def Wlo : ℚ := (rhoLo B * rhoLo B / mHi B + kapLo B * kapLo B / (1 - mLo B)) / (12 * LqHi)
def K : ℚ := if 0 < dLo B ∧ K1 B ≤ K2 B then K1 B else K2 B
def betaLo : ℚ := 1 / (2 * B.b2 * (1 - aLo B))
def pbar (vS vI : ℚ) : ℚ := (P1up vS + P1up vI) / 2
def excess (vS vI : ℚ) : ℚ := if 0 ≤ pbar vS vI - 4 then pbar vS vI - 4 else 0
def jb : ℚ := -lHi B.r2 + l1Lo (aHi B) - l1Hi B.b1
def jLo : ℚ := dLo B * (if 0 ≤ jb B then jb B else 0) / (2 * LqHi)

def boxOk : Bool :=
  decide (0 < B.r1 ∧ B.r1 ≤ B.r2 ∧ B.r2 ≤ 1 ∧ 0 < B.b1 ∧ B.b1 ≤ B.b2 ∧ B.b2 ≤ 1 / 2 ∧ 0 < B.E1)

def normOk (vS vI : ℚ) : Bool :=
  decide (0 ≤ K B ∧ K B * excess vS vI ≤ Wlo B + betaLo B * sLo B)

def meanOk (vS vI : ℚ) : Bool :=
  decide (B.r2 < 1) && ptOk B.r2 &&
    decide (DHi B * pbar vS vI ≤ jLo B + betaLo B * (dLo B * dLo B) * sLo B)

def check (vS vI : ℚ) : Bool :=
  boxOk B && ptOk (aLo B) && ptOk (aHi B) && ptOk B.b1 && ptOk B.b2 && ptOk (mHi B) &&
    anchorOk vS (sHi B) && anchorOk vI (IHi B) && decide (0 ≤ sLo B ∧ IHi B < 1) &&
    (normOk B vS vI || meanOk B vS vI)

end defs

theorem boxOk_real {B : Box3} (h : boxOk B = true) :
    (0 : ℝ) < B.r1 ∧ (B.r1 : ℝ) ≤ B.r2 ∧ (B.r2 : ℝ) ≤ 1 ∧ (0 : ℝ) < B.b1 ∧ (B.b1 : ℝ) ≤ B.b2 ∧
      (B.b2 : ℝ) ≤ 1 / 2 ∧ (0 : ℝ) < B.E1 := by
  simp only [boxOk, decide_eq_true_eq] at h
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := h
  refine ⟨by exact_mod_cast q1, by exact_mod_cast q2, by exact_mod_cast q3, by exact_mod_cast q4,
    by exact_mod_cast q5, ?_, by exact_mod_cast q7⟩
  have h : ((B.b2 : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast q6
  simpa using h

/-! Casts -/
section casts
variable (B : Box3)
theorem c_aLo : ((aLo B : ℚ) : ℝ) = (B.r1 : ℝ) * B.b1 := by push_cast [aLo]; ring
theorem c_aHi : ((aHi B : ℚ) : ℝ) = (B.r2 : ℝ) * B.b2 := by push_cast [aHi]; ring
theorem c_mLo : ((mLo B : ℚ) : ℝ) = (B.b1 : ℝ) * (1 + B.r1) / 2 := by push_cast [mLo]; ring
theorem c_mHi : ((mHi B : ℚ) : ℝ) = (B.b2 : ℝ) * (1 + B.r2) / 2 := by push_cast [mHi]; ring
theorem c_dLo : ((dLo B : ℚ) : ℝ) = (B.b1 : ℝ) * (1 - B.r2) := by push_cast [dLo]; ring
theorem c_dHi : ((dHi B : ℚ) : ℝ) = (B.b2 : ℝ) * (1 - B.r1) := by push_cast [dHi]; ring
theorem c_CLo : ((CLo B : ℚ) : ℝ) = (((Hlo (aLo B) : ℚ) : ℝ) + ((Hlo B.b1 : ℚ) : ℝ)) / 2 := by
  push_cast [CLo]; ring
theorem c_CHi : ((CHi B : ℚ) : ℝ) = (((Hhi (aHi B) : ℚ) : ℝ) + ((Hhi B.b2 : ℚ) : ℝ)) / 2 := by
  push_cast [CHi]; ring
theorem c_sLo : ((sLo B : ℚ) : ℝ) = ((CLo B : ℚ) : ℝ) - B.E1 := by push_cast [sLo]; ring
theorem c_sHi : ((sHi B : ℚ) : ℝ) = ((CHi B : ℚ) : ℝ) - B.E1 := by push_cast [sHi]; ring
theorem c_IHi : ((IHi B : ℚ) : ℝ) = ((Hhi (mHi B) : ℚ) : ℝ) - B.E1 := by push_cast [IHi]; ring
theorem c_DHi : ((DHi B : ℚ) : ℝ) = ((Hhi (mHi B) : ℚ) : ℝ) - ((CLo B : ℚ) : ℝ) := by
  push_cast [DHi]; ring
theorem c_K1 : ((K1 B : ℚ) : ℝ) = ((DHi B : ℚ) : ℝ) / (((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ)) := by
  push_cast [K1]; ring
theorem c_rhoHi : ((rhoHi B : ℚ) : ℝ) = (1 - (B.r1 : ℝ)) / (1 + B.r1) := by push_cast [rhoHi]; ring
theorem c_kapHi : ((kapHi B : ℚ) : ℝ) = ((dHi B : ℚ) : ℝ) / (2 * (1 - ((mHi B : ℚ) : ℝ))) := by
  push_cast [kapHi]; ring
theorem c_K2 : ((K2 B : ℚ) : ℝ) =
    ((1 + ((rhoHi B : ℚ) : ℝ) ^ 2 / 6 + 2 / 5 * ((rhoHi B : ℚ) : ℝ) ^ 4) / ((mLo B : ℚ) : ℝ) +
      (1 + ((kapHi B : ℚ) : ℝ) ^ 2 / 6 + 2 / 5 * ((kapHi B : ℚ) : ℝ) ^ 4) / (1 - ((mHi B : ℚ) : ℝ))) /
      (8 * ((LqLo : ℚ) : ℝ)) := by
  push_cast [K2]; ring
theorem c_rhoLo : ((rhoLo B : ℚ) : ℝ) = (1 - (B.r2 : ℝ)) / (1 + B.r2) := by push_cast [rhoLo]; ring
theorem c_kapLo : ((kapLo B : ℚ) : ℝ) = ((dLo B : ℚ) : ℝ) / (2 * (1 - ((mLo B : ℚ) : ℝ))) := by
  push_cast [kapLo]; ring
theorem c_Wlo : ((Wlo B : ℚ) : ℝ) =
    (((rhoLo B : ℚ) : ℝ) ^ 2 / ((mHi B : ℚ) : ℝ) + ((kapLo B : ℚ) : ℝ) ^ 2 / (1 - ((mLo B : ℚ) : ℝ))) /
      (12 * ((LqHi : ℚ) : ℝ)) := by
  push_cast [Wlo]; ring
theorem c_betaLo : ((betaLo B : ℚ) : ℝ) = 1 / (2 * (B.b2 : ℝ) * (1 - (B.r1 : ℝ) * B.b1)) := by
  push_cast [betaLo, aLo]; ring
theorem c_pbar (vS vI : ℚ) :
    ((pbar vS vI : ℚ) : ℝ) = (((P1up vS : ℚ) : ℝ) + ((P1up vI : ℚ) : ℝ)) / 2 := by
  push_cast [pbar]; ring
end casts

/-- The quartic-exact normalized entropy-drop bound with box constants. -/
theorem K3_bound {a b ρh κh mL mH Lq : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hρ : (b - a) / (a + b) ≤ ρh) (hκ : (b - a) / (2 - a - b) ≤ κh)
    (hmL : 0 < mL) (hmL' : mL ≤ (a + b) / 2) (hmH : (a + b) / 2 ≤ mH) (hmH1 : mH < 1)
    (hLq : 0 < Lq) (hLq' : Lq ≤ Real.log 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤
      ((1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4) / mL + (1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4) / (1 - mH)) /
        (8 * Lq) * (b - a) ^ 2 := by
  have hnorm := entropyDrop_le_normalized6 ha hab hb
  have hd0 : 0 < b - a := by linarith
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hρ0 : 0 ≤ (b - a) / (a + b) := div_nonneg hd0.le hs.le
  have hκ0 : 0 ≤ (b - a) / (2 - a - b) := div_nonneg hd0.le ht.le
  have hρ2 : ((b - a) / (a + b)) ^ 2 ≤ ρh ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
  have hκ2 : ((b - a) / (2 - a - b)) ^ 2 ≤ κh ^ 2 := pow_le_pow_left₀ hκ0 hκ 2
  have hρ4 : ((b - a) / (a + b)) ^ 4 ≤ ρh ^ 4 := pow_le_pow_left₀ hρ0 hρ 4
  have hκ4 : ((b - a) / (2 - a - b)) ^ 4 ≤ κh ^ 4 := pow_le_pow_left₀ hκ0 hκ 4
  have hm0 : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hρh : 0 ≤ 1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4 := by positivity
  have hκh : 0 ≤ 1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4 := by positivity
  have t1 : (1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) ≤
      (1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4) / mL :=
    div_le_div₀ hρh (by linarith) hmL hmL'
  have t2 : (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
      (1 - (a + b) / 2) ≤ (1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4) / (1 - mH) :=
    div_le_div₀ hκh (by linarith) (by linarith) (by linarith)
  have hsum := add_le_add t1 t2
  have hLL : (b - a) ^ 2 / (8 * Real.log 2) ≤ (b - a) ^ 2 / (8 * Lq) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hX : 0 ≤ (1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
      (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
        (1 - (a + b) / 2) := by positivity
  calc H ((a + b) / 2) - (H a + H b) / 2 ≤ _ := hnorm
    _ ≤ (b - a) ^ 2 / (8 * Lq) *
        ((1 + ((b - a) / (a + b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (a + b)) ^ 4) / ((a + b) / 2) +
          (1 + ((b - a) / (2 - a - b)) ^ 2 / 6 + 2 / 5 * ((b - a) / (2 - a - b)) ^ 4) /
            (1 - (a + b) / 2)) :=
        mul_le_mul_of_nonneg_right hLL hX
    _ ≤ (b - a) ^ 2 / (8 * Lq) *
        ((1 + ρh ^ 2 / 6 + 2 / 5 * ρh ^ 4) / mL + (1 + κh ^ 2 / 6 + 2 / 5 * κh ^ 4) / (1 - mH)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Real assembly of the normalized form with the log-sum bonus `W`. -/
theorem assembleW {inc j Δ S d2 β βlo sLo K pbar exc W : ℝ}
    (hinc : inc ≤ Δ * pbar) (hj : 4 * Δ + d2 * W ≤ j)
    (hΔK : Δ * (pbar - 4) ≤ K * d2 * exc)
    (hβ : βlo ≤ β) (hβ0 : 0 ≤ β) (hS : sLo ≤ S) (hsLo : 0 ≤ sLo) (hd2 : 0 ≤ d2)
    (hfin : K * exc ≤ W + βlo * sLo) : inc ≤ j + d2 * β * S := by
  have h1 : βlo * sLo ≤ β * S := mul_le_mul hβ hS hsLo hβ0
  have h2 : d2 * (K * exc) ≤ d2 * (W + β * S) :=
    mul_le_mul_of_nonneg_left (hfin.trans (by linarith)) hd2
  have e1 : Δ * pbar = 4 * Δ + Δ * (pbar - 4) := by ring
  have e2 : K * d2 * exc = d2 * (K * exc) := by ring
  have e3 : d2 * (W + β * S) = d2 * W + d2 * β * S := by ring
  linarith

/-- Entropy enclosures of the law's means from the checked rational points. -/
theorem law_H_bounds (B : Box3) {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (hbox : boxOk B = true) (haLo : ptOk (aLo B) = true) (haHi : ptOk (aHi B) = true)
    (hb1ok : ptOk B.b1 = true) (hb2ok : ptOk B.b2 = true) (hmHi : ptOk (mHi B) = true)
    (hr1 : (B.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (B.r2 : ℝ))
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ)) :
    ((Hlo (aLo B) : ℚ) : ℝ) ≤ H a ∧ H a ≤ ((Hhi (aHi B) : ℚ) : ℝ) ∧
      ((Hlo B.b1 : ℚ) : ℝ) ≤ H b ∧ H b ≤ ((Hhi B.b2 : ℚ) : ℝ) ∧
      H ((a + b) / 2) ≤ ((Hhi (mHi B) : ℚ) : ℝ) := by
  obtain ⟨R1, _, R2, B1, _, B2, _⟩ := boxOk_real hbox
  obtain ⟨gaL, gaH, _, gmH, _, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
  have hr2pos : (0 : ℝ) < B.r2 := lt_of_lt_of_le R1 (le_trans hr1 hr2)
  have haHi_half : (B.r2 : ℝ) * B.b2 ≤ 1 / 2 := by nlinarith
  have hmHi_half : (B.b2 : ℝ) * (1 + B.r2) / 2 ≤ 1 / 2 := by nlinarith
  have hb_half : b ≤ 1 / 2 := hb2.trans B2
  have ha_half : a ≤ 1 / 2 := gaH.trans haHi_half
  obtain ⟨HaLo, _⟩ := H_bounds haLo
  obtain ⟨_, HaHi⟩ := H_bounds haHi
  obtain ⟨Hb1L, _⟩ := H_bounds hb1ok
  obtain ⟨_, Hb2H⟩ := H_bounds hb2ok
  obtain ⟨_, HmH⟩ := H_bounds hmHi
  rw [c_aLo] at HaLo
  rw [c_aHi] at HaHi
  rw [c_mHi] at HmH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact HaLo.trans (H_le_H (by positivity) gaL ha_half)
  · exact (H_le_H ha0.le gaH haHi_half).trans HaHi
  · exact Hb1L.trans (H_le_H B1.le hb1 hb_half)
  · exact (H_le_H hb0.le hb2 B2).trans Hb2H
  · exact (H_le_H (by positivity) gmH hmHi_half).trans HmH

/-- The entropy drop is at most `K (b-a)^2`. -/
theorem K_bound (B : Box3) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1' : b < 1)
    (hbox : boxOk B = true) (hK : 0 ≤ K B)
    (hr1 : (B.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (B.r2 : ℝ))
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ))
    (hHaL : ((Hlo (aLo B) : ℚ) : ℝ) ≤ H a) (hHbL : ((Hlo B.b1 : ℚ) : ℝ) ≤ H b)
    (hHmH : H ((a + b) / 2) ≤ ((Hhi (mHi B) : ℚ) : ℝ)) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((K B : ℚ) : ℝ) * (b - a) ^ 2 := by
  obtain ⟨R1, _, R2, B1, _, B2, _⟩ := boxOk_real hbox
  have hb0 : 0 < b := ha0.trans hab
  obtain ⟨_, _, gmL, gmH, gdL, gdH, grho⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  simp only [K]
  split_ifs with hcase
  · apply K1_bound (DHi := ((DHi B : ℚ) : ℝ)) (dLo := ((dLo B : ℚ) : ℝ))
    · rw [c_DHi, c_CLo]; linarith
    · exact_mod_cast hcase.1
    · rw [c_dLo]; exact gdL
    · exact c_K1 B
    · have h : (0 : ℚ) ≤ K B := hK
      simp only [K, if_pos hcase] at h
      exact_mod_cast h
  · rw [c_K2]
    obtain ⟨hL1, _⟩ := log_two_mem
    have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
    have hmHhalf : (B.b2 : ℝ) * (1 + B.r2) / 2 ≤ 1 / 2 := by nlinarith
    apply K3_bound ha0 hab hb1'
    · rw [c_rhoHi]; exact grho
    · rw [c_kapHi, c_dHi, c_mHi]
      have hden1 : (0 : ℝ) < 2 - a - b := by linarith
      have hden2 : (0 : ℝ) < 2 * (1 - (B.b2 : ℝ) * (1 + B.r2) / 2) := by linarith
      rw [div_le_div_iff₀ hden1 hden2]
      have h2 : 2 * (1 - (B.b2 : ℝ) * (1 + B.r2) / 2) ≤ 2 - a - b := by linarith
      have hd0 : 0 ≤ b - a := by linarith
      calc (b - a) * (2 * (1 - (B.b2 : ℝ) * (1 + B.r2) / 2)) ≤ (b - a) * (2 - a - b) :=
            mul_le_mul_of_nonneg_left h2 hd0
        _ ≤ (B.b2 : ℝ) * (1 - B.r1) * (2 - a - b) :=
            mul_le_mul_of_nonneg_right gdH hden1.le
    · rw [c_mLo]; positivity
    · rw [c_mLo]; exact gmL
    · rw [c_mHi]; exact gmH
    · rw [c_mHi]; linarith
    · exact LqLo_pos
    · exact hL1

theorem beta_bound (B : Box3) {a b : ℝ} (hab : a < b) (hb1' : b < 1) (hbox : boxOk B = true)
    (haL : (B.r1 : ℝ) * B.b1 ≤ a) (hb2 : b ≤ (B.b2 : ℝ)) (hb0 : 0 < b) :
    ((betaLo B : ℚ) : ℝ) ≤ 1 / (2 * (b * (1 - a))) := by
  obtain ⟨R1, _, _, B1, _, _, _⟩ := boxOk_real hbox
  rw [c_betaLo]
  have hbpos : 0 < b * (1 - a) := mul_pos hb0 (by linarith)
  apply one_div_le_one_div_of_le (by positivity)
  have h1 : 1 - a ≤ 1 - (B.r1 : ℝ) * B.b1 := by linarith
  have h2 : 0 ≤ 1 - a := by linarith
  have h3 : 2 * b * (1 - a) ≤ 2 * (B.b2 : ℝ) * (1 - a) := by nlinarith
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
  have h4 : 2 * (B.b2 : ℝ) * (1 - a) ≤ 2 * (B.b2 : ℝ) * (1 - (B.r1 : ℝ) * B.b1) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc 2 * (b * (1 - a)) = 2 * b * (1 - a) := by ring
    _ ≤ _ := h3.trans h4

theorem excess_bound (B : Box3) (vS vI : ℚ) {Δ d2 : ℝ} (hΔ0 : 0 ≤ Δ)
    (hKb : Δ ≤ ((K B : ℚ) : ℝ) * d2) :
    Δ * (((pbar vS vI : ℚ) : ℝ) - 4) ≤ ((K B : ℚ) : ℝ) * d2 * ((excess vS vI : ℚ) : ℝ) := by
  simp only [excess]
  split_ifs with hp
  · have hp' : (0 : ℝ) ≤ ((pbar vS vI : ℚ) : ℝ) - 4 := by
      have := (Rat.cast_le (K := ℝ)).mpr hp
      push_cast at this
      linarith
    push_cast
    exact mul_le_mul_of_nonneg_right hKb hp'
  · have hp' : ((pbar vS vI : ℚ) : ℝ) - 4 < 0 := by
      have : pbar vS vI - 4 < 0 := lt_of_not_ge hp
      have := (Rat.cast_lt (K := ℝ)).mpr this
      push_cast at this
      linarith
    push_cast
    have := mul_nonpos_of_nonneg_of_nonpos hΔ0 hp'.le
    linarith

/-- `interiorCost` in logarithms. -/
theorem interiorCost_eq_logs {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) (hb1 : b < 1) :
    interiorCost a b =
      (b - a) * (Real.log (b / a) + Real.log (1 - a) - Real.log (1 - b)) / (2 * Real.log 2) := by
  unfold interiorCost J
  rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb.ne',
    Real.log_div hb.ne' ha.ne']
  have hL := log_two_pos
  field_simp
  ring

/-- Mean-form lower bound for the parent cost `j`. -/
theorem jLo_le (B : Box3) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1' : b < 1)
    (hbox : boxOk B = true) (hr2ok : ptOk B.r2 = true) (haHi : ptOk (aHi B) = true)
    (hb1ok : ptOk B.b1 = true)
    (hr1 : (B.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (B.r2 : ℝ))
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ)) :
    ((jLo B : ℚ) : ℝ) ≤ interiorCost a b := by
  obtain ⟨R1, _, R2, B1, _, _, _⟩ := boxOk_real hbox
  have hb0 : 0 < b := ha0.trans hab
  obtain ⟨_, gaH, _, _, gdL, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have ha1 : a < 1 := by linarith
  rw [interiorCost_eq_logs ha0 hb0 ha1 hb1']
  obtain ⟨_, lr2, _, _⟩ := ptOk_sound hr2ok
  obtain ⟨_, _, laH, _⟩ := ptOk_sound haHi
  obtain ⟨_, _, _, lb1⟩ := ptOk_sound hb1ok
  rw [c_aHi] at laH
  have hr0 : 0 < a / b := div_pos ha0 hb0
  have hq1 : ((B.r2 : ℚ) : ℝ) > 0 := lt_of_lt_of_le hr0 hr2
  -- the three logarithms
  have t1 : -((lHi B.r2 : ℚ) : ℝ) ≤ Real.log (b / a) := by
    have : Real.log (b / a) = -Real.log (a / b) := by
      rw [← Real.log_inv, inv_div]
    rw [this]
    have := Real.log_le_log hr0 hr2
    linarith
  have t2 : ((l1Lo (aHi B) : ℚ) : ℝ) ≤ Real.log (1 - a) := by
    have h1 : 1 - (B.r2 : ℝ) * B.b2 ≤ 1 - a := by linarith
    have hpos : 0 < 1 - (B.r2 : ℝ) * B.b2 := by
      have := ptOk_pos haHi
      have h := (Rat.cast_lt (K := ℝ)).mpr this.2
      rw [c_aHi] at h
      push_cast at h
      linarith
    exact laH.trans (Real.log_le_log hpos h1)
  have t3 : -((l1Hi B.b1 : ℚ) : ℝ) ≤ -Real.log (1 - b) := by
    have h1 : 1 - b ≤ 1 - (B.b1 : ℝ) := by linarith
    have := Real.log_le_log (by linarith) h1
    linarith
  have hbr : ((jb B : ℚ) : ℝ) ≤ Real.log (b / a) + Real.log (1 - a) - Real.log (1 - b) := by
    simp only [jb]; push_cast; linarith
  have hbr0 : 0 ≤ Real.log (b / a) + Real.log (1 - a) - Real.log (1 - b) := by
    have e1 : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha0).mpr hab.le)
    have e2 : Real.log (1 - b) ≤ Real.log (1 - a) := Real.log_le_log (by linarith) (by linarith)
    linarith
  set X := Real.log (b / a) + Real.log (1 - a) - Real.log (1 - b) with hX
  have hmax : ((if 0 ≤ jb B then jb B else 0 : ℚ) : ℝ) ≤ X := by
    split_ifs
    · exact hbr
    · push_cast; exact hbr0
  have hmax0 : (0 : ℝ) ≤ ((if 0 ≤ jb B then jb B else 0 : ℚ) : ℝ) := by
    split_ifs with h
    · exact_mod_cast h
    · simp
  obtain ⟨_, hL2⟩ := log_two_mem
  have hL := log_two_pos
  have hdLo0 : (0 : ℝ) ≤ ((dLo B : ℚ) : ℝ) := by rw [c_dLo]; nlinarith
  have hjLo : ((jLo B : ℚ) : ℝ) =
      ((dLo B : ℚ) : ℝ) * ((if 0 ≤ jb B then jb B else 0 : ℚ) : ℝ) / (2 * ((LqHi : ℚ) : ℝ)) := by
    simp only [jLo]; push_cast; ring
  rw [hjLo]
  have hdd : ((dLo B : ℚ) : ℝ) ≤ b - a := by rw [c_dLo]; exact gdL
  have hnum : ((dLo B : ℚ) : ℝ) * ((if 0 ≤ jb B then jb B else 0 : ℚ) : ℝ) ≤ (b - a) * X :=
    mul_le_mul hdd hmax hmax0 (by linarith)
  calc ((dLo B : ℚ) : ℝ) * ((if 0 ≤ jb B then jb B else 0 : ℚ) : ℝ) / (2 * ((LqHi : ℚ) : ℝ)) ≤
        ((dLo B : ℚ) : ℝ) * ((if 0 ≤ jb B then jb B else 0 : ℚ) : ℝ) / (2 * Real.log 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ ≤ (b - a) * X / (2 * Real.log 2) := div_le_div_of_nonneg_right hnum (by positivity)

/-- Pure real assembly of the mean (unnormalized) form. -/
theorem mean_assemble {inc j Δ S d2 β βlo sLo dLo2 DHi pbar jL : ℝ}
    (hinc : inc ≤ Δ * pbar) (hjL : jL ≤ j) (hΔ : Δ ≤ DHi) (hpbar0 : 0 ≤ pbar)
    (hβ : βlo ≤ β) (hβlo0 : 0 ≤ βlo) (hd : dLo2 ≤ d2) (hdLo2 : 0 ≤ dLo2)
    (hS : sLo ≤ S) (hsLo : 0 ≤ sLo)
    (hmean : DHi * pbar ≤ jL + βlo * dLo2 * sLo) : inc ≤ j + d2 * β * S := by
  have h1 : Δ * pbar ≤ DHi * pbar := mul_le_mul_of_nonneg_right hΔ hpbar0
  have h2 : βlo * dLo2 ≤ β * d2 := mul_le_mul hβ hd hdLo2 (le_trans hβlo0 hβ)
  have h3 : βlo * dLo2 * sLo ≤ β * d2 * S :=
    mul_le_mul h2 hS hsLo (mul_nonneg (le_trans hβlo0 hβ) (le_trans hdLo2 hd))
  have e : β * d2 * S = d2 * β * S := by ring
  linarith

theorem betaLo_nonneg {B : Box3} (hbox : boxOk B = true) : (0 : ℝ) ≤ ((betaLo B : ℚ) : ℝ) := by
  obtain ⟨R1, R12, R2, B1, B12, B2, _⟩ := boxOk_real hbox
  rw [c_betaLo]
  apply div_nonneg zero_le_one
  have h1 : (B.r1 : ℝ) ≤ 1 := R12.trans R2
  have h2 : (B.b1 : ℝ) ≤ 1 / 2 := B12.trans B2
  have h3 : (B.r1 : ℝ) * B.b1 ≤ 1 * (1 / 2) := mul_le_mul h1 h2 B1.le zero_le_one
  have h4 : (0 : ℝ) ≤ B.b2 := le_trans B1.le B12
  have h5 : (0 : ℝ) ≤ 1 - (B.r1 : ℝ) * B.b1 := by linarith
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h4) h5
  exact this

theorem dLo_sq_le {B : Box3} {d : ℝ} (hbox : boxOk B = true) (hd : ((dLo B : ℚ) : ℝ) ≤ d) :
    ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) ≤ d ^ 2 := by
  obtain ⟨_, _, R2, B1, _, _, _⟩ := boxOk_real hbox
  have h0 : (0 : ℝ) ≤ ((dLo B : ℚ) : ℝ) := by rw [c_dLo]; exact mul_nonneg B1.le (by linarith)
  calc ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) ≤ d * d := mul_self_le_mul_self h0 hd
    _ = d ^ 2 := by ring

/-- The log-sum bonus with box constants: `Wlo (b-a)^2 ≤ j - 4Δ`. -/
theorem W_bound (B : Box3) {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1' : b < 1)
    (hbox : boxOk B = true)
    (hr1 : (B.r1 : ℝ) ≤ a / b) (hr2 : a / b ≤ (B.r2 : ℝ))
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ)) :
    4 * (H ((a + b) / 2) - (H a + H b) / 2) + (b - a) ^ 2 * ((Wlo B : ℚ) : ℝ) ≤ interiorCost a b := by
  obtain ⟨R1, _, R2, B1, _, B2, _⟩ := boxOk_real hbox
  have hb0 : 0 < b := ha0.trans hab
  obtain ⟨_, _, gmL, gmH, gdL, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hbonus := interiorCost_sub_four_drop ha0 hab hb1'
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hm0 : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
  have hr2pos : (0 : ℝ) < B.r2 := lt_of_lt_of_le R1 (le_trans hr1 hr2)
  have hmHpos : (0 : ℝ) < ((mHi B : ℚ) : ℝ) := by rw [c_mHi]; positivity
  have hmLlt : ((mLo B : ℚ) : ℝ) < 1 := by
    rw [c_mLo]; have := R1.le; nlinarith
  -- ρ ≥ ρlo
  have hρ : ((rhoLo B : ℚ) : ℝ) ≤ (b - a) / (a + b) := by
    rw [c_rhoLo]
    have har : a = (a / b) * b := by field_simp
    set r := a / b with hrdef
    have hr0 : 0 < r := div_pos ha0 hb0
    rw [har]
    have h1 : 0 < r * b + b := by positivity
    rw [div_le_div_iff₀ (by linarith) h1]
    have e : (1 - (B.r2 : ℝ)) * (r * b + b) = b * ((1 - B.r2) * (1 + r)) := by ring
    have e' : (b - r * b) * (1 + B.r2) = b * ((1 - r) * (1 + B.r2)) := by ring
    rw [e, e']
    apply mul_le_mul_of_nonneg_left _ hb0.le
    nlinarith
  have hρlo0 : (0 : ℝ) ≤ ((rhoLo B : ℚ) : ℝ) := by
    rw [c_rhoLo]; exact div_nonneg (by linarith) (by linarith)
  -- κ ≥ κlo
  have hκ : ((kapLo B : ℚ) : ℝ) ≤ (b - a) / (2 - a - b) := by
    rw [c_kapLo, c_dLo, c_mLo]
    have hden2 : (0 : ℝ) < 2 * (1 - (B.b1 : ℝ) * (1 + B.r1) / 2) := by linarith
    rw [div_le_div_iff₀ hden2 ht]
    have h1 : (B.b1 : ℝ) * (1 - B.r2) ≤ b - a := gdL
    have h2 : 2 - a - b ≤ 2 * (1 - (B.b1 : ℝ) * (1 + B.r1) / 2) := by linarith
    have h3 : (0 : ℝ) ≤ (B.b1 : ℝ) * (1 - B.r2) := mul_nonneg B1.le (by linarith)
    calc (B.b1 : ℝ) * (1 - B.r2) * (2 - a - b) ≤ (B.b1 : ℝ) * (1 - B.r2) *
          (2 * (1 - (B.b1 : ℝ) * (1 + B.r1) / 2)) := mul_le_mul_of_nonneg_left h2 h3
      _ ≤ (b - a) * (2 * (1 - (B.b1 : ℝ) * (1 + B.r1) / 2)) :=
          mul_le_mul_of_nonneg_right h1 hden2.le
  have hκlo0 : (0 : ℝ) ≤ ((kapLo B : ℚ) : ℝ) := by
    rw [c_kapLo, c_dLo, c_mLo]
    apply div_nonneg (mul_nonneg B1.le (by linarith))
    have : (B.b1 : ℝ) * (1 + B.r1) / 2 ≤ (a + b) / 2 := gmL
    linarith
  have hρ2 := pow_le_pow_left₀ hρlo0 hρ 2
  have hκ2 := pow_le_pow_left₀ hκlo0 hκ 2
  obtain ⟨_, hL2⟩ := log_two_mem
  have hL := log_two_pos
  have hLq : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := lt_of_lt_of_le hL hL2
  have t1 : ((rhoLo B : ℚ) : ℝ) ^ 2 / ((mHi B : ℚ) : ℝ) ≤ ((b - a) / (a + b)) ^ 2 / ((a + b) / 2) := by
    apply div_le_div₀ (by positivity) hρ2 hm0
    rw [c_mHi]; exact gmH
  have t2 : ((kapLo B : ℚ) : ℝ) ^ 2 / (1 - ((mLo B : ℚ) : ℝ)) ≤
      ((b - a) / (2 - a - b)) ^ 2 / (1 - (a + b) / 2) := by
    apply div_le_div₀ (by positivity) hκ2 hm1
    rw [c_mLo] at *; linarith
  have hsum := add_le_add t1 t2
  have hX0 : 0 ≤ ((rhoLo B : ℚ) : ℝ) ^ 2 / ((mHi B : ℚ) : ℝ) +
      ((kapLo B : ℚ) : ℝ) ^ 2 / (1 - ((mLo B : ℚ) : ℝ)) := by
    have : 0 < 1 - ((mLo B : ℚ) : ℝ) := by linarith
    positivity
  have hWle : ((Wlo B : ℚ) : ℝ) ≤ (((b - a) / (a + b)) ^ 2 / ((a + b) / 2) +
      ((b - a) / (2 - a - b)) ^ 2 / (1 - (a + b) / 2)) / (12 * Real.log 2) := by
    rw [c_Wlo]
    calc (((rhoLo B : ℚ) : ℝ) ^ 2 / ((mHi B : ℚ) : ℝ) +
          ((kapLo B : ℚ) : ℝ) ^ 2 / (1 - ((mLo B : ℚ) : ℝ))) / (12 * ((LqHi : ℚ) : ℝ)) ≤
          (((rhoLo B : ℚ) : ℝ) ^ 2 / ((mHi B : ℚ) : ℝ) +
          ((kapLo B : ℚ) : ℝ) ^ 2 / (1 - ((mLo B : ℚ) : ℝ))) / (12 * Real.log 2) :=
          div_le_div_of_nonneg_left hX0 (by positivity) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hsum (by positivity)
  have hd2 : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have key := mul_le_mul_of_nonneg_left hWle hd2
  have e : (b - a) ^ 2 * ((((b - a) / (a + b)) ^ 2 / ((a + b) / 2) +
      ((b - a) / (2 - a - b)) ^ 2 / (1 - (a + b) / 2)) / (12 * Real.log 2)) =
      (b - a) ^ 2 / (12 * Real.log 2) *
        (((b - a) / (a + b)) ^ 2 / ((a + b) / 2) + ((b - a) / (2 - a - b)) ^ 2 / (1 - (a + b) / 2)) := by
    ring
  linarith

set_option maxHeartbeats 1000000 in
/-- Soundness of a log-sum leaf. -/
theorem check_sound (B : Box3) (vS vI : ℚ) (hw : check B vS vI = true) : Good B := by
  intro k μ hμ hin
  obtain ⟨hr1, hr2, hb1, hb2, hE1, _⟩ := hin
  have hab := hμ.hab
  simp only [check, Bool.and_eq_true, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, haLo⟩, haHi⟩, hb1ok⟩, hb2ok⟩, hmHi⟩, hvS⟩, hvI⟩, hcommon⟩, hacc⟩ := hw
  simp only [decide_eq_true_eq] at hcommon
  obtain ⟨qsLo, qIHi⟩ := hcommon
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := μ.b_interior.2
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    law_H_bounds B ha0 hb0 hbox haLo haHi hb1ok hb2ok hmHi hr1 hr2 hb1 hb2
  obtain ⟨R1, _, R2, B1, _, _, _⟩ := boxOk_real hbox
  obtain ⟨gaL, _, _, _, gdL, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  set Δ := μ.entropyDrop with hΔ
  set s := μ.meanDeficit with hs
  set S : ℝ := (H μ.a + H μ.b) / 2 - B.E1 with hSdef
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hsdef : s = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    rw [hs]; unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  have hs0 : 0 ≤ s := μ.meanDeficit_mem.1
  have hsS : s ≤ S := by rw [hsdef, hSdef]; linarith
  have hS0 : 0 ≤ S := hs0.trans hsS
  have hS_lo : ((sLo B : ℚ) : ℝ) ≤ S := by rw [c_sLo, c_CLo, hSdef]; linarith
  have hS_hi : S ≤ ((sHi B : ℚ) : ℝ) := by rw [c_sHi, c_CHi, hSdef]; linarith
  have hI_hi : Δ + S ≤ ((IHi B : ℚ) : ℝ) := by rw [c_IHi, hΔdef, hSdef]; linarith
  have hIHi1 : ((IHi B : ℚ) : ℝ) < 1 := by exact_mod_cast qIHi
  have hI1 : Δ + S < 1 := lt_of_le_of_lt hI_hi hIHi1
  have htrap := P_trapezoid hS0 (le_add_of_nonneg_left hΔ0) hI1
  have hPS := anchorOk_sound hvS hS0 hS_hi
  have hPI := anchorOk_sound hvI (by linarith) hI_hi
  have hinc : P (Δ + S) - P S ≤ Δ * ((pbar vS vI : ℚ) : ℝ) := by
    rw [c_pbar]
    have h1 : (Δ + S - S) = Δ := by ring
    rw [h1] at htrap
    have := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith
  have hbeta := beta_bound B hab hb1' hbox gaL hb2 hb0
  have hsLoR : (0 : ℝ) ≤ ((sLo B : ℚ) : ℝ) := by exact_mod_cast qsLo
  have hbpos : 0 < μ.b * (1 - μ.a) := mul_pos hb0 (by linarith)
  have hj := four_entropyDrop_le_interiorCost ha0 ha1 hb0 hb1'
  rw [← hΔdef] at hj
  set α : ℝ := (μ.b - μ.a) ^ 2 * (1 / (2 * (μ.b * (1 - μ.a)))) with hα
  -- G(S) ≥ 0 from either acceptance form
  have hGS : P (Δ + S) - P S ≤ interiorCost μ.a μ.b + α * S := by
    rcases hacc with hn | hm
    · simp only [normOk, decide_eq_true_eq] at hn
      obtain ⟨qK, qfin⟩ := hn
      have hKb := K_bound B ha0 hab hb1' hbox qK hr1 hr2 hb1 hb2 hHaL hHbL hHmH
      have hexc := excess_bound B vS vI hΔ0 hKb
      have hfinR : ((K B : ℚ) : ℝ) * ((excess vS vI : ℚ) : ℝ) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sLo B : ℚ) : ℝ) := by exact_mod_cast qfin
      have hjW := W_bound B ha0 hab hb1' hbox hr1 hr2 hb1 hb2
      rw [← hΔdef] at hjW
      have := assembleW hinc hjW hexc hbeta (by positivity) hS_lo hsLoR (sq_nonneg _) hfinR
      rw [hα]
      linarith only [this]
    · simp only [meanOk, Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨_, hr2ok⟩, qmean⟩ := hm
      have hjl := jLo_le B ha0 hab hb1' hbox hr2ok haHi hb1ok hr1 hr2 hb1 hb2
      have hmeanR : ((DHi B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ) ≤ ((jLo B : ℚ) : ℝ) +
          ((betaLo B : ℚ) : ℝ) * (((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ)) * ((sLo B : ℚ) : ℝ) := by
        exact_mod_cast qmean
      have hΔle : Δ ≤ ((DHi B : ℚ) : ℝ) := by rw [c_DHi, c_CLo, hΔdef]; linarith
      have hpbar0 : (0 : ℝ) ≤ ((pbar vS vI : ℚ) : ℝ) := by
        have h4 : (4 : ℝ) ≤ P1 S := by
          by_cases hS : S = 0
          · rw [hS, P1_zero]
          · rw [P1_eq_deriv (lt_of_le_of_ne hS0 (Ne.symm hS))]
            exact four_le_deriv_P (lt_of_le_of_ne hS0 (Ne.symm hS)) (by linarith)
        have h4' : (4 : ℝ) ≤ P1 (Δ + S) := by
          by_cases hS : Δ + S = 0
          · rw [hS, P1_zero]
          · have hpos : 0 < Δ + S := lt_of_le_of_ne (by linarith) (Ne.symm hS)
            rw [P1_eq_deriv hpos]
            exact four_le_deriv_P hpos hI1
        rw [c_pbar]; linarith
      have hdd := dLo_sq_le hbox (show ((dLo B : ℚ) : ℝ) ≤ μ.b - μ.a by rw [c_dLo]; exact gdL)
      have hdLo2 : (0 : ℝ) ≤ ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) := mul_self_nonneg _
      have := mean_assemble hinc hjl hΔle hpbar0 hbeta (betaLo_nonneg hbox) hdd hdLo2 hS_lo
        hsLoR hmeanR
      rw [hα]
      linarith only [this]
  have hend : 0 ≤ Scalar.gap (interiorCost μ.a μ.b) α Δ S := by
    unfold Scalar.gap; linarith
  have hzero : P Δ ≤ interiorCost μ.a μ.b := by
    rw [hΔdef]; exact deterministic_cap_bound ha0 ha1 hb0 hb1'
  have hcrit := Scalar.gap_endpoint_criterion hΔ0 hS0 hI1 hzero hend hs0 hsS
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab.le, min_eq_left hab.le]
  have hfloor : μ.psiLogSumCostFloor = interiorCost μ.a μ.b + α * s := by
    unfold InteriorLaw.psiLogSumCostFloor
    rw [hV, hsdef, hα]
    unfold InteriorLaw.meanEntropy
    field_simp
    ring
  have hmain : μ.splitBound ≤ μ.cost := by
    have e : μ.splitBound = P (Δ + s) - P s := rfl
    rw [e]
    calc P (Δ + s) - P s ≤ interiorCost μ.a μ.b + α * s := hcrit
      _ = μ.psiLogSumCostFloor := hfloor.symm
      _ ≤ μ.cost := μ.psiLogSumCostFloor_le_cost
  exact μ.gap_le_of_splitBound hμ.hactive.le hmain

end CKLaneE.LS

#check @CKLaneE.LS.check_sound
#print axioms CKLaneE.LS.check_sound

end


