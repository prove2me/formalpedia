-- Prove2me | Definitions.Def_CK_CKLaneE_CertLSK
-- name    : CK_CKLaneE_CertLSK
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:14:42.258409+00:00
-- url     : https://prove2.me/theorems/9324487f-fdd7-49c4-aca4-c26fd6b2e0c0
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertLSK` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertLSK` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertLSK` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertLSK (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertLSK.lean)

import Definitions.Def_CK_CKLaneE_KappaFloor

-- ===== source module CKLaneE.CertLSK =====
section

/-!
# Lane E: relative-floor log-sum certificate with the enhanced floor (`lsk`)

`CKLaneE.LSR` with the log-sum coefficient `β = 1/(2 b (1-a))` replaced by the enhanced
`βκ = 1/(b (1-a) (2-a))` from `CKLaneE.KF.cost_floor_sameSide` (factor `2/(2-a)`, a lower bound of the
archive's `κ(a)`); box bound `betaK = 1/(b2 (1-aLo) (2-aLo))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.LSK

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS CKLaneE.DT
open CKLaneE.LS2 (P1_mix affine_mix)
open CKLaneE.LS3 (Dm Dm_bound)
open CKLaneE.LSR (sLoR sHiR IHiR)
open CKLaneE.NLS (box_geometry)

section defs
variable (B : Box3) (t0 : ℚ)

def betaK : ℚ := 1 / (B.b2 * (1 - aLo B) * (2 - aLo B))
def tI0 : ℚ := if IHiR B t0 ≤ sLoR B t0 + Dm B then IHiR B t0 else sLoR B t0 + Dm B
def tI1 : ℚ := sHiR B t0 + Dm B

def norm2 (v0S v0I v1S v1I : ℚ) : Bool :=
  decide (Kx B * (pbar v0S v0I - 4) ≤ Wlo B + betaK B * sLoR B t0 ∧
    Kx B * (pbar v1S v1I - 4) ≤ Wlo B + betaK B * sHiR B t0)

def mean2 (v0S v0I v1S v1I : ℚ) : Bool :=
  decide (B.r2 < 1) && ptOk B.r2 &&
    decide (Dm B * pbar v0S v0I ≤ jLo B + betaK B * (dLo B * dLo B) * sLoR B t0 ∧
      Dm B * pbar v1S v1I ≤ jLo B + betaK B * (dLo B * dLo B) * sHiR B t0)

def check (v0S v0I v1S v1I : ℚ) : Bool :=
  boxOk B && decide (0 ≤ t0 ∧ t0 ≤ 1) && ptOk (aLo B) && ptOk (aHi B) && ptOk B.b1 && ptOk B.b2 &&
    ptOk (mHi B) &&
    anchorOk v0S (sLoR B t0) && anchorOk v0I (tI0 B t0) && anchorOk v1S (sHiR B t0) &&
    anchorOk v1I (tI1 B t0) &&
    decide (0 ≤ K B ∧ 0 ≤ sLoR B t0 ∧ tI1 B t0 < 1) &&
    (norm2 B t0 v0S v0I v1S v1I || mean2 B t0 v0S v0I v1S v1I)

end defs

set_option maxHeartbeats 1000000 in
/-- Soundness of an `lsk` leaf (relative floor, enhanced log-sum coefficient). -/
theorem check_sound (B : Box3) (t0 : ℚ) (v0S v0I v1S v1I : ℚ)
    (hw : check B t0 v0S v0I v1S v1I = true) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
      (B.r1 : ℝ) ≤ μ.a / μ.b → μ.a / μ.b ≤ (B.r2 : ℝ) → (B.b1 : ℝ) ≤ μ.b → μ.b ≤ (B.b2 : ℝ) →
      (t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy →
      phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost := by
  intro k μ hab hr1 hr2 hb1 hb2 hE hact
  simp only [check, Bool.and_eq_true, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, qt0⟩, haLo⟩, haHi⟩, hb1ok⟩, hb2ok⟩, hmHi⟩, hv0S⟩, hv0I⟩, hv1S⟩, hv1I⟩,
    hcommon⟩, hacc⟩ := hw
  simp only [decide_eq_true_eq] at qt0
  obtain ⟨qt00, qt01⟩ := qt0
  have ht0R : (0 : ℝ) ≤ t0 := by exact_mod_cast qt00
  have ht1R : (t0 : ℝ) ≤ 1 := by exact_mod_cast qt01
  simp only [decide_eq_true_eq] at hcommon
  obtain ⟨qK, qsLo, qtI1⟩ := hcommon
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := μ.b_interior.2
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    law_H_bounds B ha0 hb0 hbox haLo haHi hb1ok hb2ok hmHi hr1 hr2 hb1 hb2
  obtain ⟨R1, _, R2, B1, _, B2h, _⟩ := boxOk_real hbox
  obtain ⟨gaL, _, _, _, gdL, gdH, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  set Δ := μ.entropyDrop with hΔ
  set s := μ.meanDeficit with hs
  set S : ℝ := (1 - (t0 : ℝ)) * ((H μ.a + H μ.b) / 2) with hSdef
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hsdef : s = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    rw [hs]; unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  have hs0 : 0 ≤ s := μ.meanDeficit_mem.1
  have hsS : s ≤ S := by
    rw [hsdef, hSdef]
    have e : (1 - (t0 : ℝ)) * ((H μ.a + H μ.b) / 2) =
        (H μ.a + H μ.b) / 2 - (t0 : ℝ) * ((H μ.a + H μ.b) / 2) := by ring
    rw [e]; linarith
  have hS0 : 0 ≤ S := hs0.trans hsS
  have hCLo : ((CLo B : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by rw [c_CLo]; linarith
  have hCHi : (H μ.a + H μ.b) / 2 ≤ ((CHi B : ℚ) : ℝ) := by rw [c_CHi]; linarith
  have e_sLo : ((sLoR B t0 : ℚ) : ℝ) = ((CLo B : ℚ) : ℝ) * (1 - (t0 : ℝ)) := by
    simp only [sLoR]; push_cast; ring
  have e_sHi : ((sHiR B t0 : ℚ) : ℝ) = ((CHi B : ℚ) : ℝ) * (1 - (t0 : ℝ)) := by
    simp only [sHiR]; push_cast; ring
  have e_IHi : ((IHiR B t0 : ℚ) : ℝ) = ((Hhi (mHi B) : ℚ) : ℝ) - (t0 : ℝ) * ((CLo B : ℚ) : ℝ) := by
    simp only [IHiR]; push_cast; ring
  have h1t : (0 : ℝ) ≤ 1 - (t0 : ℝ) := by linarith
  have hS_lo : ((sLoR B t0 : ℚ) : ℝ) ≤ S := by
    rw [e_sLo, hSdef, mul_comm]; exact mul_le_mul_of_nonneg_left hCLo h1t
  have hS_hi : S ≤ ((sHiR B t0 : ℚ) : ℝ) := by
    rw [e_sHi, hSdef, mul_comm ((CHi B : ℚ) : ℝ)]; exact mul_le_mul_of_nonneg_left hCHi h1t
  have hI_hi : Δ + S ≤ ((IHiR B t0 : ℚ) : ℝ) := by
    rw [e_IHi, hΔdef, hSdef]
    have : (t0 : ℝ) * ((CLo B : ℚ) : ℝ) ≤ (t0 : ℝ) * ((H μ.a + H μ.b) / 2) :=
      mul_le_mul_of_nonneg_left hCLo ht0R
    have e : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 + (1 - (t0 : ℝ)) * ((H μ.a + H μ.b) / 2) =
        H ((μ.a + μ.b) / 2) - (t0 : ℝ) * ((H μ.a + H μ.b) / 2) := by ring
    rw [e]; linarith
  have hsLoR : (0 : ℝ) ≤ ((sLoR B t0 : ℚ) : ℝ) := by exact_mod_cast qsLo
  have hK0 : (0 : ℝ) ≤ ((K B : ℚ) : ℝ) := by exact_mod_cast qK
  have hKb0 := K_bound B ha0 hab hb1' hbox qK hr1 hr2 hb1 hb2 hHaL hHbL hHmH
  have hΔD0 : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 ≤ ((DHi B : ℚ) : ℝ) := by
    rw [c_DHi, c_CLo]; linarith
  obtain ⟨hΔDx, hKb, hKx0⟩ := drop_bounds B hbox ha0 hab hb1' hr1 hr2 hb1 hb2 hΔD0 hK0 hKb0
  rw [← hΔdef] at hΔDx hKb
  have hd0 : (0 : ℝ) ≤ μ.b - μ.a := by linarith
  have hΔDm : Δ ≤ ((Dm B : ℚ) : ℝ) :=
    Dm_bound B hKx0 hd0 (by rw [c_dHi]; exact gdH) hKb hΔDx
  -- the four anchor points
  have htI1 : ((tI1 B t0 : ℚ) : ℝ) = ((sHiR B t0 : ℚ) : ℝ) + ((Dm B : ℚ) : ℝ) := by
    simp only [tI1]; push_cast; ring
  have htI1lt : ((tI1 B t0 : ℚ) : ℝ) < 1 := by exact_mod_cast qtI1
  have h1lt : ((sHiR B t0 : ℚ) : ℝ) + Δ < 1 := by rw [htI1] at htI1lt; linarith
  have hI1 : Δ + S < 1 := by linarith
  have hx0I : ((sLoR B t0 : ℚ) : ℝ) + Δ ≤ ((tI0 B t0 : ℚ) : ℝ) := by
    simp only [tI0]
    split_ifs
    · linarith
    · push_cast; linarith
  have hPA0 := anchorOk_sound hv0S hsLoR (le_refl _)
  have hPB0 := anchorOk_sound hv0I (by linarith) hx0I
  have hPA1 := anchorOk_sound hv1S (by linarith) (le_refl _)
  have hPB1 := anchorOk_sound hv1I (by linarith) (show ((sHiR B t0 : ℚ) : ℝ) + Δ ≤ ((tI1 B t0 : ℚ) : ℝ) by
    rw [htI1]; linarith)
  obtain ⟨t, ht0, ht1, hSe, hmix⟩ := P1_mix hsLoR hS_lo hS_hi hΔ0 h1lt hPA0 hPB0 hPA1 hPB1
  set P0 : ℝ := ((pbar v0S v0I : ℚ) : ℝ) with hP0
  set Q1 : ℝ := ((pbar v1S v1I : ℚ) : ℝ) with hQ1
  have eP0 : P0 = (((P1up v0S : ℚ) : ℝ) + ((P1up v0I : ℚ) : ℝ)) / 2 := c_pbar v0S v0I
  have eQ1 : Q1 = (((P1up v1S : ℚ) : ℝ) + ((P1up v1I : ℚ) : ℝ)) / 2 := c_pbar v1S v1I
  set p : ℝ := (1 - t) * P0 + t * Q1 with hp
  set pm : ℝ := (P1 S + P1 (Δ + S)) / 2 with hpm
  have hpm_le : pm ≤ p := by
    rw [hpm, hp, eP0, eQ1]
    have e : (1 - t) * ((((P1up v0S : ℚ) : ℝ) + ((P1up v0I : ℚ) : ℝ)) / 2) +
        t * ((((P1up v1S : ℚ) : ℝ) + ((P1up v1I : ℚ) : ℝ)) / 2) =
        ((1 - t) * (((P1up v0S : ℚ) : ℝ) + ((P1up v0I : ℚ) : ℝ)) +
          t * (((P1up v1S : ℚ) : ℝ) + ((P1up v1I : ℚ) : ℝ))) / 2 := by ring
    rw [e]
    linarith
  have h4S : (4 : ℝ) ≤ P1 S := by
    by_cases hS : S = 0
    · rw [hS, P1_zero]
    · rw [P1_eq_deriv (lt_of_le_of_ne hS0 (Ne.symm hS))]
      exact four_le_deriv_P (lt_of_le_of_ne hS0 (Ne.symm hS)) (by linarith)
  have h4I : (4 : ℝ) ≤ P1 (Δ + S) := by
    by_cases hS : Δ + S = 0
    · rw [hS, P1_zero]
    · have hpos : 0 < Δ + S := lt_of_le_of_ne (by linarith) (Ne.symm hS)
      rw [P1_eq_deriv hpos]
      exact four_le_deriv_P hpos hI1
  have hpm4 : (4 : ℝ) ≤ pm := by rw [hpm]; linarith
  have htrap := P_trapezoid hS0 (le_add_of_nonneg_left hΔ0) hI1
  have hinc : P (Δ + S) - P S ≤ Δ * pm := by
    have h1 : (Δ + S - S) = Δ := by ring
    rw [h1] at htrap
    rw [hpm]
    have e : Δ * ((P1 S + P1 (Δ + S)) / 2) = Δ * (P1 S + P1 (Δ + S)) / 2 := by ring
    rw [e]
    exact htrap
  have hprod : 0 < μ.b * (1 - μ.a) * (2 - μ.a) := mul_pos (mul_pos hb0 (by linarith)) (by linarith)
  have hbeta : ((betaK B : ℚ) : ℝ) ≤ 1 / (μ.b * (1 - μ.a) * (2 - μ.a)) := by
    have ec : ((betaK B : ℚ) : ℝ) = 1 / ((B.b2 : ℝ) * (1 - (B.r1 : ℝ) * B.b1) * (2 - (B.r1 : ℝ) * B.b1)) := by
      simp only [betaK, aLo]; push_cast; ring
    rw [ec]
    apply one_div_le_one_div_of_le hprod
    have h1 : 0 ≤ 1 - μ.a := by linarith
    have h2 : 1 - μ.a ≤ 1 - (B.r1 : ℝ) * B.b1 := by linarith
    have h3 : 2 - μ.a ≤ 2 - (B.r1 : ℝ) * B.b1 := by linarith
    have hb2p : (0 : ℝ) ≤ B.b2 := by linarith
    calc μ.b * (1 - μ.a) * (2 - μ.a) ≤ (B.b2 : ℝ) * (1 - μ.a) * (2 - μ.a) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 h1) (by linarith)
      _ ≤ (B.b2 : ℝ) * (1 - (B.r1 : ℝ) * B.b1) * (2 - μ.a) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hb2p) (by linarith)
      _ ≤ (B.b2 : ℝ) * (1 - (B.r1 : ℝ) * B.b1) * (2 - (B.r1 : ℝ) * B.b1) := by
          apply mul_le_mul_of_nonneg_left h3 (mul_nonneg hb2p (by linarith))
  have hbetaK0 : (0 : ℝ) ≤ ((betaK B : ℚ) : ℝ) := by
    have ec : ((betaK B : ℚ) : ℝ) = 1 / ((B.b2 : ℝ) * (1 - (B.r1 : ℝ) * B.b1) * (2 - (B.r1 : ℝ) * B.b1)) := by
      simp only [betaK, aLo]; push_cast; ring
    rw [ec]
    have hb2p : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
    have hq : (B.r1 : ℝ) * B.b1 ≤ μ.a := gaL
    apply div_nonneg zero_le_one
    apply mul_nonneg (mul_nonneg hb2p.le (by linarith)) (by linarith)
  have hj := four_entropyDrop_le_interiorCost ha0 ha1 hb0 hb1'
  rw [← hΔdef] at hj
  set α : ℝ := (μ.b - μ.a) ^ 2 * (1 / (μ.b * (1 - μ.a) * (2 - μ.a))) with hα
  have hGS : P (Δ + S) - P S ≤ interiorCost μ.a μ.b + α * S := by
    rcases hacc with hn | hm
    · simp only [norm2, decide_eq_true_eq] at hn
      obtain ⟨qfin0, qfin1⟩ := hn
      have hfin0 : ((Kx B : ℚ) : ℝ) * (P0 - 4) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * ((sLoR B t0 : ℚ) : ℝ) := by
        rw [hP0]; exact_mod_cast qfin0
      have hfin1 : ((Kx B : ℚ) : ℝ) * (Q1 - 4) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * ((sHiR B t0 : ℚ) : ℝ) := by
        rw [hQ1]; exact_mod_cast qfin1
      have hfin : ((Kx B : ℚ) : ℝ) * (p - 4) ≤ ((Wlo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * S := by
        have hm := affine_mix ht0 ht1 hfin0 hfin1
        have e1 : ((Kx B : ℚ) : ℝ) * (p - 4) =
            (1 - t) * (((Kx B : ℚ) : ℝ) * (P0 - 4)) + t * (((Kx B : ℚ) : ℝ) * (Q1 - 4)) := by
          rw [hp]; ring
        have e2 : ((Wlo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * S =
            (1 - t) * (((Wlo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * ((sLoR B t0 : ℚ) : ℝ)) +
              t * (((Wlo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * ((sHiR B t0 : ℚ) : ℝ)) := by
          rw [hSe]; ring
        rw [e1, e2]; exact hm
      have hd2 : (0 : ℝ) ≤ (μ.b - μ.a) ^ 2 := sq_nonneg _
      have hKd2 : (0 : ℝ) ≤ ((Kx B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 := mul_nonneg hKx0 hd2
      have hexc : Δ * (pm - 4) ≤ ((Kx B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (p - 4) := by
        have a1 : Δ * (pm - 4) ≤ ((Kx B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (pm - 4) :=
          mul_le_mul_of_nonneg_right hKb (by linarith)
        have a2 : ((Kx B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (pm - 4) ≤
            ((Kx B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (p - 4) :=
          mul_le_mul_of_nonneg_left (by linarith) hKd2
        exact a1.trans a2
      have hjW := W_bound B ha0 hab hb1' hbox hr1 hr2 hb1 hb2
      rw [← hΔdef] at hjW
      have := assembleW hinc hjW hexc hbeta (div_nonneg zero_le_one hprod.le) (le_refl S) hS0 hd2 hfin
      rw [hα]
      linarith only [this]
    · simp only [mean2, Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨_, hr2ok⟩, qm0, qm1⟩ := hm
      have hjl := jLo_le B ha0 hab hb1' hbox hr2ok haHi hb1ok hr1 hr2 hb1 hb2
      set dd : ℝ := ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) with hdd_def
      have hm0 : ((Dm B : ℚ) : ℝ) * P0 ≤ ((jLo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * dd *
          ((sLoR B t0 : ℚ) : ℝ) := by
        rw [hP0, hdd_def]; exact_mod_cast qm0
      have hm1 : ((Dm B : ℚ) : ℝ) * Q1 ≤ ((jLo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * dd *
          ((sHiR B t0 : ℚ) : ℝ) := by
        rw [hQ1, hdd_def]; exact_mod_cast qm1
      have hmean : ((Dm B : ℚ) : ℝ) * p ≤ ((jLo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * dd * S := by
        have hm := affine_mix ht0 ht1 hm0 hm1
        have e1 : ((Dm B : ℚ) : ℝ) * p =
            (1 - t) * (((Dm B : ℚ) : ℝ) * P0) + t * (((Dm B : ℚ) : ℝ) * Q1) := by
          rw [hp]; ring
        have e2 : ((jLo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * dd * S =
            (1 - t) * (((jLo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * dd * ((sLoR B t0 : ℚ) : ℝ)) +
              t * (((jLo B : ℚ) : ℝ) + ((betaK B : ℚ) : ℝ) * dd * ((sHiR B t0 : ℚ) : ℝ)) := by
          rw [hSe]; ring
        rw [e1, e2]; exact hm
      have hp0 : (0 : ℝ) ≤ p := by linarith
      have hinc' : P (Δ + S) - P S ≤ Δ * p :=
        hinc.trans (mul_le_mul_of_nonneg_left hpm_le hΔ0)
      have hdd := dLo_sq_le hbox (show ((dLo B : ℚ) : ℝ) ≤ μ.b - μ.a by rw [c_dLo]; exact gdL)
      have hdLo2 : (0 : ℝ) ≤ dd := mul_self_nonneg _
      have := mean_assemble hinc' hjl hΔDm hp0 hbeta hbetaK0 hdd hdLo2 (le_refl S)
        hS0 hmean
      rw [hα]
      linarith only [this]
  have hend : 0 ≤ Scalar.gap (interiorCost μ.a μ.b) α Δ S := by
    unfold Scalar.gap; linarith
  have hzero : P Δ ≤ interiorCost μ.a μ.b := by
    rw [hΔdef]; exact deterministic_cap_bound ha0 ha1 hb0 hb1'
  have hcrit := Scalar.gap_endpoint_criterion hΔ0 hS0 hI1 hzero hend hs0 hsS
  have hmain : μ.splitBound ≤ μ.cost := by
    have e : μ.splitBound = P (Δ + s) - P s := rfl
    rw [e]
    have hfl := KF.cost_floor_sameSide μ hab.le (hb2.trans B2h)
    calc P (Δ + s) - P s ≤ interiorCost μ.a μ.b + α * s := hcrit
      _ ≤ μ.cost := by rw [hα]; exact hfl
  exact μ.gap_le_of_splitBound hact hmain

end CKLaneE.LSK

#check @CKLaneE.LSK.check_sound
#print axioms CKLaneE.LSK.check_sound

end


