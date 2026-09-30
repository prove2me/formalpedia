-- Prove2me | Definitions.Def_CK_CKLaneE_CertLS3
-- name    : CK_CKLaneE_CertLS3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:56:56.129567+00:00
-- url     : https://prove2.me/theorems/f08cf2ab-2287-477c-b83f-d4083037841e
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertLS3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertLS3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertLS3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertLS3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertLS3.lean)

import Definitions.Def_CK_CKLaneE_CertLS2
import Definitions.Def_CK_CKLaneE_DropTight

-- ===== source module CKLaneE.CertLS3 =====
section

/-!
# Lane E: log-sum certificate `ls3` (= `ls2` with the tight drop bounds of `CKLaneE.DT`)

Identical to `CKLaneE.LS2` except that the entropy-drop bounds are `Kx = min(K, Dt/dLo²)` (normalized
form) and `Dm3 = min(Kx dHi², Dx)`, `Dx = min(DHi, Dt)` (mean form and slope-anchor targets), where `Dt`
is the tight box bound proved in `CKLaneE.DT.drop_bounds`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.LS3

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS CKLaneE.DT
open CKLaneE.LS2 (P1_mix affine_mix)
open CKLaneE.NLS (box_geometry)

section defs
variable (B : Box3)

def Dm : ℚ := if Kx B * (dHi B * dHi B) ≤ Dx B then Kx B * (dHi B * dHi B) else Dx B
def tI0 : ℚ := if IHi B ≤ sLo B + Dm B then IHi B else sLo B + Dm B
def tI1 : ℚ := sHi B + Dm B

def norm2 (v0S v0I v1S v1I : ℚ) : Bool :=
  decide (Kx B * (pbar v0S v0I - 4) ≤ Wlo B + betaLo B * sLo B ∧
    Kx B * (pbar v1S v1I - 4) ≤ Wlo B + betaLo B * sHi B)

def mean2 (v0S v0I v1S v1I : ℚ) : Bool :=
  decide (B.r2 < 1) && ptOk B.r2 &&
    decide (Dm B * pbar v0S v0I ≤ jLo B + betaLo B * (dLo B * dLo B) * sLo B ∧
      Dm B * pbar v1S v1I ≤ jLo B + betaLo B * (dLo B * dLo B) * sHi B)

def check (v0S v0I v1S v1I : ℚ) : Bool :=
  boxOk B && ptOk (aLo B) && ptOk (aHi B) && ptOk B.b1 && ptOk B.b2 && ptOk (mHi B) &&
    anchorOk v0S (sLo B) && anchorOk v0I (tI0 B) && anchorOk v1S (sHi B) && anchorOk v1I (tI1 B) &&
    decide (0 ≤ K B ∧ 0 ≤ sLo B ∧ tI1 B < 1) &&
    (norm2 B v0S v0I v1S v1I || mean2 B v0S v0I v1S v1I)

end defs

theorem Dm_bound (B : Box3) {Δ d : ℝ} (hK0 : (0 : ℝ) ≤ ((Kx B : ℚ) : ℝ)) (hd0 : 0 ≤ d)
    (hd : d ≤ ((dHi B : ℚ) : ℝ)) (hΔK : Δ ≤ ((Kx B : ℚ) : ℝ) * d ^ 2)
    (hΔD : Δ ≤ ((Dx B : ℚ) : ℝ)) : Δ ≤ ((Dm B : ℚ) : ℝ) := by
  simp only [Dm]
  split_ifs
  · push_cast
    have h1 : d ^ 2 ≤ ((dHi B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ) := by
      rw [sq]; exact mul_le_mul hd hd hd0 (hd0.trans hd)
    exact hΔK.trans (mul_le_mul_of_nonneg_left h1 hK0)
  · exact hΔD

set_option maxHeartbeats 1000000 in
/-- Soundness of an `ls3` leaf. -/
theorem check_sound (B : Box3) (v0S v0I v1S v1I : ℚ) (hw : check B v0S v0I v1S v1I = true) :
    Good B := by
  intro k μ hμ hin
  obtain ⟨hr1, hr2, hb1, hb2, hE1, _⟩ := hin
  have hab := hμ.hab
  simp only [check, Bool.and_eq_true, Bool.or_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, haLo⟩, haHi⟩, hb1ok⟩, hb2ok⟩, hmHi⟩, hv0S⟩, hv0I⟩, hv1S⟩, hv1I⟩,
    hcommon⟩, hacc⟩ := hw
  simp only [decide_eq_true_eq] at hcommon
  obtain ⟨qK, qsLo, qtI1⟩ := hcommon
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := μ.b_interior.2
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    law_H_bounds B ha0 hb0 hbox haLo haHi hb1ok hb2ok hmHi hr1 hr2 hb1 hb2
  obtain ⟨R1, _, R2, B1, _, _, _⟩ := boxOk_real hbox
  obtain ⟨gaL, _, _, _, gdL, gdH, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
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
  have hsLoR : (0 : ℝ) ≤ ((sLo B : ℚ) : ℝ) := by exact_mod_cast qsLo
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
  have htI1 : ((tI1 B : ℚ) : ℝ) = ((sHi B : ℚ) : ℝ) + ((Dm B : ℚ) : ℝ) := by
    simp only [tI1]; push_cast; ring
  have htI1lt : ((tI1 B : ℚ) : ℝ) < 1 := by exact_mod_cast qtI1
  have h1lt : ((sHi B : ℚ) : ℝ) + Δ < 1 := by rw [htI1] at htI1lt; linarith
  have hI1 : Δ + S < 1 := by linarith
  have hx0I : ((sLo B : ℚ) : ℝ) + Δ ≤ ((tI0 B : ℚ) : ℝ) := by
    simp only [tI0]
    split_ifs
    · linarith
    · push_cast; linarith
  have hPA0 := anchorOk_sound hv0S hsLoR (le_refl _)
  have hPB0 := anchorOk_sound hv0I (by linarith) hx0I
  have hPA1 := anchorOk_sound hv1S (by linarith) (le_refl _)
  have hPB1 := anchorOk_sound hv1I (by linarith) (show ((sHi B : ℚ) : ℝ) + Δ ≤ ((tI1 B : ℚ) : ℝ) by
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
  have hbeta := beta_bound B hab hb1' hbox gaL hb2 hb0
  have hj := four_entropyDrop_le_interiorCost ha0 ha1 hb0 hb1'
  rw [← hΔdef] at hj
  set α : ℝ := (μ.b - μ.a) ^ 2 * (1 / (2 * (μ.b * (1 - μ.a)))) with hα
  have hGS : P (Δ + S) - P S ≤ interiorCost μ.a μ.b + α * S := by
    rcases hacc with hn | hm
    · simp only [norm2, decide_eq_true_eq] at hn
      obtain ⟨qfin0, qfin1⟩ := hn
      have hfin0 : ((Kx B : ℚ) : ℝ) * (P0 - 4) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sLo B : ℚ) : ℝ) := by
        rw [hP0]; exact_mod_cast qfin0
      have hfin1 : ((Kx B : ℚ) : ℝ) * (Q1 - 4) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sHi B : ℚ) : ℝ) := by
        rw [hQ1]; exact_mod_cast qfin1
      have hfin : ((Kx B : ℚ) : ℝ) * (p - 4) ≤ ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * S := by
        have hm := affine_mix ht0 ht1 hfin0 hfin1
        have e1 : ((Kx B : ℚ) : ℝ) * (p - 4) =
            (1 - t) * (((Kx B : ℚ) : ℝ) * (P0 - 4)) + t * (((Kx B : ℚ) : ℝ) * (Q1 - 4)) := by
          rw [hp]; ring
        have e2 : ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * S =
            (1 - t) * (((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sLo B : ℚ) : ℝ)) +
              t * (((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sHi B : ℚ) : ℝ)) := by
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
      have := assembleW hinc hjW hexc hbeta (by positivity) (le_refl S) hS0 hd2 hfin
      rw [hα]
      linarith only [this]
    · simp only [mean2, Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨_, hr2ok⟩, qm0, qm1⟩ := hm
      have hjl := jLo_le B ha0 hab hb1' hbox hr2ok haHi hb1ok hr1 hr2 hb1 hb2
      set dd : ℝ := ((dLo B : ℚ) : ℝ) * ((dLo B : ℚ) : ℝ) with hdd_def
      have hm0 : ((Dm B : ℚ) : ℝ) * P0 ≤ ((jLo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * dd *
          ((sLo B : ℚ) : ℝ) := by
        rw [hP0, hdd_def]; exact_mod_cast qm0
      have hm1 : ((Dm B : ℚ) : ℝ) * Q1 ≤ ((jLo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * dd *
          ((sHi B : ℚ) : ℝ) := by
        rw [hQ1, hdd_def]; exact_mod_cast qm1
      have hmean : ((Dm B : ℚ) : ℝ) * p ≤ ((jLo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * dd * S := by
        have hm := affine_mix ht0 ht1 hm0 hm1
        have e1 : ((Dm B : ℚ) : ℝ) * p =
            (1 - t) * (((Dm B : ℚ) : ℝ) * P0) + t * (((Dm B : ℚ) : ℝ) * Q1) := by
          rw [hp]; ring
        have e2 : ((jLo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * dd * S =
            (1 - t) * (((jLo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * dd * ((sLo B : ℚ) : ℝ)) +
              t * (((jLo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * dd * ((sHi B : ℚ) : ℝ)) := by
          rw [hSe]; ring
        rw [e1, e2]; exact hm
      have hp0 : (0 : ℝ) ≤ p := by linarith
      have hinc' : P (Δ + S) - P S ≤ Δ * p :=
        hinc.trans (mul_le_mul_of_nonneg_left hpm_le hΔ0)
      have hdd := dLo_sq_le hbox (show ((dLo B : ℚ) : ℝ) ≤ μ.b - μ.a by rw [c_dLo]; exact gdL)
      have hdLo2 : (0 : ℝ) ≤ dd := mul_self_nonneg _
      have := mean_assemble hinc' hjl hΔDm hp0 hbeta (betaLo_nonneg hbox) hdd hdLo2 (le_refl S)
        hS0 hmean
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

end CKLaneE.LS3

#check @CKLaneE.LS3.check_sound
#print axioms CKLaneE.LS3.check_sound

end


