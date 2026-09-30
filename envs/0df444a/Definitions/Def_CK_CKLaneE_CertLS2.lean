-- Prove2me | Definitions.Def_CK_CKLaneE_CertLS2
-- name    : CK_CKLaneE_CertLS2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:44:23.948008+00:00
-- url     : https://prove2.me/theorems/d15369cd-95c2-41d5-a154-f61a52cc9fa5
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertLS2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertLS2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertLS2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertLS2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertLS2.lean)

import Definitions.Def_CK_CKLaneE_CertLS

-- ===== source module CKLaneE.CertLS2 =====
section

/-!
# Lane E: concave-endpoint log-sum certificate (`ls2`)

Same inequality as `CKLaneE.LS` (log-sum floor, normalized or mean form), but the law's maximal deficit
`S = (H a + H b)/2 - E1 ∈ [sLo, sHi]` is handled exactly instead of pairing `β·sLo` with slope anchors
at `sHi`: by convexity of `P1` (corpus `P1_convexOn`) the slope average
`(P1 S + P1 (Δ + S))/2` is at most the convex combination of its values at the two endpoints
`σ₀ = sLo`, `σ₁ = sHi` (with `Δ ≤ Dm = min(K dHi², DHi)`), and the target inequality is affine in `S`.
So it suffices to check the inequality at both endpoints, with four slope anchors:
`P1(sLo)`, `P1(min(IHi, sLo + Dm))`, `P1(sHi)`, `P1(sHi + Dm)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.LS2

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS
open CKLaneE.NLS (box_geometry)

section defs
variable (B : Box3)

def Dm : ℚ := if K B * (dHi B * dHi B) ≤ DHi B then K B * (dHi B * dHi B) else DHi B
def tI0 : ℚ := if IHi B ≤ sLo B + Dm B then IHi B else sLo B + Dm B
def tI1 : ℚ := sHi B + Dm B

def norm2 (v0S v0I v1S v1I : ℚ) : Bool :=
  decide (K B * (pbar v0S v0I - 4) ≤ Wlo B + betaLo B * sLo B ∧
    K B * (pbar v1S v1I - 4) ≤ Wlo B + betaLo B * sHi B)

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

/-- Convex interpolation of the slope average between the two deficit endpoints. -/
theorem P1_mix {s0 s1 S Δ A0 B0 A1 B1 : ℝ} (h0 : 0 ≤ s0) (hS0 : s0 ≤ S) (hS1 : S ≤ s1)
    (hΔ : 0 ≤ Δ) (h1 : s1 + Δ < 1)
    (hA0 : P1 s0 ≤ A0) (hB0 : P1 (s0 + Δ) ≤ B0) (hA1 : P1 s1 ≤ A1) (hB1 : P1 (s1 + Δ) ≤ B1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ S = (1 - t) * s0 + t * s1 ∧
      P1 S + P1 (Δ + S) ≤ (1 - t) * (A0 + B0) + t * (A1 + B1) := by
  rcases eq_or_lt_of_le (hS0.trans hS1) with heq | hlt
  · have hS : S = s0 := le_antisymm (heq ▸ hS1) hS0
    refine ⟨0, le_refl _, zero_le_one, ?_, ?_⟩
    · rw [hS]; ring
    · rw [hS, add_comm Δ s0]
      have e : (1 - (0 : ℝ)) * (A0 + B0) + 0 * (A1 + B1) = A0 + B0 := by ring
      rw [e]
      linarith
  · have hpos : 0 < s1 - s0 := sub_pos.mpr hlt
    set t := (S - s0) / (s1 - s0) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
    have hSe : S = (1 - t) * s0 + t * s1 := by
      rw [ht]; field_simp; ring
    refine ⟨t, ht0, ht1, hSe, ?_⟩
    have hx : s0 ∈ Set.Ico (0 : ℝ) 1 := ⟨h0, by linarith⟩
    have hy : s1 ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hx' : s0 + Δ ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hy' : s1 + Δ ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, h1⟩
    have c1 := P1_convexOn.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
    have c2 := P1_convexOn.2 hx' hy' (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul] at c1 c2
    have e1 : (1 - t) * s0 + t * s1 = S := hSe.symm
    have e2 : (1 - t) * (s0 + Δ) + t * (s1 + Δ) = Δ + S := by rw [hSe]; ring
    rw [e1] at c1
    rw [e2] at c2
    have m1 : (1 - t) * P1 s0 ≤ (1 - t) * A0 := mul_le_mul_of_nonneg_left hA0 (by linarith)
    have m2 : t * P1 s1 ≤ t * A1 := mul_le_mul_of_nonneg_left hA1 ht0
    have m3 : (1 - t) * P1 (s0 + Δ) ≤ (1 - t) * B0 := mul_le_mul_of_nonneg_left hB0 (by linarith)
    have m4 : t * P1 (s1 + Δ) ≤ t * B1 := mul_le_mul_of_nonneg_left hB1 ht0
    have e3 : (1 - t) * (A0 + B0) + t * (A1 + B1) = (1 - t) * A0 + (1 - t) * B0 + t * A1 + t * B1 := by
      ring
    rw [e3]
    linarith

/-- An affine inequality checked at both endpoints holds at every convex combination. -/
theorem affine_mix {t x0 x1 y0 y1 : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h0 : x0 ≤ y0) (h1 : x1 ≤ y1) :
    (1 - t) * x0 + t * x1 ≤ (1 - t) * y0 + t * y1 := by
  have a := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ 1 - t)
  have b := mul_le_mul_of_nonneg_left h1 ht0
  linarith

theorem Dm_bound (B : Box3) {Δ d : ℝ} (hK0 : (0 : ℝ) ≤ ((K B : ℚ) : ℝ)) (hd0 : 0 ≤ d)
    (hd : d ≤ ((dHi B : ℚ) : ℝ)) (hΔK : Δ ≤ ((K B : ℚ) : ℝ) * d ^ 2)
    (hΔD : Δ ≤ ((DHi B : ℚ) : ℝ)) : Δ ≤ ((Dm B : ℚ) : ℝ) := by
  simp only [Dm]
  split_ifs
  · push_cast
    have h1 : d ^ 2 ≤ ((dHi B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ) := by
      rw [sq]; exact mul_le_mul hd hd hd0 (hd0.trans hd)
    exact hΔK.trans (mul_le_mul_of_nonneg_left h1 hK0)
  · exact hΔD

set_option maxHeartbeats 1000000 in
/-- Soundness of a concave-endpoint log-sum leaf. -/
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
  have hKb := K_bound B ha0 hab hb1' hbox qK hr1 hr2 hb1 hb2 hHaL hHbL hHmH
  rw [← hΔdef] at hKb
  have hΔD : Δ ≤ ((DHi B : ℚ) : ℝ) := by rw [c_DHi, c_CLo, hΔdef]; linarith
  have hd0 : (0 : ℝ) ≤ μ.b - μ.a := by linarith
  have hΔDm : Δ ≤ ((Dm B : ℚ) : ℝ) :=
    Dm_bound B hK0 hd0 (by rw [c_dHi]; exact gdH) hKb hΔD
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
      have hfin0 : ((K B : ℚ) : ℝ) * (P0 - 4) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sLo B : ℚ) : ℝ) := by
        rw [hP0]; exact_mod_cast qfin0
      have hfin1 : ((K B : ℚ) : ℝ) * (Q1 - 4) ≤
          ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sHi B : ℚ) : ℝ) := by
        rw [hQ1]; exact_mod_cast qfin1
      have hfin : ((K B : ℚ) : ℝ) * (p - 4) ≤ ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * S := by
        have hm := affine_mix ht0 ht1 hfin0 hfin1
        have e1 : ((K B : ℚ) : ℝ) * (p - 4) =
            (1 - t) * (((K B : ℚ) : ℝ) * (P0 - 4)) + t * (((K B : ℚ) : ℝ) * (Q1 - 4)) := by
          rw [hp]; ring
        have e2 : ((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * S =
            (1 - t) * (((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sLo B : ℚ) : ℝ)) +
              t * (((Wlo B : ℚ) : ℝ) + ((betaLo B : ℚ) : ℝ) * ((sHi B : ℚ) : ℝ)) := by
          rw [hSe]; ring
        rw [e1, e2]; exact hm
      have hd2 : (0 : ℝ) ≤ (μ.b - μ.a) ^ 2 := sq_nonneg _
      have hKd2 : (0 : ℝ) ≤ ((K B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 := mul_nonneg hK0 hd2
      have hexc : Δ * (pm - 4) ≤ ((K B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (p - 4) := by
        have a1 : Δ * (pm - 4) ≤ ((K B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (pm - 4) :=
          mul_le_mul_of_nonneg_right hKb (by linarith)
        have a2 : ((K B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (pm - 4) ≤
            ((K B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * (p - 4) :=
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

end CKLaneE.LS2

#check @CKLaneE.LS2.check_sound
#print axioms CKLaneE.LS2.check_sound

end


