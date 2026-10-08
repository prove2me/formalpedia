-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_EAdapt
-- name    : CK_CKLaneM05_FE8_EAdapt
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:56:19.990827+00:00
-- url     : https://prove2.me/theorems/3850ce1c-c750-47ce-8683-0da8d8e15306
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.EAdapt` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.EAdapt` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.EAdapt` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.EAdapt (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/EAdapt.lean)

import Definitions.Def_CK_CKLaneM05_FE8_Plane
import Definitions.Def_CK_CKLaneE_CertW
import Definitions.Def_CK_CKLaneE_CertEP3
import Definitions.Def_CK_CKLaneE_CertLSK
import Definitions.Def_CK_GeneralCK_LowInformationRegion

-- ===== source module CKLaneM05.FE8.EAdapt =====
section

/-!
# Lane M05 / FE8: reuse of Lane E's same-side kernels through a `Box3` embedding

Lane E's certificates live on boxes `(r, b, E) = (a/b, b, meanEntropy)`
(`CKLaneE.Chart.Box3`). A FE8 box `B` (archive `(a, b, t)` coordinates) is embedded in `X` when
`r1 b1_B ≤ a0`, `a1 ≤ r2 b0_B`, `[b0, b1] ⊆ [X.b1, X.b2]`, `[E_lo, E_up] ⊆ [X.E1, X.E2]`
(`embeds`, all exact ℚ). Then
* `CKLaneE.Chart.GoodW X` (LS/LS2/LS3, weak premises `a < b`, `phi ≤ psi`) gives `LeafOK B`;
* `CKLaneE.Chart.Good X` (EP/EP3, chart premises) gives `LeafOK B`: the only chart premises not
  implied by the row are `1/100 < information` (else `low_information_hybrid_of_active_psi`) and
  `10^-6 < E` (else `PsiGeneralLowEntropy.law_gap_le_cost`);
* `CKLaneE.LSK` (relative floor `t0 C0 ≤ E`) gives `LeafOK B` with `t0 := B.t0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

open GeneralCK CKLaneE.FP

/-- Ratio/`b` part of the embedding (for relative-floor kernels). The upper ratio bound may come
from the box (`a1 ≤ r2 b0`) or from the row premise `b - a ≥ 1/20` (`a/b ≤ 1 - 1/(20 b1) ≤ r2`). -/
def embedsRB (B : CKLaneD.Box) (X : CKLaneE.Chart.Box3) : Bool :=
  boxSane B &&
    decide (0 ≤ X.r1 ∧ X.r1 * B.bhi ≤ B.alo ∧ (B.ahi ≤ X.r2 * B.blo ∨ 20 * B.bhi * (1 - X.r2) ≤ 1) ∧
      X.b1 ≤ B.blo ∧ B.bhi ≤ X.b2)

/-- Embedding of a FE8 box into a Lane E `Box3`. -/
def embeds (B : CKLaneD.Box) (X : CKLaneE.Chart.Box3) : Bool :=
  embedsRB B X && boxPts B && decide (X.E1 ≤ Elo B ∧ Eup B ≤ X.E2)

theorem ratio_mem {B : CKLaneD.Box} {X : CKLaneE.Chart.Box3} (h : embedsRB B X = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : CKLaneD.InBox B μ.a μ.b μ.meanEntropy)
    (hd : 1 / 20 ≤ μ.b - μ.a) :
    (X.r1 : ℝ) ≤ μ.a / μ.b ∧ μ.a / μ.b ≤ (X.r2 : ℝ) ∧ (X.b1 : ℝ) ≤ μ.b ∧ μ.b ≤ (X.b2 : ℝ) := by
  simp only [embedsRB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hr1, hr1b, hr2b, hb1, hb2⟩ := h
  simp only [boxSane, decide_eq_true_eq] at hs
  obtain ⟨sa0, _, _, sb0, _, _, _, _, _⟩ := hs
  obtain ⟨h1, h2, h3, h4, _, _⟩ := hin
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha0 : 0 < μ.a := μ.a_interior.1
  have rr1 : (0 : ℝ) ≤ (X.r1 : ℝ) := by exact_mod_cast hr1
  have rr1b : (X.r1 : ℝ) * (B.bhi : ℝ) ≤ (B.alo : ℝ) := by exact_mod_cast hr1b
  have rb1 : (X.b1 : ℝ) ≤ (B.blo : ℝ) := by exact_mod_cast hb1
  have rb2 : (B.bhi : ℝ) ≤ (X.b2 : ℝ) := by exact_mod_cast hb2
  have rB0 : (0 : ℝ) < (B.blo : ℝ) := by exact_mod_cast sb0
  refine ⟨?_, ?_, rb1.trans h3, h4.trans rb2⟩
  · rw [le_div_iff₀ hb0]
    have := mul_le_mul_of_nonneg_left h4 rr1
    linarith
  · rw [div_le_iff₀ hb0]
    rcases hr2b with hr2b | hr2b
    · have rr2b : (B.ahi : ℝ) ≤ (X.r2 : ℝ) * (B.blo : ℝ) := by exact_mod_cast hr2b
      have hr2 : (0 : ℝ) ≤ (X.r2 : ℝ) := by
        by_contra hn
        have : (X.r2 : ℝ) * (B.blo : ℝ) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hn) rB0
        linarith
      have := mul_le_mul_of_nonneg_left h3 hr2
      linarith
    · have rr2b : 20 * (B.bhi : ℝ) * (1 - (X.r2 : ℝ)) ≤ 1 := by
        have h := (Rat.cast_le (K := ℝ)).mpr hr2b; push_cast at h; exact h
      rcases le_total (X.r2 : ℝ) 1 with hr | hr
      · -- (1 - r2) b ≤ (1 - r2) b1 ≤ 1/20 ≤ b - a
        have h1r : (0 : ℝ) ≤ 1 - (X.r2 : ℝ) := by linarith
        have hbb : (1 - (X.r2 : ℝ)) * μ.b ≤ (1 - (X.r2 : ℝ)) * (B.bhi : ℝ) :=
          mul_le_mul_of_nonneg_left h4 h1r
        nlinarith
      · nlinarith

theorem embeds_mem {B : CKLaneD.Box} {X : CKLaneE.Chart.Box3} (h : embeds B X = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hin : CKLaneD.InBox B μ.a μ.b μ.meanEntropy)
    (hd : 1 / 20 ≤ μ.b - μ.a) :
    CKLaneE.Chart.InBox X μ := by
  have h' := h
  simp only [embeds, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨hrb, hp⟩, hE1, hE2⟩ := h'
  have hs : boxSane B = true := by
    simp only [embedsRB, Bool.and_eq_true] at hrb; exact hrb.1
  obtain ⟨q1, q2, q3, q4⟩ := ratio_mem hrb μ hin hd
  obtain ⟨_, _, _, _, _, _, hElo, hEup, _, _, _⟩ := box_facts hs hp μ hin
  have rE1 : (X.E1 : ℝ) ≤ ((Elo B : ℚ) : ℝ) := by exact_mod_cast hE1
  have rE2 : ((Eup B : ℚ) : ℝ) ≤ (X.E2 : ℝ) := by exact_mod_cast hE2
  exact ⟨q1, q2, q3, q4, rE1.trans hElo, hEup.trans rE2⟩

theorem leafOK_of_goodW {B : CKLaneD.Box} {X : CKLaneE.Chart.Box3} (he : embeds B X = true)
    (h : CKLaneE.Chart.GoodW X) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact h k μ (by linarith) (embeds_mem he μ hin hd) hact'.le

theorem leafOK_of_good {B : CKLaneD.Box} {X : CKLaneE.Chart.Box3} (he : embeds B X = true)
    (h : CKLaneE.Chart.Good X) : LeafOK B := by
  intro k μ hab hsum ha hb hd hE hs hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  have hlt : μ.a < μ.b := by linarith
  by_cases hI : μ.information ≤ 1 / 100
  · exact low_information_hybrid_of_active_psi μ hI hact'.le
  by_cases hEs : μ.meanEntropy ≤ 1 / 1000000
  · exact PsiGeneralLowEntropy.law_gap_le_cost μ hlt hsum (by linarith) hEs hact'.le
  have hb0 : 0 < μ.b := μ.b_interior.1
  have hratio : (1 : ℝ) / 5 ≤ μ.a / μ.b := by
    rw [le_div_iff₀ hb0]; linarith
  refine h k μ ⟨hlt, by linarith, by linarith, lt_of_not_ge hI, lt_of_not_ge hEs, hb, by linarith,
    fun _ => by linarith, fun _ => by linarith, hact'⟩ (embeds_mem he μ hin hd)

theorem leafOK_of_lsk {B : CKLaneD.Box} {X : CKLaneE.Chart.Box3} (he : embedsRB B X = true)
    {v0S v0I v1S v1I : ℚ} (h : CKLaneE.LSK.check X B.t0 v0S v0I v1S v1I = true) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  obtain ⟨q1, q2, q3, q4⟩ := ratio_mem he μ hin hd
  have he' := he
  simp only [embedsRB, Bool.and_eq_true, decide_eq_true_eq] at he'
  obtain ⟨hs, _⟩ := he'
  simp only [boxSane, decide_eq_true_eq] at hs
  obtain ⟨_, _, _, _, _, _, st0, st1, st2⟩ := hs
  obtain ⟨_, _, _, _, hE0, _⟩ := hin
  have rt0 : (0 : ℝ) ≤ (B.t0 : ℝ) := by exact_mod_cast st0
  have rt1 : (B.t0 : ℝ) ≤ 1 := by exact_mod_cast st1.trans st2
  have hEM : (0 : ℝ) ≤ ((CKLaneD.EMIN : ℚ) : ℝ) := by simp only [CKLaneD.EMIN]; norm_num
  have hfloor : (B.t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ μ.meanEntropy := by
    have : (B.t0 : ℝ) * ((H μ.a + H μ.b) / 2) ≤ (CKLaneD.EMIN : ℝ) +
        (B.t0 : ℝ) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) := by nlinarith
    linarith
  exact CKLaneE.LSK.check_sound X B.t0 v0S v0I v1S v1I h k μ (by linarith) q1 q2 q3 q4 hfloor hact'.le

/-! ## Certificate type v2 -/

/-- FE8 certificate, version 2: v1 plus Lane E kernels on an embedding box. -/
inductive W2 where
  | outside
  | cap
  | parent (w : PW)
  | plane (c : PC)
  | ls (X : CKLaneE.Chart.Box3) (vS vI : ℚ)
  | ls2 (X : CKLaneE.Chart.Box3) (v0S v0I v1S v1I : ℚ)
  | ls3 (X : CKLaneE.Chart.Box3) (v0S v0I v1S v1I : ℚ)
  | ep (X : CKLaneE.Chart.Box3) (vS vI vc : ℚ) (mode : ℕ)
  | ep3 (X : CKLaneE.Chart.Box3) (vS vI vc : ℚ) (mode : ℕ)
  | lsk (X : CKLaneE.Chart.Box3) (v0S v0I v1S v1I : ℚ)
  deriving Repr

def W2.check (B : CKLaneD.Box) : W2 → Bool
  | .outside => decide (B.bhi - B.alo < 1 / 20)
  | .cap => capCheck B
  | .parent w => parentCheck B w
  | .plane c => planeCheck B c
  | .ls X vS vI => embeds B X && CKLaneE.LS.check X vS vI
  | .ls2 X a b c d => embeds B X && CKLaneE.LS2.check X a b c d
  | .ls3 X a b c d => embeds B X && CKLaneE.LS3.check X a b c d
  | .ep X vS vI vc m => embeds B X && CKLaneE.EP.check X vS vI vc m
  | .ep3 X vS vI vc m => embeds B X && CKLaneE.EP3.check X vS vI vc m
  | .lsk X a b c d => embedsRB B X && CKLaneE.LSK.check X B.t0 a b c d

theorem W2.check_sound : ∀ (B : CKLaneD.Box) (w : W2), W2.check B w = true → LeafOK B
  | _, .outside, h => leafOK_of_outside (by simpa [W2.check] using h)
  | _, .cap, h => leafOK_of_cap h
  | _, .parent _, h => leafOK_of_parentCheck h
  | _, .plane _, h => leafOK_of_planeCheck h
  | _, .ls X vS vI, h => by
      simp only [W2.check, Bool.and_eq_true] at h
      exact leafOK_of_goodW h.1 (CKLaneE.LS.check_soundW X vS vI h.2)
  | _, .ls2 X a b c d, h => by
      simp only [W2.check, Bool.and_eq_true] at h
      exact leafOK_of_goodW h.1 (CKLaneE.LS2.check_soundW X a b c d h.2)
  | _, .ls3 X a b c d, h => by
      simp only [W2.check, Bool.and_eq_true] at h
      exact leafOK_of_goodW h.1 (CKLaneE.LS3.check_soundW X a b c d h.2)
  | _, .ep X vS vI vc m, h => by
      simp only [W2.check, Bool.and_eq_true] at h
      exact leafOK_of_good h.1 (CKLaneE.EP.check_sound X vS vI vc m h.2)
  | _, .ep3 X vS vI vc m, h => by
      simp only [W2.check, Bool.and_eq_true] at h
      exact leafOK_of_good h.1 (CKLaneE.EP3.check_sound X vS vI vc m h.2)
  | _, .lsk X a b c d, h => by
      simp only [W2.check, Bool.and_eq_true] at h
      exact leafOK_of_lsk h.1 h.2

end CKLaneM05.FE8

#check @CKLaneM05.FE8.W2.check_sound
#print axioms CKLaneM05.FE8.W2.check_sound
#print axioms CKLaneM05.FE8.leafOK_of_good
#print axioms CKLaneM05.FE8.leafOK_of_goodW
#print axioms CKLaneM05.FE8.leafOK_of_lsk

end


