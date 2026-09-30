-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_Base
-- name    : CK_CKLaneM05_FE8_Base
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:48:21.131669+00:00
-- url     : https://prove2.me/theorems/62c6cf26-f31e-48e5-94cc-23604c448d17
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.Base` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.Base` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.Base` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.Base (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/Base.lean)

import Definitions.Def_CK_CKLaneM05_Checker
import Definitions.Def_CK_CKLaneN23_SameSideHalf

-- ===== source module CKLaneM05.FE8.Base =====
section

/-!
# Lane M05 / FE8: FULL_ENTROPY Theorem (8) — boxes, per-leaf obligation, tree soundness

Archive `CK_FULL_ENTROPY_CONTINUATION/FULL_ENTROPY_COVER.py` (sha256 e7f10ae4…82e8), result
`FULL_ENTROPY_RESULT.json` (sha256 1dbc7c5b…ba7c, 33,572 leaves): root
`(a, b, t) ∈ [1/10,1/2]² × [0,1]`, `E = 10^-6 + t (C0 - 10^-6)`, `C0 = (H a + H b)/2`; exact
midpoint halving, path digit `d`: axis `d / 2` (`0 = a`, `1 = b`, `2 = t`), side `d % 2`.

* Box semantics: `CKLaneD.Box` / `CKLaneD.InBox` (Lane D's `(a, b)` box with entropy fraction over
  `CKLaneD.EMIN = 10^-6`), i.e. exactly the archive coordinate map; the entropy split is arbitrary.
* `LeafOK B` : the route row `CKLaneN23.FullEntropySSCoverRest` restricted to the image of `B`.
* `leafOK_step` : exact halving (no side conditions); `CT` : certificate trees with generic
  soundness `CT.sound`; `row_of_root : LeafOK feRoot → CKLaneN23.FullEntropySSCoverRest`.
* Leaf adapters: `outside` (`b1 - a0 < 1/20`), `cap` (`s ≤ 3/40` on the box, contradicting the row's
  `3/40 < s`), psi-candidate statements (`CKLaneD.Sem`), parent dominance (`ParentBox`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

open GeneralCK CKLaneE.FP

/-! ## Archived boxes -/

/-- Root of the archived FULL_ENTROPY (8) cover. -/
def feRoot : CKLaneD.Box := ⟨1 / 10, 1 / 2, 1 / 10, 1 / 2, 0, 1⟩

/-- One exact halving step (`reconstruct`: `axis, side = divmod(d, 2)`). -/
def feStep (B : CKLaneD.Box) (d : ℕ) : CKLaneD.Box :=
  match d with
  | 0 => { B with ahi := (B.alo + B.ahi) / 2 }
  | 1 => { B with alo := (B.alo + B.ahi) / 2 }
  | 2 => { B with bhi := (B.blo + B.bhi) / 2 }
  | 3 => { B with blo := (B.blo + B.bhi) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- The exact box of an archived path. -/
def feBox (p : List ℕ) : CKLaneD.Box := p.foldl feStep feRoot

theorem feBox_append (p : List ℕ) (d : ℕ) : feBox (p ++ [d]) = feStep (feBox p) d := by
  unfold feBox
  rw [List.foldl_append]
  rfl

/-! ## The per-leaf obligation of the route row -/

/-- `CKLaneN23.FullEntropySSCoverRest` restricted to the image of the box `B`. -/
def LeafOK (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 20 ≤ μ.b - μ.a →
    1 / 1000000 ≤ μ.meanEntropy → 3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy →
    CKLaneD.InBox B μ.a μ.b μ.meanEntropy → CKLaneN23.PsiActive μ → μ.gap ≤ μ.cost

theorem inBox_step (B : CKLaneD.Box) (ax : ℕ) (hax : ax < 3) {a b E : ℝ}
    (h : CKLaneD.InBox B a b E) :
    CKLaneD.InBox (feStep B (2 * ax)) a b E ∨ CKLaneD.InBox (feStep B (2 * ax + 1)) a b E := by
  unfold CKLaneD.InBox at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases (by omega : ax = 0 ∨ ax = 1 ∨ ax = 2) with rfl | rfl | rfl
  · rcases le_total a ((((B.alo + B.ahi) / 2 : ℚ)) : ℝ) with hc | hc
    · left; exact ⟨h1, hc, h3, h4, h5, h6⟩
    · right; exact ⟨hc, h2, h3, h4, h5, h6⟩
  · rcases le_total b ((((B.blo + B.bhi) / 2 : ℚ)) : ℝ) with hc | hc
    · left; exact ⟨h1, h2, h3, hc, h5, h6⟩
    · right; exact ⟨h1, h2, hc, h4, h5, h6⟩
  · rcases le_total E ((CKLaneD.EMIN : ℝ) +
        ((((B.t0 + B.t1) / 2 : ℚ)) : ℝ) * ((H a + H b) / 2 - (CKLaneD.EMIN : ℝ))) with hc | hc
    · left; exact ⟨h1, h2, h3, h4, h5, hc⟩
    · right; exact ⟨h1, h2, h3, h4, hc, h6⟩

/-- Exact halving: the obligation on both halves gives it on the box. -/
theorem leafOK_step (B : CKLaneD.Box) (ax : ℕ) (hax : ax < 3)
    (h0 : LeafOK (feStep B (2 * ax))) (h1 : LeafOK (feStep B (2 * ax + 1))) : LeafOK B := by
  intro k μ hab hsum ha hb hd hE hs hin hact
  rcases inBox_step B ax hax hin with h | h
  · exact h0 k μ hab hsum ha hb hd hE hs h hact
  · exact h1 k μ hab hsum ha hb hd hE hs h hact

/-- Path form of `leafOK_step`. -/
theorem leafOK_split (p p0 p1 : List ℕ) (ax : ℕ) (hax : ax < 3)
    (e0 : p0 = p ++ [2 * ax]) (e1 : p1 = p ++ [2 * ax + 1])
    (h0 : LeafOK (feBox p0)) (h1 : LeafOK (feBox p1)) : LeafOK (feBox p) := by
  subst e0 e1
  rw [feBox_append] at h0 h1
  exact leafOK_step (feBox p) ax hax h0 h1

/-! ## Certificate trees -/

/-- A certificate tree: exact halving nodes and per-leaf certificates of type `α`. -/
inductive CT (α : Type) where
  | leaf (w : α)
  | node (ax : ℕ) (l r : CT α)
  deriving Repr

/-- Boolean check of a certificate tree below the box `B`, with a per-leaf checker `chk`. -/
def CT.check {α : Type} (chk : CKLaneD.Box → α → Bool) : CT α → CKLaneD.Box → Bool
  | CT.leaf w, B => chk B w
  | CT.node ax l r, B => decide (ax < 3) && l.check chk (feStep B (2 * ax)) &&
      r.check chk (feStep B (2 * ax + 1))

theorem CT.sound {α : Type} (chk : CKLaneD.Box → α → Bool)
    (hchk : ∀ B w, chk B w = true → LeafOK B) :
    ∀ (T : CT α) (B : CKLaneD.Box), T.check chk B = true → LeafOK B
  | CT.leaf w, B, h => hchk B w h
  | CT.node ax l r, B, h => by
      simp only [CT.check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hax, hl⟩, hr⟩ := h
      exact leafOK_step B ax hax (CT.sound chk hchk l _ hl) (CT.sound chk hchk r _ hr)

/-! ## Root containment and the route row -/

theorem inBox_feRoot {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (ha : 1 / 10 ≤ μ.a)
    (hb : μ.b ≤ 1 / 2) (hE : 1 / 1000000 ≤ μ.meanEntropy) :
    CKLaneD.InBox feRoot μ.a μ.b μ.meanEntropy := by
  have hEle : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
  have hEM : ((CKLaneD.EMIN : ℚ) : ℝ) = 1 / 1000000 := by
    simp only [CKLaneD.EMIN]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [feRoot] <;> push_cast
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [hEM]; linarith
  · rw [hEM]; linarith

/-- The route row from the obligation on the root box. -/
theorem row_of_root (h : LeafOK feRoot) : CKLaneN23.FullEntropySSCoverRest := by
  intro k μ hab hsum ha hb hd hE hs hact
  exact h k μ hab hsum ha hb hd hE hs (inBox_feRoot μ hab ha hb hE) hact

/-! ## Leaf adapters -/

/-- Boxes with `b1 - a0 < 1/20` carry no law of the row. -/
theorem leafOK_of_outside {B : CKLaneD.Box} (h : B.bhi - B.alo < 1 / 20) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ hin _
  obtain ⟨h1, _, _, h4, _, _⟩ := hin
  have h' : ((B.bhi - B.alo : ℚ) : ℝ) < ((1 / 20 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exfalso
  linarith

/-- Cap boxes: `s ≤ (1 - t0)(C0hi - EMIN) ≤ 3/40` on the box, contradicting the row's `3/40 < s`. -/
def capCheck (B : CKLaneD.Box) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ B.ahi ≤ 1 / 2 ∧ 0 < B.blo ∧ B.blo ≤ B.bhi ∧ B.bhi ≤ 1 / 2 ∧
      0 ≤ B.t0 ∧ B.t0 ≤ 1) &&
    ptOk B.ahi && ptOk B.bhi &&
    decide ((1 - B.t0) * ((Hhi B.ahi + Hhi B.bhi) / 2 - CKLaneD.EMIN) ≤ 3 / 40)

theorem leafOK_of_cap {B : CKLaneD.Box} (h : capCheck B = true) : LeafOK B := by
  intro k μ _ _ _ _ _ _ hs hin _
  simp only [capCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hb0, hb1, hb2, hb3, hb4, hb5, ht0, ht1⟩, pa⟩, pb⟩, hcap⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hin
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0' : 0 < μ.b := μ.b_interior.1
  have rA : ((B.ahi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hb2; push_cast at h; exact h
  have rB : ((B.bhi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hb5; push_cast at h; exact h
  obtain ⟨_, HA⟩ := H_bounds pa
  obtain ⟨_, HB⟩ := H_bounds pb
  have hHa : H μ.a ≤ ((Hhi B.ahi : ℚ) : ℝ) := (H_le_H ha0.le h2 rA).trans HA
  have hHb : H μ.b ≤ ((Hhi B.bhi : ℚ) : ℝ) := (H_le_H hb0'.le h4 rB).trans HB
  have ht0R : (0 : ℝ) ≤ (B.t0 : ℝ) := by exact_mod_cast ht0
  have ht1R : (B.t0 : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hcapR : (1 - (B.t0 : ℝ)) * ((((Hhi B.ahi : ℚ) : ℝ) + ((Hhi B.bhi : ℚ) : ℝ)) / 2 -
      (CKLaneD.EMIN : ℝ)) ≤ 3 / 40 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcap; push_cast at h; exact h
  -- s = C0 - E ≤ (1 - t0)(C0 - EMIN) ≤ (1 - t0)(C0hi - EMIN)
  have hmono : (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) ≤
      (1 - (B.t0 : ℝ)) * ((((Hhi B.ahi : ℚ) : ℝ) + ((Hhi B.bhi : ℚ) : ℝ)) / 2 -
        (CKLaneD.EMIN : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hs' : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤
      (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) := by nlinarith
  exfalso
  linarith

/-- psi-candidate statement on the box (Lane D form) gives the row obligation. -/
theorem leafOK_of_sem {B : CKLaneD.Box} (h : CKLaneD.Sem B) : LeafOK B := by
  intro k μ _ _ _ _ _ _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact (hybrid_gap_le_psi hact'.le).trans (h k μ hin)

/-- Parent dominance on the image of a box. -/
def ParentBox (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), CKLaneD.InBox B μ.a μ.b μ.meanEntropy →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

theorem leafOK_of_parentBox {B : CKLaneD.Box} (h : ParentBox B) : LeafOK B := by
  intro k μ _ _ _ _ _ _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact absurd (h k μ hin) (not_le.mpr hact')

end CKLaneM05.FE8

#check @CKLaneM05.FE8.row_of_root
#check @CKLaneM05.FE8.CT.sound
#check @CKLaneM05.FE8.leafOK_of_cap
#print axioms CKLaneM05.FE8.row_of_root
#print axioms CKLaneM05.FE8.CT.sound
#print axioms CKLaneM05.FE8.leafOK_of_cap
#print axioms CKLaneM05.FE8.leafOK_of_outside
#print axioms CKLaneM05.FE8.leafOK_of_sem
#print axioms CKLaneM05.FE8.leafOK_of_parentBox

end


