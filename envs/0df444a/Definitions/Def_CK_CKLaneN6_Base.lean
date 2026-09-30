-- Prove2me | Definitions.Def_CK_CKLaneN6_Base
-- name    : CK_CKLaneN6_Base
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:55:54.990334+00:00
-- url     : https://prove2.me/theorems/d850a489-8e9a-4415-becb-b4bdfe23cc3f
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Base` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Base` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Base` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Base (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Base.lean)

import Definitions.Def_CK_CKLaneM05_FE8_Parent

-- ===== source module CKLaneN6.Base =====
section

/-!
# Lane N6: SMALL_RATIO Theorem 3 — per-leaf obligation, certificate trees, structural leaves

Archive `CK_SMALL_RATIO_EXTENSION/SMALL_DIFFERENCE_COVER.py` (sha256 39d33cde…7c4e) with the core
`FULL_ENTROPY_COVER.py` (sha256 e7f10ae4…82e8) run at `DMIN = 1/100`; result
`SMALL_DIFFERENCE_RESULT.json` (sha256 b7d88a13…14a2, 76,547 leaves): root
`(a, b, t) ∈ [1/10,1/2]² × [0,1]`, `E = 10^-6 + t (C0 - 10^-6)`, `C0 = (H a + H b)/2`; exact midpoint
halving, digit `d`: axis `d / 2` (`0 = a`, `1 = b`, `2 = t`), side `d % 2`.

* Box semantics: `CKLaneD.Box` / `CKLaneD.InBox`, root and path map `CKLaneM05.FE8.feRoot` /
  `CKLaneM05.FE8.feBox` (the FULL_ENTROPY (8) root is the same box).  The entropy split is arbitrary.
* `LeafOK B` : the route row `CKLaneN23.SmallRatioT3NearRest` (verbatim hypotheses) restricted to
  the image of `B`.
* `leafOK_step` : exact halving; `CT.soundN6` : certificate trees (refinement inside a leaf);
  `row_of_root : LeafOK feRoot → CKLaneN23.SmallRatioT3NearRest`.
* Structural leaves: `irr` (`b1 - a0 < 1/100`: archive `outside`), `prior` (`1/20 ≤ b0 - a1`: archive
  `prior_same_side`), `csr` (`E ≤ 11/200` and `d ≤ 4E` on the box: archive `central_small_ratio`),
  `cap` (`s ≤ 3/40` on the box: archive `cap`) — each contradicts a hypothesis of the row.
* Row-independent box statements consumed by the method kernels: `ParentBox` (Lane M05),
  `ParentBoxD` (parent dominance using `1/100 ≤ b - a`), `RadSem` (psi candidate, `a < b`),
  `GapBox` (hybrid gap under `a < b`, `phi ≤ psi`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6

open GeneralCK CKLaneE.FP
open CKLaneM05.FE8 (feRoot feStep feBox feBox_append CT ParentBox capCheck mLo mHi C0lo C0hi Eup Elo
  qHi boxSane boxPts box_facts inBox_step)
open CKLaneM05 (H_le_H)

/-! ## The per-leaf obligation of the route row -/

/-- `CKLaneN23.SmallRatioT3NearRest` restricted to the image of the box `B`. -/
def LeafOK (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → 1 / 100 ≤ μ.b - μ.a → μ.b - μ.a < 1 / 20 →
    1 / 1000000 ≤ μ.meanEntropy →
    (11 / 200 < μ.meanEntropy ∨ 4 * μ.meanEntropy < μ.b - μ.a) →
    3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy →
    CKLaneD.InBox B μ.a μ.b μ.meanEntropy → CKLaneN23.PsiActive μ → μ.gap ≤ μ.cost

/-- Exact halving: the obligation on both halves gives it on the box. -/
theorem leafOK_step (B : CKLaneD.Box) (ax : ℕ) (hax : ax < 3)
    (h0 : LeafOK (feStep B (2 * ax))) (h1 : LeafOK (feStep B (2 * ax + 1))) : LeafOK B := by
  intro k μ hab hsum ha hb hd hd20 hE hor hs hin hact
  rcases inBox_step B ax hax hin with h | h
  · exact h0 k μ hab hsum ha hb hd hd20 hE hor hs h hact
  · exact h1 k μ hab hsum ha hb hd hd20 hE hor hs h hact

/-- Certificate trees (`CKLaneM05.FE8.CT`) are sound for the Thm 3 obligation. -/
theorem CT.soundN6 {α : Type} (chk : CKLaneD.Box → α → Bool)
    (hchk : ∀ B w, chk B w = true → LeafOK B) :
    ∀ (T : CT α) (B : CKLaneD.Box), T.check chk B = true → LeafOK B
  | CT.leaf w, B, h => hchk B w h
  | CT.node ax l r, B, h => by
      simp only [CT.check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hax, hl⟩, hr⟩ := h
      exact leafOK_step B ax hax (CT.soundN6 chk hchk l _ hl) (CT.soundN6 chk hchk r _ hr)

/-- A shard: archived paths with certificate trees; one Boolean check for all of them. -/
theorem entries_sound {α : Type} (chk : CKLaneD.Box → α → Bool)
    (hchk : ∀ B w, chk B w = true → LeafOK B) (L : List (List ℕ × CT α))
    (h : L.all (fun x => x.2.check chk (feBox x.1)) = true) :
    ∀ q ∈ L.map Prod.fst, LeafOK (feBox q) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  rw [List.all_eq_true] at h
  exact CT.soundN6 chk hchk x.2 _ (h x hx)

/-- The route row from the obligation on the root box. -/
theorem row_of_root (h : LeafOK feRoot) : CKLaneN23.SmallRatioT3NearRest := by
  intro k μ hab hsum ha hb hd hd20 hE hor hs hact
  exact h k μ hab hsum ha hb hd hd20 hE hor hs
    (CKLaneM05.FE8.inBox_feRoot μ hab ha hb hE) hact

/-! ## Structural leaves -/

/-- Archive `outside`: `b1 - a0 < 1/100`, no law of the row. -/
theorem leafOK_of_irr {B : CKLaneD.Box} (h : B.bhi - B.alo < 1 / 100) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ _ _ hin _
  obtain ⟨h1, _, _, h4, _, _⟩ := hin
  have h' : ((B.bhi - B.alo : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exfalso
  linarith

/-- Archive `prior_same_side`: `1/20 ≤ b0 - a1`, no law of the row (`b - a < 1/20`). -/
theorem leafOK_of_prior {B : CKLaneD.Box} (h : 1 / 20 ≤ B.blo - B.ahi) : LeafOK B := by
  intro k μ _ _ _ _ _ hd20 _ _ _ hin _
  obtain ⟨_, h2, h3, _, _, _⟩ := hin
  have h' : ((1 / 20 : ℚ) : ℝ) ≤ ((B.blo - B.ahi : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exfalso
  linarith

/-- Archive `central_small_ratio`: `E ≤ 11/200` and `b - a ≤ 4E` on the whole box. -/
def csrCheck (B : CKLaneD.Box) : Bool :=
  boxSane B && boxPts B && decide (Eup B ≤ 11 / 200 ∧ B.bhi - B.alo ≤ 4 * Elo B)

theorem leafOK_of_csr {B : CKLaneD.Box} (h : csrCheck B = true) : LeafOK B := by
  intro k μ _ _ _ _ _ _ _ hor _ hin _
  simp only [csrCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, hp⟩, hE, hD⟩ := h
  obtain ⟨_, _, _, _, _, _, hElo, hEup, _, _, _⟩ := box_facts hs hp μ hin
  obtain ⟨h1, _, _, h4, _, _⟩ := hin
  have hE' : ((Eup B : ℚ) : ℝ) ≤ ((11 / 200 : ℚ) : ℝ) := by exact_mod_cast hE
  have hD' : ((B.bhi - B.alo : ℚ) : ℝ) ≤ ((4 * Elo B : ℚ) : ℝ) := by exact_mod_cast hD
  push_cast at hE' hD'
  exfalso
  rcases hor with h | h <;> linarith

/-- Archive `cap`: `s ≤ (1 - t0)(C0hi - EMIN) ≤ 3/40` on the box, contradicting `3/40 < s`. -/
theorem leafOK_of_cap {B : CKLaneD.Box} (h : capCheck B = true) : LeafOK B := by
  intro k μ _ _ _ _ _ _ _ _ hs hin _
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
  have hmono : (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) ≤
      (1 - (B.t0 : ℝ)) * ((((Hhi B.ahi : ℚ) : ℝ) + ((Hhi B.bhi : ℚ) : ℝ)) / 2 -
        (CKLaneD.EMIN : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hs' : (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤
      (1 - (B.t0 : ℝ)) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) := by nlinarith
  exfalso
  linarith

/-! ## Row-independent box statements and their leaf adapters -/

/-- Parent dominance on a box (Lane M05) gives the obligation (vacuous in-row). -/
theorem leafOK_of_parentBox {B : CKLaneD.Box} (h : ParentBox B) : LeafOK B := by
  intro k μ _ _ _ _ _ _ _ _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact absurd (h k μ hin) (not_le.mpr hact')

/-- Parent dominance on a box for laws with `1/100 ≤ b - a`. -/
def ParentBoxD (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), CKLaneD.InBox B μ.a μ.b μ.meanEntropy →
    1 / 100 ≤ μ.b - μ.a → psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

theorem leafOK_of_parentBoxD {B : CKLaneD.Box} (h : ParentBoxD B) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact absurd (h k μ hin hd) (not_le.mpr hact')

/-- psi-candidate statement on a box, for ordered laws. -/
def RadSem (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), CKLaneD.InBox B μ.a μ.b μ.meanEntropy → μ.a < μ.b →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

theorem leafOK_of_radSem {B : CKLaneD.Box} (h : RadSem B) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact (hybrid_gap_le_psi hact'.le).trans (h k μ hin (by linarith))

/-- Hybrid gap statement on a box, for ordered laws with a (weakly) active psi branch. -/
def GapBox (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), CKLaneD.InBox B μ.a μ.b μ.meanEntropy → μ.a < μ.b →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem leafOK_of_gapBox {B : CKLaneD.Box} (h : GapBox B) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact h k μ hin (by linarith) hact'.le

end CKLaneN6

end


