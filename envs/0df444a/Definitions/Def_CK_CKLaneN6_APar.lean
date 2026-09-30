-- Prove2me | Definitions.Def_CK_CKLaneN6_APar
-- name    : CK_CKLaneN6_APar
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:59:36.600796+00:00
-- url     : https://prove2.me/theorems/96bdc6b3-ee1a-4e1a-b5cc-5ceae17a82dd
-- title:
--   Courtade–Kumar proof module `CKLaneN6.APar` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.APar` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.APar` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.APar (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/APar.lean)

import Definitions.Def_CK_CKLaneN6_Base
import Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentClosure
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy28
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy200
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy2048
import Definitions.Def_CK_GeneralCK_PsiOuterEntropyExtension

-- ===== source module CKLaneN6.APar =====
section

/-!
# Lane N6: compiled analytic parent dominance on archived boxes (`apar`)

For a law of an archived Thm 3 box with `1/100 ≤ b - a` (so `q = 1 - a - b ≥ b - a ≥ 1/100`, since
`b ≤ 1/2`), the box gives `q ∈ [max(1/100, 1-a1-b1), 1-a0-b0]` and `E ≤ E⁺ = EMIN + t1 (C0hi - EMIN)`.
If these enclosures lie in one of the compiled parent-dominance regions, `psi ≤ phi` at the parent:

* `q ≤ 1/2, E ≤ 1/200, 8E ≤ q` : `PsiOuterEntropy200.active_bias_lt_eight_entropy` (contrapositive)
* `q ≤ 3/10, 8E ≤ q`           : `PsiThreeTenthsParent.parent_dominance_ratio8`
* `q ≤ 2/5, 28E ≤ q`           : `PsiOuterEntropy28.parent_dominance_two_fifths28`
* `2/5 ≤ q ≤ 1/2, 75E ≤ q`     : `PsiOuterEntropy200.parent_dominance_half`
* `1/8 ≤ q ≤ 1/2, E ≤ 1/2048`  : `PsiOuterEntropy2048.parent_dominance_high_bias`
* `1/10 ≤ q ≤ 1/2, E ≤ 1/32768`: `PsiOuterEntropyExtension.parent_dominance`

`aparCheck_sound : aparCheck B = true → ParentBoxD B` (no other hypothesis).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6.APar

open GeneralCK CKLaneE.FP CKLaneN6
open CKLaneM05.FE8 (Eup boxSane boxPts box_facts)

def qLoA (B : CKLaneD.Box) : ℚ := max (1 / 100) (1 - B.ahi - B.bhi)
def qHiA (B : CKLaneD.Box) : ℚ := 1 - B.alo - B.blo

def aparRegion (B : CKLaneD.Box) : Bool :=
  decide ((qHiA B ≤ 1 / 2 ∧ Eup B ≤ 1 / 200 ∧ 8 * Eup B ≤ qLoA B) ∨
    (qHiA B ≤ 3 / 10 ∧ 8 * Eup B ≤ qLoA B) ∨
    (qHiA B ≤ 2 / 5 ∧ 28 * Eup B ≤ qLoA B) ∨
    (2 / 5 ≤ qLoA B ∧ qHiA B ≤ 1 / 2 ∧ 75 * Eup B ≤ qLoA B) ∨
    (1 / 8 ≤ qLoA B ∧ qHiA B ≤ 1 / 2 ∧ Eup B ≤ 1 / 2048) ∨
    (1 / 10 ≤ qLoA B ∧ qHiA B ≤ 1 / 2 ∧ Eup B ≤ 1 / 32768))

def aparCheck (B : CKLaneD.Box) : Bool := boxSane B && boxPts B && aparRegion B

theorem aparCheck_sound {B : CKLaneD.Box} (h : aparCheck B = true) : ParentBoxD B := by
  intro k μ hin hd
  simp only [aparCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hs, hp⟩, hreg⟩ := h
  obtain ⟨_, _, _, _, _, _, _, hEup, _, hE0, _⟩ := box_facts hs hp μ hin
  have hs' := hs
  simp only [boxSane, decide_eq_true_eq] at hs'
  obtain ⟨_, _, _, _, _, sb2, _, _, _⟩ := hs'
  obtain ⟨h1, h2, h3, h4, _, _⟩ := hin
  have rb2 : ((B.bhi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr sb2; push_cast at h'; exact h'
  set q : ℝ := 1 - μ.a - μ.b with hqdef
  set E : ℝ := μ.meanEntropy with hEdef
  have hq_lo : ((qLoA B : ℚ) : ℝ) ≤ q := by
    unfold qLoA
    rw [Rat.cast_max]
    push_cast
    apply max_le
    · linarith
    · linarith
  have hq_hi : q ≤ ((qHiA B : ℚ) : ℝ) := by
    unfold qHiA; push_cast; linarith
  have hq0 : (1 : ℝ) / 100 ≤ q := by
    have : ((1 / 100 : ℚ) : ℝ) ≤ ((qLoA B : ℚ) : ℝ) := by
      exact_mod_cast (le_max_left _ _ : (1 / 100 : ℚ) ≤ max (1 / 100) (1 - B.ahi - B.bhi))
    push_cast at this
    linarith
  have hqpos : 0 < q := by linarith
  have hmid : μ.midpoint = (1 - q) / 2 := by
    rw [hqdef]; unfold InteriorLaw.midpoint; ring
  rw [hmid]
  simp only [aparRegion, decide_eq_true_eq] at hreg
  -- real forms of the rational region conditions
  have cq : ∀ {x y : ℚ}, x ≤ y → (x : ℝ) ≤ (y : ℝ) := fun hxy => by exact_mod_cast hxy
  rcases hreg with ⟨r1, r2, r3⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2, r3⟩ | ⟨r1, r2, r3⟩ | ⟨r1, r2, r3⟩
  · -- q ≤ 1/2, E ≤ 1/200, 8E ≤ q
    have c1 := cq r1; have c2 := cq r2; have c3 := cq r3
    push_cast at c1 c2 c3
    by_contra hn
    have hact : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E := (lt_of_not_ge hn).le
    have := PsiOuterEntropy200.active_bias_lt_eight_entropy (by linarith) hE0 (by linarith) hact
    linarith
  · have c1 := cq r1; have c2 := cq r2
    push_cast at c1 c2
    exact (PsiThreeTenthsParent.parent_dominance_ratio8 hqpos (by linarith) hE0 (by linarith)).le
  · have c1 := cq r1; have c2 := cq r2
    push_cast at c1 c2
    exact (PsiOuterEntropy28.parent_dominance_two_fifths28 hqpos (by linarith) hE0
      (by linarith)).le
  · have c1 := cq r1; have c2 := cq r2; have c3 := cq r3
    push_cast at c1 c2 c3
    exact (PsiOuterEntropy200.parent_dominance_half (by linarith) (by linarith) hE0
      (by linarith)).le
  · have c1 := cq r1; have c2 := cq r2; have c3 := cq r3
    push_cast at c1 c2 c3
    exact (PsiOuterEntropy2048.parent_dominance_high_bias (by linarith) (by linarith) hE0
      (by linarith)).le
  · have c1 := cq r1; have c2 := cq r2; have c3 := cq r3
    push_cast at c1 c2 c3
    exact (PsiOuterEntropyExtension.parent_dominance (by linarith) (by linarith) hE0
      (by linarith)).le

/-- Leaf form for the Thm 3 row. -/
theorem leafOK_of_aparCheck {B : CKLaneD.Box} (h : aparCheck B = true) : LeafOK B :=
  leafOK_of_parentBoxD (aparCheck_sound h)

end CKLaneN6.APar

end


