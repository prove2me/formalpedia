-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapSymmetry
-- name    : CK_GeneralCK_PureGapSymmetry
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:50:03.41556+00:00
-- url     : https://prove2.me/theorems/97770d53-6ea1-4136-8755-e15f621fe1c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapSymmetry` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapSymmetry` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapSymmetry` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapSymmetry (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapSymmetry.lean)

import Definitions.Def_CK_GeneralCK_CorrectionBasics

/-!
# Exact symmetries of the retained pure gap

The retained pure-gap argument canonicalizes a four-moment tuple using only
exchange of the two complete labels and simultaneous complementation of both
means.  This file proves that these operations preserve `candidateGap phi`,
the four-moment lower bound, and hence `pureGap`.
-/

namespace GeneralCK

/-- The radial candidate is invariant under complementing its mean. -/
@[simp] theorem phi_complement (m h : ℝ) : phi (1 - m) h = phi m h := by
  unfold phi
  congr 2
  rw [show 1 - 2 * (1 - m) = -(1 - 2 * m) by ring, abs_neg]

/-- Exchanging the two complete mean-entropy labels preserves the `phi` gap. -/
theorem candidateGap_phi_swap (a b e f : ℝ) :
    candidateGap phi b a f e = candidateGap phi a b e f := by
  unfold candidateGap
  rw [add_comm b a, add_comm f e, add_comm (phi b f) (phi a e)]

/-- Simultaneously complementing both means preserves the `phi` gap. -/
theorem candidateGap_phi_complement (a b e f : ℝ) :
    candidateGap phi (1 - a) (1 - b) e f = candidateGap phi a b e f := by
  unfold candidateGap
  rw [show ((1 - a) + (1 - b)) / 2 = 1 - (a + b) / 2 by ring]
  simp only [phi_complement]

/-- Exchanging the two complete labels preserves the four-moment lower bound. -/
theorem fourMomentLowerBound_swap (a b e f : ℝ) :
    fourMomentLowerBound b a f e = fourMomentLowerBound a b e f := by
  unfold fourMomentLowerBound
  rw [abs_sub_comm b a, add_comm f e, entropyCorrection_comm f e]

/-- Simultaneously complementing both means preserves the four-moment lower bound. -/
theorem fourMomentLowerBound_complement (a b e f : ℝ) :
    fourMomentLowerBound (1 - a) (1 - b) e f = fourMomentLowerBound a b e f := by
  unfold fourMomentLowerBound
  congr 2
  rw [show (1 - a) - (1 - b) = b - a by ring, abs_sub_comm b a]

/-- Exchanging the two complete labels preserves the retained pure gap. -/
@[simp] theorem pureGap_swap (a b e f : ℝ) :
    pureGap b a f e = pureGap a b e f := by
  unfold pureGap
  rw [fourMomentLowerBound_swap, candidateGap_phi_swap]

/-- Simultaneously complementing both means preserves the retained pure gap. -/
@[simp] theorem pureGap_complement (a b e f : ℝ) :
    pureGap (1 - a) (1 - b) e f = pureGap a b e f := by
  unfold pureGap
  rw [fourMomentLowerBound_complement, candidateGap_phi_complement]

/-- Reflecting only the first mean preserves the pointwise pure gap.  This is
an algebraic symmetry of `pureGap`; it is not asserted for the Bellman value. -/
@[simp] theorem pureGap_reflect_left (a b e f : ℝ) :
    pureGap (1 - a) b e f = pureGap a b e f := by
  have houter : |(1 - a) - b| = |1 - 2 * ((a + b) / 2)| := by
    congr 1
    ring
  have hcenter : |1 - 2 * (((1 - a) + b) / 2)| = |a - b| := by
    congr 1
    ring
  have hchild : |1 - 2 * (1 - a)| = |1 - 2 * a| := by
    rw [show 1 - 2 * (1 - a) = -(1 - 2 * a) by ring, abs_neg]
  unfold pureGap fourMomentLowerBound candidateGap phi
  rw [houter, hcenter, hchild]
  ring

/-- Reflecting only the second mean preserves the pointwise pure gap. -/
@[simp] theorem pureGap_reflect_right (a b e f : ℝ) :
    pureGap a (1 - b) e f = pureGap a b e f := by
  calc
    pureGap a (1 - b) e f = pureGap (1 - b) a f e := (pureGap_swap _ _ _ _).symm
    _ = pureGap b a f e := pureGap_reflect_left b a f e
    _ = pureGap a b e f := (pureGap_swap b a f e).symm

/-- Physical means admit a sorted lower-half representative of the same pure
gap.  The entropy coordinates move only together with a full label swap. -/
theorem exists_sorted_lower_half_pureGap {a b e f : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    ∃ x y g h : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 / 2 ∧
      ((g = e ∧ h = f ∧ H x = H a ∧ H y = H b) ∨
       (g = f ∧ h = e ∧ H x = H b ∧ H y = H a)) ∧
      pureGap x y g h = pureGap a b e f := by
  let ra := min a (1 - a)
  let rb := min b (1 - b)
  have hra₀ : 0 ≤ ra := le_min ha₀ (sub_nonneg.mpr ha₁)
  have hrb₀ : 0 ≤ rb := le_min hb₀ (sub_nonneg.mpr hb₁)
  have hra_half : ra ≤ 1 / 2 := by
    dsimp only [ra]
    rcases le_total a (1 / 2) with ha | ha
    · exact (min_le_left _ _).trans ha
    · exact (min_le_right _ _).trans (by linarith)
  have hrb_half : rb ≤ 1 / 2 := by
    dsimp only [rb]
    rcases le_total b (1 / 2) with hb | hb
    · exact (min_le_left _ _).trans hb
    · exact (min_le_right _ _).trans (by linarith)
  have hHa : H ra = H a := by
    dsimp only [ra]
    by_cases ha : a ≤ 1 - a
    · rw [min_eq_left ha]
    · rw [min_eq_right (le_of_not_ge ha), H_complement]
  have hHb : H rb = H b := by
    dsimp only [rb]
    by_cases hb : b ≤ 1 - b
    · rw [min_eq_left hb]
    · rw [min_eq_right (le_of_not_ge hb), H_complement]
  have hreflect : pureGap ra rb e f = pureGap a b e f := by
    have hraeq : pureGap ra rb e f = pureGap a rb e f := by
      dsimp only [ra]
      by_cases ha : a ≤ 1 - a
      · rw [min_eq_left ha]
      · rw [min_eq_right (le_of_not_ge ha), pureGap_reflect_left]
    have hrbeq : pureGap a rb e f = pureGap a b e f := by
      dsimp only [rb]
      by_cases hb : b ≤ 1 - b
      · rw [min_eq_left hb]
      · rw [min_eq_right (le_of_not_ge hb), pureGap_reflect_right]
    exact hraeq.trans hrbeq
  rcases le_total ra rb with hab | hba
  · exact ⟨ra, rb, e, f, hra₀, hab, hrb_half,
      Or.inl ⟨rfl, rfl, hHa, hHb⟩, hreflect⟩
  · exact ⟨rb, ra, f, e, hrb₀, hba, hra_half,
      Or.inr ⟨rfl, rfl, hHb, hHa⟩,
      (pureGap_swap ra rb e f).trans hreflect⟩

/-- Every pure-gap tuple can be moved into the canonical mean chamber using
only the two exact target symmetries. -/
theorem pureGap_nonneg_of_canonical
    (hcanonical : ∀ a b e f : ℝ,
      a ≤ b → a + b ≤ 1 → 0 ≤ pureGap a b e f)
    (a b e f : ℝ) : 0 ≤ pureGap a b e f := by
  by_cases hab : a ≤ b
  · by_cases hsum : a + b ≤ 1
    · exact hcanonical a b e f hab hsum
    · have h := hcanonical (1 - b) (1 - a) f e (by linarith) (by linarith)
      simpa only [pureGap_swap, pureGap_complement] using h
  · by_cases hsum : a + b ≤ 1
    · have h := hcanonical b a f e (le_of_not_ge hab) (by linarith)
      simpa only [pureGap_swap] using h
    · have h := hcanonical (1 - a) (1 - b) e f (by linarith) (by linarith)
      simpa only [pureGap_complement] using h

/-- For physical means, the individual reflection identities and label
exchange reduce the pure-gap theorem to the sorted lower-half chart. -/
theorem pureGap_nonneg_of_sorted_lower_half
    (hlower : ∀ a b e f : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 / 2 → 0 ≤ pureGap a b e f)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) : 0 ≤ pureGap a b e f := by
  let ra := min a (1 - a)
  let rb := min b (1 - b)
  have hra₀ : 0 ≤ ra := le_min ha₀ (sub_nonneg.mpr ha₁)
  have hrb₀ : 0 ≤ rb := le_min hb₀ (sub_nonneg.mpr hb₁)
  have hra_half : ra ≤ 1 / 2 := by
    dsimp only [ra]
    rcases le_total a (1 / 2) with ha | ha
    · exact (min_le_left _ _).trans ha
    · exact (min_le_right _ _).trans (by linarith)
  have hrb_half : rb ≤ 1 / 2 := by
    dsimp only [rb]
    rcases le_total b (1 / 2) with hb | hb
    · exact (min_le_left _ _).trans hb
    · exact (min_le_right _ _).trans (by linarith)
  have hreflect : pureGap ra rb e f = pureGap a b e f := by
    have hraeq : pureGap ra rb e f = pureGap a rb e f := by
      dsimp only [ra]
      by_cases ha : a ≤ 1 - a
      · rw [min_eq_left ha]
      · rw [min_eq_right (le_of_not_ge ha), pureGap_reflect_left]
    have hrbeq : pureGap a rb e f = pureGap a b e f := by
      dsimp only [rb]
      by_cases hb : b ≤ 1 - b
      · rw [min_eq_left hb]
      · rw [min_eq_right (le_of_not_ge hb), pureGap_reflect_right]
    exact hraeq.trans hrbeq
  rw [← hreflect]
  rcases le_total ra rb with hab | hba
  · exact hlower ra rb e f hra₀ hab hrb_half
  · have h := hlower rb ra f e hrb₀ hba hra_half
    simpa only [pureGap_swap] using h

end GeneralCK


