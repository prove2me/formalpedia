-- Prove2me | Definitions.Def_CK_GeneralCK_BellmanSymmetry
-- name    : CK_GeneralCK_BellmanSymmetry
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:30:15.14159+00:00
-- url     : https://prove2.me/theorems/d4b57ae7-a638-4bf8-b6b8-237069117827
-- title:
--   Courtade–Kumar proof module `GeneralCK.BellmanSymmetry` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.BellmanSymmetry` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.BellmanSymmetry` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.BellmanSymmetry (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/BellmanSymmetry.lean)

import Definitions.Def_CK_GeneralCK_BellmanAssembly

namespace GeneralCK.InteriorLaw
variable {ι : Type*} [Fintype ι]

@[simp] theorem swap_midpoint (μ : InteriorLaw ι) : μ.swap.midpoint = μ.midpoint := by
  simp only [midpoint, swap_a, swap_b, add_comm]

@[simp] theorem complement_midpoint (μ : InteriorLaw ι) :
    μ.complement.midpoint = 1 - μ.midpoint := by
  simp only [midpoint, complement_a, complement_b]
  ring

@[simp] theorem swap_meanEntropy (μ : InteriorLaw ι) : μ.swap.meanEntropy = μ.meanEntropy := by
  simp only [meanEntropy, swap_e, swap_f, add_comm]

@[simp] theorem complement_meanEntropy (μ : InteriorLaw ι) :
    μ.complement.meanEntropy = μ.meanEntropy := by
  simp only [meanEntropy, complement_e, complement_f]

@[simp] theorem swap_entropyDrop (μ : InteriorLaw ι) : μ.swap.entropyDrop = μ.entropyDrop := by
  simp only [entropyDrop, swap_midpoint, swap_a, swap_b, add_comm]

@[simp] theorem complement_entropyDrop (μ : InteriorLaw ι) :
    μ.complement.entropyDrop = μ.entropyDrop := by
  simp only [entropyDrop, complement_midpoint, complement_a, complement_b, H_complement]

@[simp] theorem swap_meanDeficit (μ : InteriorLaw ι) : μ.swap.meanDeficit = μ.meanDeficit := by
  simp only [meanDeficit, swap_a, swap_b, swap_e, swap_f, add_comm]

@[simp] theorem complement_meanDeficit (μ : InteriorLaw ι) :
    μ.complement.meanDeficit = μ.meanDeficit := by
  simp only [meanDeficit, complement_a, complement_b, complement_e, complement_f, H_complement]

@[simp] theorem swap_information (μ : InteriorLaw ι) : μ.swap.information = μ.information := by
  simp only [information, swap_midpoint, swap_meanEntropy]

@[simp] theorem complement_information (μ : InteriorLaw ι) :
    μ.complement.information = μ.information := by
  simp only [information, complement_midpoint, complement_meanEntropy, H_complement]

@[simp] theorem swap_splitBound (μ : InteriorLaw ι) : μ.swap.splitBound = μ.splitBound := by
  simp only [splitBound, swap_entropyDrop, swap_meanDeficit]

@[simp] theorem complement_splitBound (μ : InteriorLaw ι) :
    μ.complement.splitBound = μ.splitBound := by
  simp only [splitBound, complement_entropyDrop, complement_meanDeficit]

/-- Canonicalization preserves the split-uniform comparison and its information parameter. -/
theorem exists_canonical_split (μ : InteriorLaw ι) :
    ∃ ν : InteriorLaw ι, ν.a ≤ ν.b ∧ ν.a + ν.b ≤ 1 ∧
      ν.splitBound = μ.splitBound ∧ ν.information = μ.information ∧ ν.cost = μ.cost := by
  by_cases hab : μ.a ≤ μ.b
  · by_cases hs : μ.a + μ.b ≤ 1
    · exact ⟨μ, hab, hs, rfl, rfl, rfl⟩
    · refine ⟨μ.complement.swap, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [swap_a, swap_b, complement_a, complement_b]; linarith
      · simp only [swap_a, swap_b, complement_a, complement_b]; linarith
      · simp
      · simp
      · simp
  · by_cases hs : μ.a + μ.b ≤ 1
    · refine ⟨μ.swap, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [swap_a, swap_b]; linarith
      · simp only [swap_a, swap_b]; linarith
      · simp
      · simp
      · simp
    · refine ⟨μ.complement, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [complement_a, complement_b]; linarith
      · simp only [complement_a, complement_b]; linarith
      · simp
      · simp
      · simp

/-- Any canonical split bound under a condition on information transfers to all orientations. -/
theorem splitBound_le_cost_of_canonical (Q : ℝ → Prop)
    (hc : ∀ ν : InteriorLaw ι, ν.a ≤ ν.b → ν.a + ν.b ≤ 1 →
      Q ν.information → ν.splitBound ≤ ν.cost)
    (μ : InteriorLaw ι) (hQ : Q μ.information) : μ.splitBound ≤ μ.cost := by
  obtain ⟨ν, hab, hs, hsplit, hinfo, hcost⟩ := μ.exists_canonical_split
  have h := hc ν hab hs (hinfo ▸ hQ)
  simpa only [hsplit, hcost] using h

end GeneralCK.InteriorLaw


