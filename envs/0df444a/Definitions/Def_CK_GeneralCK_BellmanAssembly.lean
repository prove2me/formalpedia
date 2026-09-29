-- Prove2me | Definitions.Def_CK_GeneralCK_BellmanAssembly
-- name    : CK_GeneralCK_BellmanAssembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:28:05.383356+00:00
-- url     : https://prove2.me/theorems/765fc4ac-411c-4010-8221-bbd3872269ee
-- title:
--   Courtade–Kumar proof module `GeneralCK.BellmanAssembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.BellmanAssembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.BellmanAssembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.BellmanAssembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/BellmanAssembly.lean)

import Definitions.Def_CK_GeneralCK_FiniteLaw
import Definitions.Def_CK_GeneralCK_ProfileConvexity

/-! Exact branch reductions. These do not assert that the remaining regional bounds hold. -/
namespace GeneralCK
open scoped BigOperators

theorem psi_eq_P (m h : ℝ) : psi m h = Scalar.P (H m - h) := by
  unfold psi Scalar.P
  congr 1
  ring

noncomputable def candidateGap (C : ℝ → ℝ → ℝ) (a b e f : ℝ) : ℝ :=
  C ((a + b) / 2) ((e + f) / 2) - (C a e + C b f) / 2

theorem hybrid_gap_le_phi {a b e f : ℝ}
    (hp : psi ((a + b) / 2) ((e + f) / 2) ≤ phi ((a + b) / 2) ((e + f) / 2)) :
    candidateGap B a b e f ≤ candidateGap phi a b e f := by
  have h₁ := le_max_left (phi a e) (psi a e)
  have h₂ := le_max_left (phi b f) (psi b f)
  unfold candidateGap
  rw [show B ((a + b) / 2) ((e + f) / 2) = phi ((a + b) / 2) ((e + f) / 2)
    from max_eq_left hp]
  change _ ≤ _
  dsimp only [B] at *
  linarith

theorem hybrid_gap_le_psi {a b e f : ℝ}
    (hp : phi ((a + b) / 2) ((e + f) / 2) ≤ psi ((a + b) / 2) ((e + f) / 2)) :
    candidateGap B a b e f ≤ candidateGap psi a b e f := by
  have h₁ := le_max_right (phi a e) (psi a e)
  have h₂ := le_max_right (phi b f) (psi b f)
  unfold candidateGap
  rw [show B ((a + b) / 2) ((e + f) / 2) = psi ((a + b) / 2) ((e + f) / 2)
    from max_eq_right hp]
  dsimp only [B] at *
  linarith

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

noncomputable def midpoint (μ : InteriorLaw ι) : ℝ := (μ.a + μ.b) / 2
noncomputable def meanEntropy (μ : InteriorLaw ι) : ℝ := (μ.e + μ.f) / 2
noncomputable def entropyDrop (μ : InteriorLaw ι) : ℝ :=
  H μ.midpoint - (H μ.a + H μ.b) / 2
noncomputable def meanDeficit (μ : InteriorLaw ι) : ℝ :=
  ((H μ.a - μ.e) + (H μ.b - μ.f)) / 2
noncomputable def information (μ : InteriorLaw ι) : ℝ := H μ.midpoint - μ.meanEntropy
noncomputable def splitBound (μ : InteriorLaw ι) : ℝ :=
  Scalar.P (μ.entropyDrop + μ.meanDeficit) - Scalar.P μ.meanDeficit

theorem left_deficit_mem (μ : InteriorLaw ι) : H μ.a - μ.e ∈ Set.Ico (0 : ℝ) 1 := by
  have h₀ := μ.e_le_cap
  have h₁ := H_le_one μ.a
  have hp := μ.e_pos
  constructor <;> linarith

theorem right_deficit_mem (μ : InteriorLaw ι) : H μ.b - μ.f ∈ Set.Ico (0 : ℝ) 1 := by
  have h₀ := μ.f_le_cap
  have h₁ := H_le_one μ.b
  have hp := μ.f_pos
  constructor <;> linarith

theorem entropyDrop_nonneg (μ : InteriorLaw ι) : 0 ≤ μ.entropyDrop := by
  have h := Real.strictConcave_binEntropy.concaveOn.2
    ⟨μ.a_interior.1.le, μ.a_interior.2.le⟩
    ⟨μ.b_interior.1.le, μ.b_interior.2.le⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hd := div_le_div_of_nonneg_right h log_two_pos.le
  change 0 ≤ H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2
  unfold H
  have he : (1 / 2 : ℝ) * μ.a + (1 / 2) * μ.b = (μ.a + μ.b) / 2 := by ring
  rw [he] at hd
  simp only [add_div, mul_div_assoc] at hd
  rw [← add_div μ.a μ.b 2] at hd
  linarith

theorem information_eq (μ : InteriorLaw ι) :
    μ.information = μ.entropyDrop + μ.meanDeficit := by
  unfold information entropyDrop meanDeficit meanEntropy
  ring

theorem meanDeficit_mem (μ : InteriorLaw ι) : μ.meanDeficit ∈ Set.Ico (0 : ℝ) 1 := by
  have h₁ := μ.left_deficit_mem
  have h₂ := μ.right_deficit_mem
  unfold meanDeficit
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

theorem information_mem (μ : InteriorLaw ι) : μ.information ∈ Set.Ico (0 : ℝ) 1 := by
  have h₀ := μ.entropyDrop_nonneg
  have h₁ := μ.meanDeficit_mem.1
  have hc := H_le_one μ.midpoint
  have he := μ.e_pos
  have hf := μ.f_pos
  constructor
  · rw [μ.information_eq]; linarith
  · unfold information meanEntropy; linarith

/-- Jensen removes the entropy split, including exact child-cap equality. -/
theorem psi_gap_le_splitBound (μ : InteriorLaw ι) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.splitBound := by
  have hj := Scalar.P_convexOn.2 μ.left_deficit_mem μ.right_deficit_mem
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  have hmid : (1 / 2 : ℝ) * (H μ.a - μ.e) + (1 / 2) * (H μ.b - μ.f) = μ.meanDeficit := by
    unfold meanDeficit; ring
  rw [hmid] at hj
  simp only [candidateGap, psi_eq_P]
  change Scalar.P μ.information - _ ≤ _
  rw [μ.information_eq]
  unfold splitBound
  linarith

/-- A split-uniform scalar bound is sufficient only when psi is active at the parent. -/
theorem gap_le_of_splitBound (μ : InteriorLaw ι)
    (hp : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy)
    (hs : μ.splitBound ≤ μ.cost) : μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hp).trans ((μ.psi_gap_le_splitBound).trans hs)

end InteriorLaw

/-- The unproved regional obligations are confined to their correct active parent branch. -/
theorem finiteHybridBellman_of_canonical_branches
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost) :
    FiniteHybridBellman := by
  apply finiteHybridBellman_of_canonical
  intro k μ hab hsum
  by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact (hybrid_gap_le_phi hp).trans (hphi k μ hab hsum)
  · exact hpsi k μ hab hsum (lt_of_not_ge hp)

end GeneralCK


