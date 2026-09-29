-- Prove2me | Definitions.Def_CK_GeneralCK_PsiRetainedChildBridge_v2
-- name    : CK_GeneralCK_PsiRetainedChildBridge_v2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:32:57.267643+00:00
-- url     : https://prove2.me/theorems/69a5bcb5-d940-40f9-a9ec-9e0d7763f927
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiRetainedChildBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiRetainedChildBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiRetainedChildBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiRetainedChildBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiRetainedChildBridge.lean)

import Definitions.Def_CK_GeneralCK_PsiChildEntropyCoupling
import Definitions.Def_CK_GeneralCK_BellmanAssembly

-- ===== source module GeneralCK.PsiRetainedChildBridge =====
section

/-!
# Coordinate and feasibility bridge for the retained-child active-psi bound

These statements retain the child `phi` values beneath the actual hybrid
maxima and connect the signed radial coordinates to the original Bellman gap.
No scalar-owner inequality or cost lower bound is assumed.
-/

namespace GeneralCK.PsiRetainedChildBridge
open Set PsiChildEntropyCoupling

/-- Branch at the parent while retaining both phi contributions at the
children, rather than replacing them by psi. -/
theorem hybrid_gap_le_retained_phi {a b e f : ℝ}
    (hp : phi ((a + b) / 2) ((e + f) / 2) ≤
      psi ((a + b) / 2) ((e + f) / 2)) :
    candidateGap B a b e f ≤
      psi ((a + b) / 2) ((e + f) / 2) - (phi a e + phi b f) / 2 := by
  have h₁ : phi a e ≤ B a e := le_max_left _ _
  have h₂ : phi b f ≤ B b f := le_max_left _ _
  unfold candidateGap
  rw [show B ((a + b) / 2) ((e + f) / 2) =
      psi ((a + b) / 2) ((e + f) / 2) from max_eq_right hp]
  linarith

theorem coordinate_child_phi_average {d q E t : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d) :
    (phi ((1 - d - q) / 2) (E * (1 + t)) +
      phi ((1 + d - q) / 2) (E * (1 - t))) / 2 = childAverage d q E t := by
  have h₁ : |1 - 2 * ((1 - d - q) / 2)| = d + q := by
    rw [show (1 - 2 * ((1 - d - q) / 2) : ℝ) = d + q by ring,
      abs_of_nonneg (by linarith)]
  have h₂ : |1 - 2 * ((1 + d - q) / 2)| = d - q := by
    rw [show (1 - 2 * ((1 + d - q) / 2) : ℝ) = -(d - q) by ring,
      abs_neg, abs_of_nonneg (by linarith)]
  simp only [phi, childAverage, radialPhi, h₁, h₂]

/-- Exact bridge from canonical signed coordinates to the hybrid Bellman gap.
The same bound holds at a parent tie. -/
theorem canonical_hybrid_gap_le_childAverage {d q E t : ℝ}
    (hq : 0 ≤ q) (hqd : q ≤ d)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) :
    candidateGap B ((1 - d - q) / 2) ((1 + d - q) / 2)
      (E * (1 + t)) (E * (1 - t)) ≤
      eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t := by
  have hmean : (((1 - d - q) / 2 + (1 + d - q) / 2) / 2 : ℝ) = (1 - q) / 2 := by ring
  have hentropy : (E * (1 + t) + E * (1 - t)) / 2 = E := by ring
  have hp : phi (((1 - d - q) / 2 + (1 + d - q) / 2) / 2)
      ((E * (1 + t) + E * (1 - t)) / 2) ≤
      psi (((1 - d - q) / 2 + (1 + d - q) / 2) / 2)
      ((E * (1 + t) + E * (1 - t)) / 2) := by rwa [hmean, hentropy]
  have h := hybrid_gap_le_retained_phi hp
  rw [hmean, hentropy, coordinate_child_phi_average hq hqd] at h
  have he : psi ((1 - q) / 2) E = eta (E + (1 - H ((1 - q) / 2))) := by
    unfold psi
    congr 1
    ring
  rwa [he] at h

/-- Physical child entropy caps imply the physical parent entropy cap by
binary entropy concavity, even when a child itself is deterministic. -/
theorem entropy_mean_le_parent_cap {a b e f : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (he : e ≤ H a) (hf : f ≤ H b) :
    (e + f) / 2 ≤ H ((a + b) / 2) := by
  have hj := Real.strictConcave_binEntropy.concaveOn.2 ha hb
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  have h := div_le_div_of_nonneg_right hj log_two_pos.le
  have hmean : (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 := by ring
  rw [hmean] at h
  have hn : (H a + H b) / 2 ≤ H ((a + b) / 2) := by
    unfold H
    convert! h using 1
    ring
  linarith

/-- Domain condition needed for the parent gain follows from the actual
child feasibility constraints in the signed coordinate chart. -/
theorem canonical_parent_physical {d q E t : ℝ}
    (ha : (1 - d - q) / 2 ∈ Icc (0 : ℝ) 1)
    (hb : (1 + d - q) / 2 ∈ Icc (0 : ℝ) 1)
    (he : E * (1 + t) ≤ H ((1 - d - q) / 2))
    (hf : E * (1 - t) ≤ H ((1 + d - q) / 2)) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  have h := entropy_mean_le_parent_cap ha hb he hf
  have hmean : (((1 - d - q) / 2 + (1 + d - q) / 2) / 2 : ℝ) = (1 - q) / 2 := by ring
  have hentropy : (E * (1 + t) + E * (1 - t)) / 2 = E := by ring
  rw [hmean, hentropy] at h
  linarith

/-- Every positive pair has an exact interior signed entropy split. -/
theorem positive_entropy_split {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    |(e - f) / (e + f)| < 1 ∧
      (e + f) / 2 * (1 + (e - f) / (e + f)) = e ∧
      (e + f) / 2 * (1 - (e - f) / (e + f)) = f := by
  have hs : 0 < e + f := by linarith
  constructor
  · apply abs_lt.mpr
    constructor
    · apply (lt_div_iff₀ hs).2
      linarith
    · apply (div_lt_iff₀ hs).2
      linarith
  · constructor <;> field_simp <;> ring

/-- The bound in original means/entropies; this reconstructs the chart rather
than asking a user of the theorem to assume chart identities. -/
theorem opposite_hybrid_gap_le_childAverage {a b e f : ℝ}
    (_ha : a ≤ 1 / 2) (hb : 1 / 2 ≤ b) (hsum : a + b ≤ 1)
    (he : 0 < e) (hf : 0 < f)
    (hactive : phi ((a + b) / 2) ((e + f) / 2) ≤
      psi ((a + b) / 2) ((e + f) / 2)) :
    candidateGap B a b e f ≤
      eta ((e + f) / 2 + (1 - H ((a + b) / 2))) -
        childAverage (b - a) (1 - a - b) ((e + f) / 2) ((e - f) / (e + f)) := by
  have hq : 0 ≤ 1 - a - b := by linarith
  have hqd : 1 - a - b ≤ b - a := by linarith
  have hp : (1 - (1 - a - b)) / 2 = (a + b) / 2 := by ring
  have hactive' : phi ((1 - (1 - a - b)) / 2) ((e + f) / 2) ≤
      psi ((1 - (1 - a - b)) / 2) ((e + f) / 2) := by rwa [hp]
  have h := canonical_hybrid_gap_le_childAverage
    (t := (e - f) / (e + f)) hq hqd hactive'
  have hca : (1 - (b - a) - (1 - a - b)) / 2 = a := by ring
  have hcb : (1 + (b - a) - (1 - a - b)) / 2 = b := by ring
  obtain ⟨_, hce, hcf⟩ := positive_entropy_split he hf
  rwa [hca, hcb, hce, hcf, hp] at h

#print axioms hybrid_gap_le_retained_phi
#print axioms coordinate_child_phi_average
#print axioms canonical_hybrid_gap_le_childAverage
#print axioms entropy_mean_le_parent_cap
#print axioms canonical_parent_physical
#print axioms positive_entropy_split
#print axioms opposite_hybrid_gap_le_childAverage

end GeneralCK.PsiRetainedChildBridge

end


