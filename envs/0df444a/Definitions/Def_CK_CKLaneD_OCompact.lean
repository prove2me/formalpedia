-- Prove2me | Definitions.Def_CK_CKLaneD_OCompact
-- name    : CK_CKLaneD_OCompact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:37:51.59176+00:00
-- url     : https://prove2.me/theorems/73e2b834-a86f-4fda-9f8c-e6942b31e522
-- title:
--   Courtade–Kumar proof module `CKLaneD.OCompact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.OCompact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.OCompact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.OCompact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/OCompact.lean)

import Definitions.Def_CK_CKLaneD_Cover

-- ===== source module CKLaneD.OCompact =====
section

/-!
# Lane D: generic aggregation over the archived (O) tree into the manuscript row `OP_Compact`

`OPCompactRow` is a verbatim copy of `CKRoute.OP_Compact` from
`~/ck_lanes_20260923/coord/routesrc/CKRoute/Manuscript.lean` (with a verbatim local copy of
`CKRoute.PsiActive`), so the coordinator binds it by `Iff.rfl`.

`opCompact_of_leaves`: if every archived leaf `q` of `ArchTree.archTree` satisfies the per-leaf
obligation `OLeafOK (uvtBox q.1)` (OP_Compact hypotheses + the leaf's physical image), then the row holds.
It uses only the coverage lemma `archTree_cover`.
-/

namespace CKLaneD.OCompact

open GeneralCK

/-- Strict psi-activity at the parent (verbatim copy of `CKRoute.PsiActive`). -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- Row "otherwise": the complete 29,495-leaf finite cover of root (O)
(verbatim copy of `CKRoute.OP_Compact`). -/
def OPCompactRow : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a < 1 / 10 → 1 / 268435456 < μ.a → 1 / 8192 < μ.a + (1 - μ.b) →
    1 / 1000000 < μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- Per-leaf obligation in the OP_Compact-region form on the physical image of a leaf box. -/
def OLeafOK (U : UVT) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a < 1 / 10 → 1 / 268435456 < μ.a → 1 / 8192 < μ.a + (1 - μ.b) →
    1 / 1000000 < μ.meanEntropy → InUVT U μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Parent dominance (psi not strictly active) on the physical image of a leaf box. -/
def ParentUVT (U : UVT) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InUVT U μ.a μ.b μ.meanEntropy →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

/-- Adapter: the psi-candidate Bellman statement on a leaf image gives the row obligation. -/
theorem oLeafOK_of_semUVT (U : UVT) (h : SemUVT U) : OLeafOK U := by
  intro k μ _ _ _ _ _ _ _ hin hact
  exact (hybrid_gap_le_psi hact.le).trans (h k μ hin)

/-- Adapter: parent dominance on a leaf image makes the row obligation vacuous. -/
theorem oLeafOK_of_parentUVT (U : UVT) (h : ParentUVT U) : OLeafOK U := by
  intro k μ _ _ _ _ _ _ _ hin hact
  exact absurd (h k μ hin) (not_le.mpr hact)

theorem two_rpow_neg_28 : (2 : ℝ) ^ (-(28 : ℝ)) = 1 / 268435456 := by
  rw [Real.rpow_neg (by norm_num), show (28 : ℝ) = ((28 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- Generic aggregation over the archived (O) partition tree into the manuscript row. -/
theorem opCompact_of_leaves (h : ∀ q ∈ ArchTree.archTree.leaves, OLeafOK (uvtBox q.1)) :
    OPCompactRow := by
  intro k μ hab hsum hb ha10 ha28 hcor hE hact
  have ha0 : (2 : ℝ) ^ (-(28 : ℝ)) ≤ μ.a := by rw [two_rpow_neg_28]; exact ha28.le
  have hb1 : (2 : ℝ) ^ (-(28 : ℝ)) ≤ 1 - μ.b := by rw [two_rpow_neg_28]; linarith
  have hEm : (EMIN : ℝ) ≤ μ.meanEntropy := by
    unfold EMIN; push_cast; linarith
  obtain ⟨q, hq, hin⟩ := archTree_cover μ ha0 ha10.le hb hb1 hsum hEm
  exact h q hq k μ hab hsum hb ha10 ha28 hcor hE hin hact

end CKLaneD.OCompact

end


