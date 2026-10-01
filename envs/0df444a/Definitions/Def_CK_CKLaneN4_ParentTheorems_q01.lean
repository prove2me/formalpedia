-- Prove2me | Definitions.Def_CK_CKLaneN4_ParentTheorems_q01
-- name    : CK_CKLaneN4_ParentTheorems_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:56:07.299984+00:00
-- url     : https://prove2.me/theorems/fee8f0f8-fdf4-4485-8cca-fd507f2ebd75
-- title:
--   Courtade–Kumar proof module `CKLaneN4.ParentTheorems (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.ParentTheorems (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.ParentTheorems (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.ParentTheorems (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/ParentTheorems (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneN4_ParentTheorems_q00

namespace CKLaneN4
open GeneralCK
/-- HIGH_Q_PARENT: parent dominance on `2/5 ≤ q ≤ 1/2`, `1/40 ≤ E ≤ 1/25`. -/
def HighQParent : Prop :=
  ∀ q E : ℝ, 2 / 5 ≤ q → q ≤ 1 / 2 → 1 / 40 ≤ E → E ≤ 1 / 25 →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

theorem parent8 : Parent8 := by
  intro q E hE hq hq25 h8
  by_cases h10 : q ≤ 1 / 10
  · exact PsiParentDominance.parent_dominance_ratio8_small_bias hE hq h10 h8
  by_cases h32 : 32 * E ≤ q
  · exact PsiOuterEntropy28.parent_dominance_two_fifths28 hq hq25 hE (by linarith)
  · have h := Parent8Tree.sem_root
    simp only [SemQX, Parent8Tree.root] at h
    exact h q E hE (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)

end CKLaneN4


