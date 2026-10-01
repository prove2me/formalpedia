-- Prove2me | Definitions.Def_CK_CKLaneN4_ParentTheorems_q00
-- name    : CK_CKLaneN4_ParentTheorems_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:48:15.254982+00:00
-- url     : https://prove2.me/theorems/ecefca8c-d113-4673-b485-d41716cfa5fe
-- title:
--   Courtade–Kumar proof module `CKLaneN4.ParentTheorems (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.ParentTheorems (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.ParentTheorems (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.ParentTheorems (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/ParentTheorems (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneN4_Parent8Tree
import Definitions.Def_CK_CKLaneN4_Parent16Tree
import Definitions.Def_CK_CKLaneN4_HighQTree
import Definitions.Def_CK_GeneralCK_PsiParentDominance
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy28
import Definitions.Def_CK_GeneralCK_PsiOuterEntropy200



/-!
# Lane N4: the parent-dominance theorems PARENT8, PARENT16 and HIGH_Q_PARENT

* `parent8` (CK_OPPOSITE_EXTENSION `audit/PARENT8_PROOF.md`): `0 < q ≤ 2/5`, `q/E ≥ 8` ⇒ `phi > psi`.
  Proof exactly as archived: `q ≤ 1/10` is Theorem C of CK_NO_SEPARATION_EXTENSION
  (`PsiParentDominance.parent_dominance_ratio8_small_bias`); the compact rectangle
  `[1/10, 2/5] × [8, 32]` is the archived 332-leaf partition (`Parent8Tree.sem_root`); the unbounded
  tail `x ≥ 32` is analytic (here `PsiOuterEntropy28.parent_dominance_two_fifths28`, `x ≥ 28`).
* `parent16` (CK_GENERAL_COMPLETION `parent/PARENT16_PROOF.md`): `0 < q ≤ 1/2`, `q/E ≥ 16` ⇒
  `phi > psi`: PARENT8 for `q ≤ 2/5`, the archived 69-leaf partition of `[2/5,1/2] × [16,128]`
  (`Parent16Tree.sem_root`), analytic tail `x ≥ 128` (here `PsiOuterEntropy200.parent_dominance_half`,
  `x ≥ 75`).
* `highQParent` (`reduction/eight_global/HIGH_Q_PARENT.py`): `2/5 ≤ q ≤ 1/2`, `1/40 ≤ E ≤ 1/25` ⇒
  `phi > psi`: the archived 59-leaf partition (`HighQTree.sem_root`).

`q` is the parent bias `|1 - 2m|`, the parent mean is `m = (1 - q)/2`.
-/

namespace CKLaneN4

open GeneralCK

/-- PARENT8: factor-eight parent dominance for `0 < q ≤ 2/5`. -/
def Parent8 : Prop :=
  ∀ q E : ℝ, 0 < E → 0 < q → q ≤ 2 / 5 → 8 * E ≤ q →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

/-- PARENT16: factor-sixteen parent dominance for `0 < q ≤ 1/2`. -/
def Parent16 : Prop :=
  ∀ q E : ℝ, 0 < E → 0 < q → q ≤ 1 / 2 → 16 * E ≤ q →
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E

end CKLaneN4


