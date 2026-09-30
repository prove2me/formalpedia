-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisPartitionKernel
-- name    : CK_GeneralCK_Certificates_E8TAxisPartitionKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:37:41.429519+00:00
-- url     : https://prove2.me/theorems/a96e4233-cadb-487d-80cc-616cddc4404c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisPartitionKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisPartitionKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisPartitionKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisPartitionKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisPartitionKernel.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8AxisConsumers
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_reusable_cell_interface

-- ===== source module GeneralCK.Certificates.E8TAxisPartitionKernel =====
section

/-!
# Exact partition kernel for the E8 t-axis family

The historical search produced a binary subdivision tree.  This file proves
once and for all that a tree whose split points lie inside their parent boxes
covers its parent rectangle.  Generated files need only instantiate the tree
and provide one analytic proof at each leaf.
-/

namespace GeneralCK.Certificates.E8TAxisPartitionKernel

open GeneralCK















def Tree.leafCount : Tree → ℕ
  | .leaf => 1
  | .splitS _ left right | .splitT _ left right => left.leafCount + right.leafCount















theorem locate_leaf {P : Rect → Prop} {tree : Tree} {r : Rect} {s t : ℝ}
    (hall : AllLeaves P tree r) (hpoint : r.Covers s t) :
    ∃ leaf, P leaf ∧ leaf.Covers s t := by
  induction tree generalizing r with
  | leaf => exact ⟨r, hall, hpoint⟩
  | splitS x left right ihl ihr =>
      rcases hall with ⟨hx0, hx1, hl, hr⟩
      by_cases hs : s ≤ (x : ℝ)
      · apply ihl hl
        exact ⟨hpoint.1, hs, hpoint.2.2⟩
      · apply ihr hr
        exact ⟨le_of_not_ge hs, hpoint.2.1, hpoint.2.2⟩
  | splitT x lower upper ihl ihu =>
      rcases hall with ⟨hx0, hx1, hl, hu⟩
      by_cases ht : t ≤ (x : ℝ)
      · apply ihl hl
        exact ⟨hpoint.1, hpoint.2.1, hpoint.2.2.1, ht⟩
      · apply ihu hu
        exact ⟨hpoint.1, hpoint.2.1, le_of_not_ge ht, hpoint.2.2.2⟩




noncomputable def domain : Rect := ⟨3 / 50, 63 / 20, 0, 1 / 50⟩

theorem derivativeBound_of_tree {tree : Tree}
    (hall : AllLeaves CellPositive tree domain) : E8TAxisDerivativeBound := by
  intro s t hadm hs0 hs1 ht1
  have ht0 : 0 ≤ t := hadm.2.1.le
  obtain ⟨leaf, hleaf, hcover⟩ := locate_leaf hall
    (r := domain) (s := s) (t := t) ⟨hs0, hs1, ht0, ht1⟩
  exact hleaf s t hadm hcover

#print axioms locate_leaf
#print axioms derivativeBound_of_tree

end GeneralCK.Certificates.E8TAxisPartitionKernel

end


