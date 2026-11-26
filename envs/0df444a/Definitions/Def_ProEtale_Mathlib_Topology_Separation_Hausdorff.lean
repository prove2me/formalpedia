-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
-- name    : ProEtale_Mathlib_Topology_Separation_Hausdorff
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:09.962291+00:00
-- url     : https://prove2.me/theorems/e08f6d85-5eed-4429-8d32-db764c166c97
-- title:
--   A space is Hausdorff iff its diagonal is closed
-- statement:
--   For a topological space $X$, the file proves
--   $$X \text{ is Hausdorff} \iff \Delta_X = \{(x, x) : x \in X\} \text{ is closed in } X \times X.$$
--
--   This criterion is used to show that fibre products over Hausdorff spaces embed as closed subspaces of products.
--
--   **Formalization Note** Main declaration: `t2Space_iff_diagonal_closed`, with the diagonal written as `Set.range (fun x : X ↦ (x, x))`. It is a restatement of Mathlib's `t2_iff_isClosed_diagonal` and is tagged with Stacks 08ZE.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 08ZE. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Separation/Hausdorff.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Separation.Hausdorff

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- after `t2Space_iff_disjoint_nhds`
-- `by copilot`, this theorem exists in mathlib already.
@[stacks 08ZE]
theorem t2Space_iff_diagonal_closed {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ IsClosed (Set.range (fun x : X ↦ (x, x))) := by
  rw [show (fun x : X ↦ (x, x)) = Function.diag from rfl, Set.range_diag]
  exact t2_iff_isClosed_diagonal


