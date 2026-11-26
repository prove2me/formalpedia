-- Prove2me | Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
-- name    : ProEtale_Mathlib_Order_BooleanAlgebra_Set
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:53.071405+00:00
-- url     : https://prove2.me/theorems/587f4b82-f162-4a16-8a6d-e98476ec2fa2
-- title:
--   Two sets are codisjoint if and only if their union is the whole type
-- statement:
--   For subsets $s, t$ of a type $\alpha$, $s$ and $t$ are codisjoint in the lattice of subsets (i.e. every upper bound of both is the whole type) if and only if
--   $$ s \cup t = \alpha . $$
--
--   **Formalization Note** The lemma is `Set.codisjoint_iff : Codisjoint s t ↔ s ∪ t = Set.univ`, proved by simplification from the general lattice-theoretic `codisjoint_iff`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Order/BooleanAlgebra/Set.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Order.BooleanAlgebra.Set

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
lemma Set.codisjoint_iff {α : Type*} {s t : Set α} : Codisjoint s t ↔ s ∪ t = .univ := by
  simp [_root_.codisjoint_iff]


