-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Constructions
-- name    : ProEtale_Mathlib_Topology_Constructions
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:04.010398+00:00
-- url     : https://prove2.me/theorems/90e5eb9b-3c6a-4e26-9659-30a1e4717978
-- title:
--   The map from a product with a discrete factor to the corresponding sigma type is continuous
-- statement:
--   Let $\alpha$ be a discrete topological space and $\beta$ a topological space. The file proves that the canonical map
--   $$\alpha \times \beta \longrightarrow \textstyle\coprod_{a\in\alpha} \beta, \qquad (a, b) \mapsto (a, b),$$
--   from the product to the disjoint union (sigma type) of copies of $\beta$ indexed by $\alpha$, is continuous.
--
--   It is used to identify products with discrete spaces and disjoint unions, for example when handling constant sheaves and locally constant functions on profinite sets.
--
--   **Formalization Note** Main declaration: `Prod.continuous_toSigma`, about Mathlib's `Prod.toSigma : α × β → Σ _ : α, β`, assuming `[DiscreteTopology α]`. Only continuity is proved here (not that the map is a homeomorphism).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Constructions.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- after `Topology.isOpenEmbedding_sigmaMap`
variable {α β : Type*} [TopologicalSpace α] [b : TopologicalSpace β]
theorem Prod.continuous_toSigma [DiscreteTopology α] : Continuous (Prod.toSigma : α × β → _) := by
  refine ⟨fun U hU ↦ ?_⟩
  rw [isOpen_prod_iff]
  rw [isOpen_sigma_iff] at hU
  intro a b hab
  use {a}, ((Sigma.mk (β := fun _ ↦ β) a) ⁻¹' U)
  refine ⟨by simp, hU a, by simp, hab, fun t hT ↦ ?_⟩
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage] at hT
  simpa [← hT.1, Prod.toSigma] using hT.2


