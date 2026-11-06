-- Prove2me | Definitions.Def_GradSuffice_IsDualValued
-- name    : GradSuffice_IsDualValued
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:49.144204+00:00
-- url     : https://prove2.me/theorems/07059606-ea2a-487a-a847-0ee5228d6c90
-- title:
--   $B^\star$-valued adaptive sequence
-- statement:
--   Let $X$ be a real normed space with closed unit ball $B$, and let $B^\star$ be the closed unit ball of the dual space $X^\star$ for the dual norm $\|\xi\|_\star=\sup_{w\in B}|\xi\cdot w|$.
--
--   An **adaptive sequence** of length $m$ is a sequence of maps $\xi_i:\{-1,1\}^{i-1}\to X^\star$, $i=1,\dots,m$; equivalently, a labelling of the internal nodes of the complete binary tree of depth $m$ by dual vectors, the node reached by the sign prefix $\sigma_{<i}=(\sigma_1,\dots,\sigma_{i-1})$ carrying $\xi_i(\sigma_{<i})$. The sequence is **$B^\star$-valued** if every label has dual norm at most $1$:
--   $$\|\xi_i(s)\|_\star\le 1\qquad\text{for all } i \text{ and all } s\in\{-1,1\}^{i-1}.$$
--
--   In the paper every adaptive sequence is $B^\star$-valued; this condition appears in the definitions of sequential Rademacher complexity, M-type and uniformly bounded shattered trees.
--
--   **Formalization Note** An adaptive sequence of length $m$ is a `NondualOpt.Tree (StrongDual ℝ X) m`; positions are 0-based and the dual norm is the operator norm of `StrongDual ℝ X`.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.5

import Mathlib
import Definitions.Def_NondualOpt_Tree

namespace GradSuffice

/-- **`B⋆`-valued adaptive sequence (tree).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.5: "An adaptive sequence
`ξ̄ = (ξ₁, …, ξₘ)` is comprised of a sequence of mappings `ξᵢ : {−1, 1}^{i−1} → B⋆`.
Equivalently, `ξ̄` labels the internal nodes of a complete binary tree of depth `m` by elements of
`B⋆`."

**Formalization Note.** An adaptive sequence of length `m` (a complete binary tree of depth `m`
labelled by dual vectors) is a `NondualOpt.Tree (StrongDual ℝ X) m`, i.e. a family
`ξ i : (Fin i → Bool) → StrongDual ℝ X`; positions are 0-based. `B⋆` is the closed unit ball of
`StrongDual ℝ X` for the operator norm, which is the dual norm `‖ξ‖⋆ = sup_{w ∈ B} |ξ · w|` of
p.3. -/
def IsDualValued {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} (ξ : NondualOpt.Tree (StrongDual ℝ X) m) : Prop :=
  ∀ (i : Fin m) (s : Fin i → Bool), ‖ξ i s‖ ≤ 1

end GradSuffice


