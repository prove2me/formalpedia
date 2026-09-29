-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
-- name    : MaxLatticeFree_Geometry_IsLambdaSubspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:10:55.197737+00:00
-- url     : https://prove2.me/theorems/c95696f7-5c15-4272-a519-b6974f4e0f5a
-- title:
--   $\Lambda$-subspace (lattice subspace) of $V$ (Definition 7)
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$. A linear subspace $L\subseteq V$ is a **$\Lambda$-subspace of $V$** (the paper also says **lattice subspace of $V$**) if $L$ has a basis contained in $\Lambda$: there are linearly independent vectors $b_1,\dots,b_k\in\Lambda$ with
--
--   $$
--   L=\langle b_1,\dots,b_k\rangle .
--   $$
--
--   For the lattice $\mathbb Z^2$ of $\mathbb R^2$, the line $x_2=2x_1$ is a $\Lambda$-subspace, while the line $x_2=\sqrt2\,x_1$ is not. The distinction between $\Lambda$-subspaces and the remaining ("irrational") subspaces is what separates the two cases of Lovász's characterization.
--
--   **Formalization Note** The containment $L\subseteq V$ is part of the predicate. The zero subspace is a $\Lambda$-subspace (empty basis, $k=0$).
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 8, Definition 7

import Mathlib

namespace MaxLatticeFree.Geometry

/-- Definition 7 (arXiv:1701.06543v1, p. 8). Let `Λ` be a lattice of a linear space `V`. A linear
subspace `L` of `V` is a *`Λ`-subspace of `V`* (also called a *lattice subspace of `V`*) if `L` has
a basis contained in `Λ`: linearly independent vectors `b₁, …, b_k ∈ Λ` spanning `L`.
The containment `L ≤ V` is part of the predicate. `{0}` is a `Λ`-subspace (empty basis). -/
def IsLambdaSubspace {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  L ≤ V ∧ ∃ (k : ℕ) (b : Fin k → EuclideanSpace ℝ (Fin n)),
    LinearIndependent ℝ b ∧ Submodule.span ℝ (Set.range b) = L ∧ ∀ i, b i ∈ Λ

end MaxLatticeFree.Geometry


