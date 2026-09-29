-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
-- name    : MaxLatticeFree_Geometry_IsLambdaFree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:11:43.304798+00:00
-- url     : https://prove2.me/theorems/c6b93c0f-dff8-4888-a7d8-0e547d9854cc
-- title:
--   $\Lambda$-free and maximal $\Lambda$-free convex sets of $W$ (Definition 8)
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ and let $W$ be a linear space containing $V$. A set $S\subseteq\mathbb R^n$ is a **$\Lambda$-free convex set of $W$** if
--
--   1. $S\subseteq W$,
--   2. $S$ is convex, and
--   3. $\Lambda\cap\mathbf{int}_W(S)=\emptyset$, i.e. no point of $\Lambda$ lies in the interior of $S$ relative to $W$.
--
--   $S$ is a **maximal $\Lambda$-free convex set of $W$** if it is a $\Lambda$-free convex set of $W$ and is not properly contained in any other $\Lambda$-free convex set of $W$:
--
--   $$
--   K \text{ a } \Lambda\text{-free convex set of } W,\ S\subseteq K \ \Longrightarrow\ K=S .
--   $$
--
--   These are the objects classified by Theorems 9 and 10. With $W=V=\mathbb R^n$ and $\Lambda=\mathbb Z^n$ they are the classical maximal lattice-free convex sets from which intersection cuts are built.
--
--   **Formalization Note** The predicates take $\Lambda$ and $W$ as parameters; that $\Lambda$ is a lattice of some $V\subseteq W$ is a hypothesis of each theorem, not part of the predicate.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 8, Definition 8

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_intW

namespace MaxLatticeFree.Geometry

/-- Definition 8, first part (arXiv:1701.06543v1, p. 8). A set `S ⊆ ℝⁿ` is a *`Λ`-free convex set
of the linear space `W`* if `S ⊆ W`, `S` is convex, and no point of `Λ` lies in `int_W(S)`, the
interior of `S` relative to `W`. (In the paper `Λ` is a lattice of a linear space `V ⊆ W`; those
standing assumptions are hypotheses of each theorem.) -/
def IsLambdaFree {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  S ⊆ (W : Set (EuclideanSpace ℝ (Fin n))) ∧ Convex ℝ S ∧
    (Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ intW (W : Set (EuclideanSpace ℝ (Fin n))) S = ∅

/-- Definition 8, second part (arXiv:1701.06543v1, p. 8). `S` is a *maximal `Λ`-free convex set of
`W`* if it is a `Λ`-free convex set of `W` and is not properly contained in any `Λ`-free convex
set of the same `W`. -/
def IsMaxLambdaFree {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsLambdaFree Λ W S ∧ ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsLambdaFree Λ W K → S ⊆ K → K = S

end MaxLatticeFree.Geometry


