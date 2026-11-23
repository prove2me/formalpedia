-- Prove2me | Definitions.Def_MaxLatticeFree_Geometry_Supplement_NormH
-- name    : MaxLatticeFree_Geometry_Supplement_NormH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:58:47.29771+00:00
-- url     : https://prove2.me/theorems/11060c76-c486-4fa5-ad46-cf46e15629d6
-- title:
--   The norm $\|\cdot\|_H$ on $\mathcal W$ and closure with respect to it
-- statement:
--   Let $W\subseteq\mathbb R^q$ be a linear subspace and let $\mathcal W$ be the space of functions $s=(s_r)_{r\in W}$ with finite support. The norm $\|\cdot\|_H$ on $\mathcal W$ is
--
--   $$
--   \|s\|_H=|s_0|+\sum_{r\in W\setminus\{0\}}\|r\|\,|s_r| ,
--   $$
--
--   where $\|r\|$ is the Euclidean norm. For $A\subseteq\mathcal W$, its closure $\bar A$ is the set of $s\in\mathcal W$ such that for every $\varepsilon>0$ some $t\in A$ satisfies $\|s-t\|_H<\varepsilon$.
--
--   Unlike the Euclidean norm on $\mathcal W$, this norm makes every function $s\mapsto\sum_r\psi(r)s_r$ with continuous positively homogeneous $\psi$ continuous (Lemma 32), which is what makes the closure in Theorem 4 an intersection of half-spaces.
--
--   **Formalization Note** $\mathcal W$ is `W →₀ ℝ`. The sum is taken over the whole support; its term at $r=0$ vanishes because $\|0\|=0$, so the coordinate $s_0$ carries weight $1$ exactly as on the page.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 7, definition of $\|\cdot\|_H$ and $\bar A$

import Mathlib

namespace MaxLatticeFree.Geometry.Supplement

/-- The norm `‖s‖_H = |s_0| + ∑_{r ∈ W ∖ {0}} ‖r‖ |s_r|` on the space `𝒲 = W →₀ ℝ` of finitely
supported functions (arXiv:1701.06543v1, p. 7), `‖r‖` the Euclidean norm. The term `r = 0` of the
sum vanishes because `‖0‖ = 0`, so the coordinate at `0` has weight `1`. -/
noncomputable def normH {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (s : W →₀ ℝ) : ℝ :=
  |s 0| + s.sum (fun r c => ‖(r : EuclideanSpace ℝ (Fin q))‖ * |c|)

/-- The closure `Ā` of `A ⊆ 𝒲` with respect to `‖·‖_H` (arXiv:1701.06543v1, p. 7): the points
`s` with elements of `A` arbitrarily close to `s` in `‖·‖_H`. -/
noncomputable def closureH {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (A : Set (W →₀ ℝ)) :
    Set (W →₀ ℝ) :=
  {s | ∀ ε : ℝ, 0 < ε → ∃ t ∈ A, normH (s - t) < ε}

end MaxLatticeFree.Geometry.Supplement


