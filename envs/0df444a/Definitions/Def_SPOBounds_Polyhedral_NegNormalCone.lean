-- Prove2me | Definitions.Def_SPOBounds_Polyhedral_NegNormalCone
-- name    : SPOBounds_Polyhedral_NegNormalCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:45:14.403673+00:00
-- url     : https://prove2.me/theorems/6b2cbd35-32de-48f7-826a-2b800bb7d083
-- title:
--   Negative normal cone $-N_S(\bar x)$ (the cones $\mathcal K_j$ of the normal fan)
-- statement:
--   Let $E$ be a real normed space and $S\subseteq E$. Cost vectors are continuous linear functionals $\hat c$ on $E$, with $\hat c^\top x$ denoting $\hat c(x)$. For a point $\bar x$, the *negative normal cone* of $S$ at $\bar x$ is
--   $$-N_S(\bar x) := \{\hat c : \hat c^\top(x-\bar x)\ge 0 \text{ for all } x\in S\}.$$
--   For $\bar x\in S$ it is exactly the set of cost vectors for which $\bar x$ is an optimal solution of $\min_{x\in S}\hat c^\top x$.
--
--   When $S=\mathrm{conv}\{v_1,\dots,v_K\}$ is a polytope, the cones $\mathcal K_j:=-N_S(v_j)$, $j=1,\dots,K$, cover the space of cost vectors and form part of the normal fan of the polytope; the paper uses them to describe the degenerate cost vectors and to compute the distance to degeneracy.
--
--   **Formalization Note** The cone is a subset of `StrongDual ℝ E`. It is defined for any point $\bar x$; the theorems use it only at the points $v_j$ of the convex hull representation.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 24, §5.2, eq. (9) (definition of $\mathcal K_j$)

import Mathlib

namespace SPOBounds.Polyhedral

/-- The negative normal cone `−N_S(x̄) = {ĉ : ĉᵀ(x − x̄) ≥ 0 for all x ∈ S}`
(arXiv:1905.11488v3, §5.2, p. 24, eq. (9), where `𝒦_j := −N_S(v_j)`): the cost vectors for which
`x̄` is an optimal solution of `min_{x ∈ S} ĉᵀx`. Cost vectors are continuous linear functionals,
so `ĉᵀx` is `ĉ x`. -/
def negNormalCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (xbar : E) : Set (StrongDual ℝ E) :=
  {chat | ∀ x ∈ S, 0 ≤ chat (x - xbar)}

end SPOBounds.Polyhedral


