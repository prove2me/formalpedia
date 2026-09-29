-- Prove2me | Definitions.Def_ApproxCliqueWidth_Certificate_CutRank
-- name    : ApproxCliqueWidth_Certificate_CutRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:30:46.609365+00:00
-- url     : https://prove2.me/theorems/e72bea84-c276-4875-b171-86233dc49e0e
-- title:
--   Cut-rank functions $\mathrm{cutrk}^*_G(X,Y)$ and $\mathrm{cutrk}_G(X)$
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$ and let $A(G)$ be its adjacency matrix over $\mathrm{GF}(2)$. For a matrix $M$ with rows indexed by $R$ and columns by $C$, and $X \subseteq R$, $Y \subseteq C$, write $M[X, Y]$ for the submatrix with rows $X$ and columns $Y$. For disjoint $X, Y \subseteq V$,
--   $$\mathrm{cutrk}^*_G(X, Y) = \mathrm{rk}\big(A(G)[X, Y]\big),$$
--   and the **cut-rank function** of $G$ is
--   $$\mathrm{cutrk}_G(X) = \mathrm{cutrk}^*_G(X, V \setminus X), \qquad X \subseteq V.$$
--
--   $\mathrm{cutrk}_G(X)$ counts, over $\mathrm{GF}(2)$, how many essentially different neighbourhoods across the cut $(X, V\setminus X)$ the vertices of $X$ have. The branch-width of $\mathrm{cutrk}_G$ is the **rank-width** $\mathrm{rwd}(G)$, and a branch-decomposition of $\mathrm{cutrk}_G$ is a rank-decomposition of $G$.
--
--   **Formalization Note** The rank is Mathlib's `Matrix.rank` over `ZMod 2` of the submatrix of `G.adjMatrix (ZMod 2)` with rows the elements of $X$ and columns the elements of $Y$, cast to $\mathbb{Z}$. The formula is defined for every pair; the paper uses it only for disjoint pairs and every statement of the mission restricts to those. The page writes $\mathrm{cutrk}^*_G(A, B)$ on the left of the definition, a misprint for $\mathrm{cutrk}^*_G(X, Y)$.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 522, Section 6 (M[X,Y], A(G) over GF(2)) and Definition 6.1

import Mathlib

namespace ApproxCliqueWidth.Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oum–Seymour Definition 6.1 (p. 522): `cutrk*_G(X, Y) = rk(A(G)[X, Y])`, the rank over
`GF(2)` of the submatrix of the adjacency matrix of `G` with rows `X` and columns `Y`.
The paper defines it for disjoint `X, Y`; the formula makes sense for all pairs. -/
noncomputable def cutrkStar (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℤ :=
  (((G.adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V)) (fun y : Y => (y : V))).rank : ℤ)

/-- Oum–Seymour Definition 6.1 (p. 522): the cut-rank function
`cutrk_G(X) = cutrk*_G(X, V(G) \ X)`. -/
noncomputable def cutrk (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : ℤ :=
  cutrkStar G X Xᶜ

end ApproxCliqueWidth.Certificate


