-- Prove2me | Definitions.Def_TSPSDPGap_simplicialCost
-- name    : TSPSDPGap_simplicialCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:15.239982+00:00
-- url     : https://prove2.me/theorems/c7c8e34b-9ce6-48e3-bedc-6e4c0c20af09
-- title:
--   Simplicial TSP instance $D=(J_g-I_g)\otimes J_{n/g}$
-- statement:
--   Split $n$ cities into $g$ groups of $n/g$ consecutive cities. The **simplicial instance** has cost $0$ between two cities of the same group and cost $1$ between cities of different groups. With the $i$-th group consisting of the cities $(i-1)n/g+1,\dots,in/g$, its cost matrix is
--   $$
--   D=(J_g-I_g)\otimes J_{n/g}.
--   $$
--   These instances are metric; they place each group at a vertex of a regular $(g-1)$-simplex with unit edges.
--
--   **Formalization Note** Cities are `Fin n` (0-based); city $p$ lies in group $\lfloor p/(n/g)\rfloor$. For $g\mid n$ the matrix equals $(J_g-I_g)\otimes J_{n/g}$ reindexed by $\mathtt{Fin}\ g\times\mathtt{Fin}\ (n/g)\simeq\mathtt{Fin}\ n$ (proved in `Solutions/verification`).
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §4.1, p.14

import Mathlib

namespace TSPSDPGap

/-- **The simplicial TSP instance `D = (J_g − I_g) ⊗ J_{n/g}` on `n` cities.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §4.1, p.14: "we consider an instance with g equally sized groups of n/g
vertices. If u, v are two vertices in the same group, then the cost of traveling between u and v
is zero; otherwise the cost is 1. Labeling the vertices so that the ith group consists of
vertices {(i − 1)n/g + 1, ..., in/g}, the cost matrix is D = (J_g − I_g) ⊗ J_{n/g}."

The cost between cities `p` and `q` is `0` if they lie in the same group and `1` otherwise.

**Formalization Note.** Cities are `Fin n` (0-based); city `p` lies in group `⌊p / (n/g)⌋`
(natural-number division), which is the printed labelling shifted to 0-based indices. When
`g ∣ n` this matrix is `(J_g − I_g) ⊗ J_{n/g}` reindexed by `Fin g × Fin (n/g) ≃ Fin n`
(proved in `Solutions/verification/TSPSDPGap_sanity.lean`). -/
def simplicialCost (g n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if (p : ℕ) / (n / g) = (q : ℕ) / (n / g) then 0 else 1

end TSPSDPGap


