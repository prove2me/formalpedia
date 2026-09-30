-- Prove2me | Definitions.Def_HeldKarp_Ascent_oneTreeBound
-- name    : HeldKarp_Ascent_oneTreeBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:03:16.324988+00:00
-- url     : https://prove2.me/theorems/096c9286-e675-4417-8fe0-72652672d84e
-- title:
--   The Held–Karp 1-tree bound $w(\pi) = \min_k [c_k + \pi \cdot v_k]$ and the polyhedron $P_{\bar w}$
-- statement:
--   Let $(c_{ij})$ be a symmetric real $n \times n$ matrix of edge weights on $K_n$ (no sign, metric or diagonal condition). The **weight** $c(G)$ of a subgraph $G$ is the sum of the weights of its edges. For a graph $G$ let $v_G \in \mathbb R^n$ be its **degree-excess vector**, $(v_G)_i = \deg_G(i) - 2$. For a real $n$-vector $\pi$ define the **Lagrangian weight**
--   $$L(\pi, G) = c(G) + \pi \cdot v_G = c(G) + \sum_{i=1}^n \pi_i\,(\deg_G(i) - 2).$$
--   Indexing the 1-trees by $k$, with $c_k$ the weight and $v_k$ the degree-excess vector of the $k$-th 1-tree, the **1-tree bound** is
--   $$w(\pi) = \min_k \,[c_k + \pi \cdot v_k].$$
--   A 1-tree $G$ is a **minimum-weight 1-tree at the point $\pi$** if it minimizes $c_k + \pi\cdot v_k$ over all 1-trees (equivalently, it has least weight for the transformed weights $c_{ij} + \pi_i + \pi_j$); the paper writes $k(\pi)$ for the index of such a 1-tree. For a target value $\bar w$, the polyhedron
--   $$P_{\bar w} = \{\pi \in \mathbb R^n : \bar w \le c_k + \pi \cdot v_k \text{ for all } k\}$$
--   is the feasible set of the system (5). Finally, for sets $X, Y$ of edges, $T(X,Y)$ is the set of 1-trees containing every edge of $X$ and no edge of $Y$, and $w_{X,Y}(\pi) = \min_{k \in T(X,Y)} [c_k + \pi \cdot v_k]$.
--
--   The function $w$ is the minimum of finitely many affine functions of $\pi$, hence concave and piecewise linear; $\max_\pi w(\pi)$ is the Held–Karp lower bound on the weight of an optimum tour, and the ascent method of the paper approximates it.
--
--   **Formalization Note** Weights are `c : Sym2 (Fin n) → ℝ` on unordered pairs. The inner product is the Euclidean one, written as a sum. `oneTreeBound` is an `sInf` over the finite set of 1-tree values; it is a genuine minimum for $n \ge 3$ and the junk value $0$ for $n \le 2$, where no 1-tree exists (every theorem assumes $3 \le n$). Likewise `restrictedBound` is $0$ when $T(X,Y)$ is empty; it is only used for pairs $(X,Y)$ that admit a tour.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, p. 7 (PDF p. 2) weights; p. 8 (PDF p. 3) w(π), v_k; p. 9 (PDF p. 4) k(π); p. 10 (PDF p. 5) Eq. (5) and P_w̄; p. 14 (PDF p. 9) T(X,Y), w_{X,Y}

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree

open Classical

namespace HeldKarp.Ascent

/-- **Weight of a subgraph** (Held & Karp, *The traveling-salesman problem and minimum spanning
trees: Part II*, Math. Programming 1 (1971), §1, p. 7 (PDF p. 2)): "Each subgraph of K_n is
assigned a weight equal to the sum of the weights of its edges."

Formalization Note: the symmetric weight matrix `(c_ij)` is a function `c : Sym2 (Fin n) → ℝ` on
unordered pairs, so symmetry is built in. The weights are arbitrary reals (no sign, metric or
diagonal condition); loops never occur in a simple graph, so the diagonal is irrelevant. -/
noncomputable def weight {n : ℕ} (c : Sym2 (Fin n) → ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ G.edgeFinset, c e

/-- **The degree-excess vector `v_k`** (Held & Karp 1971, §1, p. 8 (PDF p. 3)): "v_k is the
n-vector having d_ik − 2 as its i-th component", where `d_ik` is the degree of vertex `i` in the
1-tree `k`. Here it is defined for every graph `G`: `degExcess G i = deg_G(i) − 2`. -/
noncomputable def degExcess {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → ℝ :=
  fun i => (G.degree i : ℝ) - 2

/-- **The Lagrangian weight `c_k + π · v_k`** (Held & Karp 1971, §1, p. 8 (PDF p. 3)): the weight
of the graph `G` plus the inner product of the real `n`-vector `π` with the degree-excess vector of
`G`. For a 1-tree `G` this equals the weight of `G` under the transformed weights
`c_ij + π_i + π_j` minus the constant `2 Σ_i π_i` (observation (iii), p. 8). The inner product is
the Euclidean one, written out as a sum. -/
noncomputable def lagrWeight {n : ℕ} (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) : ℝ :=
  weight c G + ∑ i, π i * degExcess G i

/-- **The 1-tree bound `w(π)`** (Held & Karp 1971, §1, p. 8 (PDF p. 3)):
"w(π) = min_k [c_k + π · v_k]", the minimum over all 1-trees `k`.

Formalization Note: the set of 1-trees on `Fin n` is finite, and nonempty exactly when `n ≥ 3`,
so for `n ≥ 3` this `sInf` is an attained minimum. For `n ≤ 2` there is no 1-tree and the value is
the junk value `sInf ∅ = 0`; every theorem using `oneTreeBound` assumes `3 ≤ n`. -/
noncomputable def oneTreeBound {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ x = lagrWeight c π G}

/-- **Minimum-weight 1-tree at the point `π`** (Held & Karp 1971, §2, p. 9 (PDF p. 4)): "for any π,
k(π) is the index of a minimum-weight 1-tree at the point π". `G` is a 1-tree and minimizes
`c_k + π · v_k` over all 1-trees `k` (equivalently, it has least weight under the weights
`c_ij + π_i + π_j`). Ties are allowed: the theorems quantify over every such choice. -/
def IsMinOneTree {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) : Prop :=
  IsOneTree G ∧ ∀ G' : SimpleGraph (Fin n), IsOneTree G' → lagrWeight c π G ≤ lagrWeight c π G'

/-- **The polyhedron `P_w̄`** (Held & Karp 1971, §2, p. 10 (PDF p. 5)): "Let P_w̄ denote the
polyhedron of feasible solutions to (5)", where (5) is the system "w̄ ≤ c_k + π · v_k for all k"
(one inequality per 1-tree `k`). -/
def feasibleSet {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (wbar : ℝ) : Set (Fin n → ℝ) :=
  {π | ∀ G : SimpleGraph (Fin n), IsOneTree G → wbar ≤ lagrWeight c π G}

/-- **The restricted bound `w_{X,Y}(π)`** (Held & Karp 1971, §3, p. 14 (PDF p. 9)): "let T(X, Y)
be the set of all 1-trees which include the edges in X and exclude the edges in Y, and let
w_{X,Y}(π) = min_{k∈T(X,Y)} [c_k + π · v_k]."

Formalization Note: edges are elements of `Sym2 (Fin n)`; "include the edges in X" is
`X ⊆ G.edgeSet` and "exclude the edges in Y" is `Disjoint Y G.edgeSet`. When `T(X, Y)` is empty
the value is the junk value `sInf ∅ = 0`; the theorem using it only concerns pairs `(X, Y)` for
which a tour, hence a 1-tree, of the derived problem exists. -/
noncomputable def restrictedBound {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ)
    (X Y : Set (Sym2 (Fin n))) (π : Fin n → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ X ⊆ G.edgeSet ∧
    Disjoint Y G.edgeSet ∧ x = lagrWeight c π G}

end HeldKarp.Ascent


