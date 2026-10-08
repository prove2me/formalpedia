-- Prove2me | Definitions.Def_DiaconisStroock_Poincare_Paths
-- name    : DiaconisStroock_Poincare_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:52.303399+00:00
-- url     : https://prove2.me/theorems/34db85e8-0728-46a6-8b3b-e5a3468285c0
-- title:
--   §1B, p. 37 — walks, edge-simple paths, and Q-weighted path length
-- statement:
--   For a finite reversible Markov chain with transition matrix $P$ and stationary distribution $\pi$, let $Q(z,w)=\pi(z)P(z,w)$. A walk from $x$ to $y$ is a finite vertex sequence starting at $x$, ending at $y$, and traversing only steps with $Q(z,w)>0$. A **path** is such a walk in which no unordered edge occurs twice; vertices may repeat. Its weighted length is
--
--   $$
--   |\gamma|_Q=\sum_{(z,w)\text{ traversed by }\gamma}\frac{1}{Q(z,w)}.
--   $$
--
--   These definitions encode the paths and the length in §1B and (1.4), and supply the shared vocabulary for the paper's path bounds.
--
--   **Formalization Note** A path is stored as a vertex list. The list of traversed steps is directed, while the no-repeated-edge condition identifies $(z,w)$ with $(w,z)$. Length counts each traversal in the list.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 37, §1B and (1.4), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_lower

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- The directed edges `(v₀, v₁), (v₁, v₂), …, (v_{k-1}, v_k)` traversed by the path whose vertex
list is `[v₀, v₁, …, v_k]` (Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains,
Ann. Appl. Probab. 1 (1991), §1B, p. 37 = PDF 2). A path with `k` edges has `k + 1` vertices. -/
def pathEdges {V : Type*} (p : List V) : List (V × V) :=
  p.zip p.tail

/-- `p` is a walk from `x` to `y` in the graph of the chain `(P, π)`: its vertex list starts at `x`,
ends at `y`, and every step `(z, w)` is an edge of the graph, `Q(z, w) = π(z) P(z, w) > 0`
(§1B, p. 37: "a graph with vertex set X and {x, y} an edge iff Q(x, y) > 0"; a step `(z, z)` is a
self-loop, an edge when `Q(z, z) > 0`, §1C, p. 40). -/
def IsWalk {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ) (x y : V)
    (p : List V) : Prop :=
  p.head? = some x ∧ p.getLast? = some y ∧ ∀ e ∈ pathEdges p, 0 < edgeMeasure P π e.1 e.2

/-- `p` is a path from `x` to `y` in the sense of §1B (p. 37): a walk in which no edge occurs twice.
"Paths may have repeated vertices but a given edge appears at most once in a given path"; the edge
traversed by a step `(z, w)` is the unordered pair `{z, w}`. -/
def IsPath {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ) (x y : V)
    (p : List V) : Prop :=
  IsWalk P π x y p ∧ ((pathEdges p).map Sym2.mk).Nodup

/-- The path length (1.4), p. 37: `|γ|_Q = ∑_{e ∈ γ} Q(e)⁻¹`, summed over the edges of the path. -/
noncomputable def qLength {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (p : List V) : ℝ :=
  ((pathEdges p).map fun e => (edgeMeasure P π e.1 e.2)⁻¹).sum

end DiaconisStroock.Poincare


