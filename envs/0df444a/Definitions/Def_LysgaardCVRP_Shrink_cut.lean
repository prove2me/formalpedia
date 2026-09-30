-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_cut
-- name    : LysgaardCVRP_Shrink_cut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:21:30.433064+00:00
-- url     : https://prove2.me/theorems/7327b252-2271-40ac-9e90-81b4fabb4622
-- title:
--   Cut value $x(\delta(S))$ in the complete graph with depot
-- statement:
--   Let $G = (V, E)$ be the complete undirected graph on $V = \{0, 1, \dots, n\}$, where vertex $0$ is the depot and $1, \dots, n$ are the customers, and let $x = (x_e)_{e \in E}$ be a real vector indexed by the edges, so that $x_{ij}$ and $x_{ji}$ denote the same number. For a vertex set $S \subseteq V$, let $\delta(S)$ be the set of edges with exactly one end-vertex in $S$. The **cut value** of $S$ is
--
--   $$x(\delta(S)) = \sum_{e \in \delta(S)} x_e = \sum_{i \in S} \sum_{j \in V \setminus S} x_{ij}.$$
--
--   Cut values are the left-hand sides of the degree equations $x(\delta(\{i\})) = 2$ and of the capacity inequalities $x(\delta(S)) \ge 2r(S)$ of the two-index formulation of the capacitated vehicle routing problem. Edges to the depot are part of $\delta(S)$.
--
--   **Formalization Note** Vertices are `Fin (n+1)` with the depot `0`; the edge vector is a function on unordered pairs `Sym2 (Fin (n+1))`. Each crossing edge is counted once, from its end-vertex in $S$; diagonal pairs $\{i, i\}$ never cross a cut.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 424 (PDF p. 2), §1, definitions of δ(S) and x(F)

import Mathlib

namespace LysgaardCVRP.Shrink

/-- The cut value $x(\delta(S))$ of Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm
for the capacitated vehicle routing problem*, Math. Program. Ser. A 100 (2004), §1, p. 424
(PDF p. 2): for a vertex set $S$, $\delta(S)$ is the set of edges of the complete graph
$G = (V, E)$, $V = \{0, \dots, n\}$, with exactly one end-vertex in $S$, and
$x(F) = \sum_{e \in F} x_e$.

**Formalization Note.** Vertices are `Fin (n+1)`, the depot is `0`. The edge vector is a function
on unordered pairs `Sym2 (Fin (n+1))`, so $x_{ij}$ and $x_{ji}$ are the same variable, as in the
paper. Each edge $\{i, j\}$ of $\delta(S)$ is counted exactly once, from its end-vertex $i \in S$;
diagonal pairs `s(i, i)` never have exactly one end-vertex in $S$ and never contribute. Edges to
the depot are included (the cut is taken in $G$, not in the customer graph). -/
def cut {n : ℕ} (x : Sym2 (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1))) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, x s(i, j)

end LysgaardCVRP.Shrink


