-- Prove2me | Definitions.Def_EvenCycleTuran_PathCount_Setting
-- name    : EvenCycleTuran_PathCount_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:56.065909+00:00
-- url     : https://prove2.me/theorems/09496e00-36c9-49ab-b0a8-b6ab90091cb3
-- title:
--   Cycle-free graphs, generalized Turán numbers, balanced bipartite graphs and spectral radius
-- statement:
--   For a set $A$ of natural numbers, a graph $G$ is $\mathcal C_A$-free when it contains no cycle $C_a$ with $a\in A$. The generalized Turán number is
--
--   $$
--   \operatorname{ex}(n,H,\mathcal C_A)
--     =\max\{\mathcal N(H,G): |V(G)|=n,\ G\text{ is }\mathcal C_A\text{-free}\},
--   $$
--
--   where $\mathcal N(H,G)$ counts unlabelled copies of $H$ as subgraphs of $G$. The setting also defines $B_{n,a}=K_{a,n-a}$ by the partition of vertices $0,\ldots,n-1$ at $a$, and $\mu(G)$ as the largest absolute eigenvalue of the real adjacency matrix of $G$.
--
--   These objects support the path-count statements and can be reused in other cycle-free extremal problems.
--
--   **Formalization Note** The extremal maximum is represented by a supremum in $\mathbb N$; for the odd-cycle family used here it is attained, since the empty graph is feasible and there are finitely many graphs on $n$ vertices. For $a\le n$, the bipartite parts have sizes $a$ and $n-a$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, pp. 2–3, §1.1; p. 29, §7.1; p. 32, §7.2

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting

namespace EvenCycleTuran.PathCount

/-- The complete bipartite graph with parts `Finset.Iio a` and `Finset.Ici a`.
When `a ≤ n`, the parts have sizes `a` and `n - a`. -/
def bipGraph (n a : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val < a ∧ a ≤ v.val) ∨ (v.val < a ∧ a ≤ u.val)
  symm := by
    constructor
    intro u v h
    exact h.elim Or.inr Or.inl
  loopless := by
    constructor
    intro u h
    rcases h with h | h <;> omega

/-- The spectral radius of the real adjacency matrix, using its finite set of
real eigenvalues. The empty graph on an empty vertex type has radius zero. -/
noncomputable def specRad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := by
  classical
  exact ⨆ i, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|

end EvenCycleTuran.PathCount


