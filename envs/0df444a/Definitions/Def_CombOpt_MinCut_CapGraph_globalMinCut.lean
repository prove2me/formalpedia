-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_globalMinCut
-- name    : CombOpt_MinCut_CapGraph_globalMinCut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:56.038917+00:00
-- url     : https://prove2.me/theorems/03242b81-b174-40a1-ab10-3c2abc5bcbf5
-- title:
--   $\lambda(G)$, the capacity of a minimum cut
-- statement:
--   For a finite capacitated graph $G=(V,E)$, the **minimum cut problem** asks for $S\subseteq V$ with $\emptyset\ne S\ne V$ minimizing $u(\delta(S))$; $\lambda(G)$ is its optimal value:
--
--   $$\lambda(G)=\min\{u(\delta(S)) : \emptyset\ne S\subsetneq V\}.$$
--
--   **Formalization Note** The value lies in $\mathbb R\cup\{+\infty\}$ (`WithTop ℝ`) with $\min\emptyset=+\infty$. A graph with at most one node has no such $S$, and its value is $+\infty$ (the book's algorithm on p. 75 likewise starts from $M=\infty$). With at least two nodes it is the book's real number.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5, pp. 72–73 (PDF pp. 81–82)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum
import Definitions.Def_CombOpt_MinCut_CapGraph_delta

namespace CombOpt.MinCut

open Classical in
/-- **`λ(G)`, the capacity of a minimum cut.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5,
pp. 72–73 (PDF pp. 81–82): "We want to find a set S ⊆ V with ∅ ≠ S ≠ V such that u(δ(S)) is
minimized. In this section we use minimum cut to mean an optimal solution to this problem. …
introduce the notation λ(G) for the capacity of a minimum cut of G".

`G.globalMinCut` is the minimum of `u(δ(S))` over all `S ⊆ V` with `∅ ≠ S ≠ V`.

**Formalization Note.** The value lies in `WithTop ℝ`; a graph with at most one node has no such
`S`, and then the value is `⊤` (`min ∅ = +∞`; compare the algorithm on p. 75, which initializes
`M` to `∞`). With two or more nodes it is the book's real number. -/
noncomputable def CapGraph.globalMinCut {V E : Type*} [Fintype V] [Fintype E]
    (G : CapGraph V E) : WithTop ℝ :=
  (Finset.univ.filter (fun S : Finset V => S.Nonempty ∧ S ≠ Finset.univ)).inf
    (fun S => ((G.uSum (G.delta S) : ℝ) : WithTop ℝ))

end CombOpt.MinCut


