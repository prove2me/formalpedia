-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_minCutValue
-- name    : CombOpt_MinCut_CapGraph_minCutValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:55.577314+00:00
-- url     : https://prove2.me/theorems/0d1ad45f-9bf3-4c08-9ebe-21a0051c7380
-- title:
--   $\lambda(G;v,w)$, the capacity of a minimum $(v,w)$-cut
-- statement:
--   For a finite capacitated graph $G=(V,E)$ and nodes $v,w$, $\lambda(G;v,w)$ is the capacity of a minimum $(v,w)$-cut:
--
--   $$\lambda(G;v,w)=\min\{u(\delta(S)) : S\subseteq V,\ \text{exactly one of } v,w \text{ is in } S\}.$$
--
--   This is the quantity compared in Lemma 3.37, in the node-identification identity and in Theorem 3.36.
--
--   **Formalization Note** The value lies in $\mathbb R\cup\{+\infty\}$ (`WithTop ℝ`) with $\min\emptyset=+\infty$: for $v\ne w$ the minimum is over a nonempty finite family and is the book's real number; for $v=w$ no set separates the nodes and the value is $+\infty$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5, pp. 72–73 (PDF pp. 81–82)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum
import Definitions.Def_CombOpt_MinCut_CapGraph_delta
import Definitions.Def_CombOpt_MinCut_Separates

namespace CombOpt.MinCut

open Classical in
/-- **`λ(G; v, w)`, the capacity of a minimum `(v, w)`-cut.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5,
pp. 72–73 (PDF pp. 81–82): "λ(G; v, w) for the capacity of a minimum (v, w)-cut of G", where δ(S)
is a (v, w)-cut if exactly one of v, w is in S.

`G.minCutValue v w` is the minimum of `u(δ(S))` over all `S ⊆ V` separating `v` from `w`.

**Formalization Note.** The value lies in `WithTop ℝ` and is the infimum of a finite family, so
it is attained whenever some `S` separates `v` and `w`, i.e. whenever `v ≠ w`; for `v = w` no set
separates them and the value is `⊤` (`min ∅ = +∞`). For distinct nodes it is the book's real
number. -/
noncomputable def CapGraph.minCutValue {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E)
    (v w : V) : WithTop ℝ :=
  (Finset.univ.filter (fun S : Finset V => Separates S v w)).inf
    (fun S => ((G.uSum (G.delta S) : ℝ) : WithTop ℝ))

end CombOpt.MinCut


