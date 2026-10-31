-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_SpanningTreeLPFeasible
-- name    : CombOpt_SpanningTree_Graph_SpanningTreeLPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:49.087979+00:00
-- url     : https://prove2.me/theorems/290b9641-06eb-415f-9896-9ec5f1a9bdda
-- title:
--   Feasible solution of the spanning-tree LP (2.2)–(2.4)
-- statement:
--   For $x\in\mathbb R^E$ and $B\subseteq E$ write $x(B)=\sum_{e\in B}x_e$. The vector $x$ is a **feasible solution** of the linear program (2.1) if
--
--   $$x(\gamma(S))\le |S|-1\quad\text{for all } S,\ \emptyset\ne S\subseteq V, \tag{2.2}$$
--   $$x(E)=|V|-1, \tag{2.3}$$
--   $$x_e\ge 0\quad\text{for all } e\in E. \tag{2.4}$$
--
--   **Formalization Note** The book prints (2.2) with $\emptyset\ne S\subset V$; it writes $\subset$ also in (2.6), whose proof says "Let $A\subseteq E$". The constraint for $S=V$ reads $x(E)\le|V|-1$ and is implied by (2.3), so the feasible set is the same either way; here (2.2) is imposed for every nonempty $S\subseteq V$. Right-hand sides are real numbers.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 16 (PDF p. 25), constraints (2.2)–(2.4)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_gamma

namespace CombOpt.SpanningTree

/-- **A feasible solution of the spanning-tree linear program (2.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 16 (PDF p. 25), constraints (2.2)–(2.4):
"x(γ(S)) ≤ |S| − 1, for all S, ∅ ≠ S ⊂ V (2.2); x(E) = |V| − 1 (2.3); x_e ≥ 0, for all e ∈ E (2.4)",
where "p(B) [means] Σ(p_j : j ∈ B)".

`G.SpanningTreeLPFeasible x` holds for `x : E → ℝ` when
1. `∑_{e ∈ γ(S)} x e ≤ |S| − 1` for every nonempty node set `S`;
2. `∑_{e ∈ E} x e = |V| − 1`;
3. `x e ≥ 0` for every edge `e`.

**Formalization Note.** (2.2) is imposed for every nonempty `S ⊆ V`, `S = V` included: the book
writes `⊂` also in (2.6), whose proof says "Let A ⊆ E", and in any case the constraint for
`S = V` is `x(E) ≤ |V| − 1`, implied by (2.3), so the feasible set is the same under either
reading. The right-hand sides are real numbers (no natural-number subtraction). -/
def Graph.SpanningTreeLPFeasible {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E)
    (x : E → ℝ) : Prop :=
  (∀ S : Finset V, S.Nonempty → ∑ e ∈ G.gamma S, x e ≤ (S.card : ℝ) - 1) ∧
    ∑ e, x e = (Fintype.card V : ℝ) - 1 ∧
    ∀ e, 0 ≤ x e

end CombOpt.SpanningTree


