-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
-- name    : CrossLearnCB_UCB1CL_Supplement_AcyclicNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:47:44.906646+00:00
-- url     : https://prove2.me/theorems/2ff51a99-527c-48df-8ee5-92765e397f39
-- title:
--   Definition 3, p. 13 — maximum acyclic subgraph number λ(G) and its average λ̄ over the CL graphs
-- statement:
--   Let $G$ be a directed graph on a finite vertex set $V$; write $u \to v$ for an edge. An **acyclic subgraph** of $G$ is a set of vertices that can be listed as $v_1, v_2, \dots, v_r$ (distinct) so that there is no edge $v_i \to v_j$ whenever $i > j$. The **maximum acyclic subgraph number** is
--
--   $$\lambda(G) = \max\{\, r : \text{some } r \text{ distinct vertices form an acyclic subgraph} \,\}.$$
--
--   Self-loops play no role, because only pairs with $i > j$ are constrained. For cross-learning graphs $G_1, \dots, G_K$ on the contexts $[C]$ (one per arm), the average is
--
--   $$\bar\lambda = \frac1K \sum_{i=1}^K \lambda(G_i).$$
--
--   For complete cross-learning $\lambda(G) = 1$, and with no cross-learning $\lambda(G) = C$. The quantity $\lambda$ governs the regret of EXP3.CL and EXP3.CL-U.
--
--   **Formalization Note** A graph is a relation `H : V → V → Prop` on a finite type, `H u v` meaning $u \to v$; the CL graphs use the encoding of the published `CrossLearnCB.UCB1CL.Model` (`G i c c'` is the edge $c \to c'$ of $G_i$). An acyclic subgraph of size $r$ is an injective map `Fin r → V` with no edge from a later to an earlier vertex; $\lambda$ is the supremum of the admissible sizes, a set that contains $0$ and is bounded by $|V|$, so it is a maximum.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 13, Definition 3; p. 21, definition of λ̄

import Mathlib

namespace CrossLearnCB.UCB1CL.Supplement

/-! ### Definition 3 (p. 13): the maximum acyclic subgraph number

A directed graph on a finite vertex type `V` is a relation `H : V → V → Prop`; `H u v` is the
edge `u → v`. -/

/-- Maximum acyclic subgraph number `λ(H)` (Definition 3): the largest `r` such that some
`r` distinct vertices `v 0, …, v (r-1)` admit no edge `v i → v j` whenever `j < i`.
The set of such `r` contains `0` and is bounded by the number of vertices, so the supremum is
its maximum. -/
noncomputable def maxAcyclicNumber {V : Type*} [Fintype V] (H : V → V → Prop) : ℕ :=
  sSup {r : ℕ | ∃ v : Fin r → V, Function.Injective v ∧ ∀ i j : Fin r, j < i → ¬ H (v i) (v j)}

/-- The average `λ̄ = (1/K) Σ_i λ(G_i)` of the maximum acyclic subgraph numbers of the
cross-learning graphs `G i` (`G i c c'` is the edge `c → c'` of `G_i`). -/
noncomputable def lambdaBar {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) : ℝ :=
  (1 / (K : ℝ)) * ∑ i, (maxAcyclicNumber (G i) : ℝ)

end CrossLearnCB.UCB1CL.Supplement


