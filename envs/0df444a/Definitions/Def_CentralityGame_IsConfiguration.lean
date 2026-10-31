-- Prove2me | Definitions.Def_CentralityGame_IsConfiguration
-- name    : CentralityGame_IsConfiguration
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:32.177789+00:00
-- url     : https://prove2.me/theorems/80dae0b2-50b1-4b0c-8d47-c33248bd13a6
-- title:
--   Configuration $x\in\mathcal X$
-- statement:
--   A **configuration** is a tuple $x=(x_1,\dots,x_n)$ in $\mathcal X=\prod_{i\in\mathcal V}\mathcal A_i$. It determines the graph $\mathcal G(x)=(\mathcal V,\mathcal E(x))$ with link set $\mathcal E(x)=\{(i,j)\mid i\in\mathcal V,\ j\in x_i\}$.
--
--   **Formalization Note** $\mathcal G(x)$ is the graph with out-neighbourhoods $\mathcal N_i=x_i$, so a configuration is used directly wherever an out-neighbourhood map is expected.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §3, p.8

import Mathlib
import Definitions.Def_CentralityGame_IsAction

namespace CentralityGame

/-- A **configuration** `x = (x_1, …, x_n) ∈ X = ∏_{i ∈ V} A_i` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §3, p.8).

**Formalization Note** The graph `G(x)`, with link set `{(i, j) | i ∈ V, j ∈ x_i}`, is the graph
with out-neighbourhoods `N = x`. Every notion on `G(x)` is the notion on `x` read as `N`. -/
def IsConfiguration {V : Type*} (d : V → ℕ) (x : V → Finset V) : Prop :=
  ∀ k, IsAction d k (x k)

end CentralityGame


