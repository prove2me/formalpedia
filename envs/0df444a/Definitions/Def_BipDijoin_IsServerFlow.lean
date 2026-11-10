-- Prove2me | Definitions.Def_BipDijoin_IsServerFlow
-- name    : BipDijoin_IsServerFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:24.570838+00:00
-- url     : https://prove2.me/theorems/4b93c7d9-d733-40f4-b48d-0de3c183abf6
-- title:
--   Balanced server flows, loads and the threshold potential $\Phi_\eta$
-- statement:
--   Let $G=(L\cup R,E)$ be a bipartite multigraph, the left vertices being clients and the right vertices servers. A **server flow** assigns a value $x_e\ge 0$ to every edge so that every client $\ell\in L$ sends exactly one unit: $\sum_{e:\,\ell(e)=\ell}x_e=1$. The **load** of a server $r$ is $\alpha(r)=\sum_{e:\,r(e)=r}x_e$. The flow is **balanced** if every client sends flow only to neighbours of minimum load.
--
--   For $\eta\in[0,1]$ the **threshold potential** of the flow is
--   $$\Phi_\eta=\sum_{r\in R}\big(\alpha(r)-\eta\big)_+,\qquad (t)_+=\max\{t,0\}.$$
--   The module also defines $N_G(X)$, the set of servers adjacent to a set $X$ of clients.
--
--   **Formalization Note** The paper writes $\Phi_\eta(G)$ as a function of $G$, relying on the uniqueness of the load vector of a balanced flow [BHR19]. That uniqueness is cited, not proved, so the potential is attached to a given flow and the lemmas quantify over all balanced flows.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §6.3.1–6.3.2, p.29 (PDF p.31) and p.30 (PDF p.32)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph

set_option autoImplicit false

namespace BipDijoin

/-!
# Balanced server flows and the threshold potential

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §6.3.1, p.29
(PDF p.31): "For a bipartite graph G = (L ∪ R, E), a server flow consists of nonnegative values
x_ℓr such that Σ_{r∈N(ℓ)} x_ℓr = 1 for every ℓ ∈ L. The load of a server r ∈ R is
α_G(r) := Σ_{ℓ∈N(r)} x_ℓr. A server flow is balanced if every ℓ ∈ L sends flow only to neighbors of
minimum load." §6.3.2, p.30 (PDF p.32): "Fix η ∈ [0, 1] and define
Φ_η(G) := Σ_{r∈R} (α_G(r) − η)₊, where (x)₊ := max{x, 0}."

**Formalization Note.**
* A flow is a real value on each edge identity (parallel edges carry separate values); only the
  values on `E` matter.
* `Phi G η x` is the potential of the given flow `x`. The paper's `Φ_η(G)` is a function of `G`
  because the load vector of a balanced flow is unique [BHR19]; that uniqueness is cited, not
  proved, so the potential is defined per flow and every statement quantifies over all balanced
  flows.
* `nbr G X` is `N_G(X)`, the set of right vertices adjacent to `X`.
-/

namespace BipGraph

variable (G : BipGraph)

/-- `N_G(X)`: the right ends of the edges with left end in `X`. -/
def nbr (X : Finset ℕ) : Finset ℕ := (G.E.filter (fun e => G.tl e ∈ X)).image G.hd

/-- A **server flow**: nonnegative values on the edges, each left vertex sending exactly one unit. -/
def IsServerFlow (x : ℕ → ℝ) : Prop :=
  (∀ e ∈ G.E, 0 ≤ x e) ∧ ∀ ℓ ∈ G.left, ∑ e ∈ G.E.filter (fun e => G.tl e = ℓ), x e = 1

/-- The **load** `α_G(r)` of the right vertex `r`. -/
def load (x : ℕ → ℝ) (r : ℕ) : ℝ := ∑ e ∈ G.E.filter (fun e => G.hd e = r), x e

/-- A **balanced** server flow: an edge carries positive flow only if its right end has minimum
load among the right ends of the edges at its left end. -/
def IsBalancedServerFlow (x : ℕ → ℝ) : Prop :=
  G.IsServerFlow x ∧ ∀ e ∈ G.E, 0 < x e → ∀ e' ∈ G.E, G.tl e' = G.tl e →
    G.load x (G.hd e) ≤ G.load x (G.hd e')

/-- The **threshold potential** `Φ_η = Σ_{r ∈ R} (α(r) − η)₊` of the flow `x`. -/
def Phi (η : ℝ) (x : ℕ → ℝ) : ℝ := ∑ r ∈ G.right, max (G.load x r - η) 0

end BipGraph

end BipDijoin


