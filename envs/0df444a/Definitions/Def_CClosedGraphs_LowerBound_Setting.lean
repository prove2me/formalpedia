-- Prove2me | Definitions.Def_CClosedGraphs_LowerBound_Setting
-- name    : CClosedGraphs_LowerBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:33.517062+00:00
-- url     : https://prove2.me/theorems/17aa89b1-f69c-44b6-ad7d-84711f536836
-- title:
--   §4, p. 12 — the clique blow-up of a graph
-- statement:
--   Given a simple graph $H$ and $h \in \mathbb N$, its blow-up $H^{(h)}$ has vertex set $V(H) \times \{0, \dots, h-1\}$; write $U_x = \{x\} \times \{0,\dots,h-1\}$. Two vertices are adjacent by the rule
--   $$
--   (x, i) \sim (y, j) \iff i \neq j \ \text{ and } \ \bigl(x = y \ \text{ or } \ xy \in E(H)\bigr).
--   $$
--   So each $U_x$ is a clique of size $h$; for every edge $xy$ of $H$ the bipartite graph between $U_x$ and $U_y$ is the complete bipartite graph $K_{h,h}$ minus the perfect matching $\{(x,i),(y,i)\}$; and for distinct non-adjacent $x, y$ there are no edges between $U_x$ and $U_y$.
--
--   The paper takes $h = c/2$ and $H$ a graph of girth at least $5$ with many edges, and shows that the blow-up is $c$-closed with many maximal cliques. The mission uses the frozen shared definitions of $c$-closed graphs and maximal-clique counts from `CClosedGraphs.Peeling.Setting`.
--
--   **Formalization Note** The paper says "a perfect matching" without fixing one; the blow-up fixes the matching $(x,i) \leftrightarrow (y,i)$ for every edge, which is one admissible instance of the paper's construction.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 12, §4, Construction

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

namespace CClosedGraphs.LowerBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in

/-- The blow-up of §4 (p. 12): vertex `x` of `H` becomes `U_x = {x} × Fin h`, and
`(x, i) ~ (y, j)` iff `i ≠ j` and (`x = y` or `x ~ y` in `H`). So each `U_x` is a clique, the
bipartite graph between `U_x` and `U_y` is `K_{h,h}` minus the perfect matching
`{(x, i), (y, i)}` when `x ~ y`, and there are no edges between `U_x` and `U_y` otherwise. -/
def blowUp {W : Type*} (H : SimpleGraph W) (h : ℕ) : SimpleGraph (W × Fin h) where
  Adj p q := p.2 ≠ q.2 ∧ (p.1 = q.1 ∨ H.Adj p.1 q.1)
  symm := ⟨fun _ _ hpq => ⟨hpq.1.symm, hpq.2.imp Eq.symm (fun a => a.symm)⟩⟩
  loopless := ⟨fun _ hp => hp.1 rfl⟩

end CClosedGraphs.LowerBound


