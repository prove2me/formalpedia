-- Prove2me | Definitions.Def_QGraphColl_gc
-- name    : QGraphColl_gc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:12.638214+00:00
-- url     : https://prove2.me/theorems/9c07ca7a-9edb-4f37-a433-5e7d7bc45627
-- title:
--   Graph collision: neighbourhoods $N_G(v)$, degrees, marked set $M$ and $\mathrm{gc}_G(x)$
-- statement:
--   Let $G=(V,E)$ be a simple undirected graph on a finite vertex set $V$, known in advance, and let $x\in\{0,1\}^V$ be an input. A vertex $v$ is **marked** if $x_v=1$, and
--   $$M=\{v\in V:\ x_v=1\}$$
--   is the set of marked vertices. $N_G(v)$ is the set of neighbours of $v$, $\deg_G(v)=|N_G(v)|$ its degree, and $|E(G)|$ the number of edges.
--
--   The **graph collision** function of $G$ is
--   $$\mathrm{gc}_G(x)=\bigvee_{uv\in E(G)}(x_u\wedge x_v),$$
--   which is $1$ exactly when some edge has both endpoints marked. An input is **positive** if $\mathrm{gc}_G(x)=1$ and **negative** otherwise; on a negative input $M$ is an independent set.
--
--   These are the objects of every statement of the mission: the graph is free information, and only queries to the bits $x_v$ are counted.
--
--   **Formalization Note.** The graph is Mathlib's `SimpleGraph V` on a finite type `V`, an input is `x : V → Bool`. `nbr G v`, `deg G v` and `numEdges G` decide adjacency classically, so statements may use edge deletion `G \ H`, suprema of graphs and induced graphs on the same labels without decidability instances. `gc G x : Bool`, and the lemma `gc_eq_true_iff` unfolds it.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), §1 p.3 (graph collision problem); §2 'Graph collision', p.12 (M, N_G(v), positive/negative inputs); §6 p.32 (gc_G(y) = ⋁_{uv∈E(G)} (y_u ∧ y_v))

import Mathlib

namespace QGraphColl

/-!
# Graph collision: neighbourhoods, degrees, marked vertices and the function `gc_G`

A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…),
§1, p.3 (the graph collision problem); §2 "Graph collision", p.12 (marked set `M`, `N_G(v)`,
positive and negative inputs); §6, p.32 (`gc_G(y) = ⋁_{uv ∈ E(G)} (y_u ∧ y_v)`).

**Formalization Note.**
* A simple undirected graph is Mathlib's `SimpleGraph V` on a finite vertex type `V`; an input is
  `x : V → Bool`, and `v` is marked when `x v = true`.
* `nbr G v` is `N_G(v)` as a `Finset`, `deg G v = |N_G(v)|` is `deg_G(v)`, and `numEdges G = |E(G)|`.
  They decide adjacency classically, so no `DecidableRel G.Adj` instance is needed; this lets the
  statements use edge deletion `G \ H`, suprema of graphs and `restrict` freely.
* `gc G x = true` exactly when some edge `uv` of `G` has both endpoints marked (a *positive* input);
  `gc G x = false` is a *negative* input.
-/

variable {V : Type*} [Fintype V]

/-- §2, p.12: the neighbourhood `N_G(v)` of `v` in `G`, as a finite set. -/
noncomputable def nbr (G : SimpleGraph V) (v : V) : Finset V := by
  classical exact Finset.univ.filter fun w => G.Adj v w

/-- Definition 2.1, p.12: the degree `deg_G(v) = |N_G(v)|`. -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ :=
  (nbr G v).card

/-- §4.2, p.23 ("a bipartite graph `G` with `m` edges"), Lemma 4.5, p.25 (`m = |E(G)|`): the number
of edges of `G`. -/
noncomputable def numEdges (G : SimpleGraph V) : ℕ := by
  classical exact G.edgeFinset.card

/-- §2, p.12: the set `M = {v : x_v = 1}` of marked vertices of the input `x`. -/
def marked (x : V → Bool) : Finset V :=
  Finset.univ.filter fun v => x v = true

/-- §1, p.3 and §6, p.32: the graph collision function `gc_G(x) = ⋁_{uv ∈ E(G)} (x_u ∧ x_v)`; it is
`true` exactly when some edge of `G` has both endpoints marked. -/
noncomputable def gc (G : SimpleGraph V) (x : V → Bool) : Bool := by
  classical exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

theorem gc_eq_true_iff (G : SimpleGraph V) (x : V → Bool) :
    gc G x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold gc
  simp

theorem mem_nbr {G : SimpleGraph V} {v w : V} : w ∈ nbr G v ↔ G.Adj v w := by
  unfold nbr
  simp

theorem mem_marked {x : V → Bool} {v : V} : v ∈ marked x ↔ x v = true := by
  simp [marked]

end QGraphColl


