-- Prove2me | Definitions.Def_WeldedPath_WeldedInstance
-- name    : WeldedPath_WeldedInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:35.115069+00:00
-- url     : https://prove2.me/theorems/bfaa2bb7-6420-4cb2-b2f9-1c93b2f70bee
-- title:
--   Welded trees instances: weld edges, proper 3-colorings and validity
-- statement:
--   An **instance** of the welded trees graph $G_n=(V_n,E_n)$ is given by the set $E_W$ of **weld edges**, pairs $(u,w)$ with $u\in\mathrm{col}(n)$ and $w\in\mathrm{col}(n+1)$, and an edge coloring $\mathrm{Color}:E_n\to\mathcal C$ with $\mathcal C=\{\alpha,\beta,\gamma\}$. The edges are the tree edges $\{v,p(v)\}$, one for every non-root vertex $v$, and the weld edges.
--
--   Each edge $e$ has a **tail** and a **head**: a tree edge is directed from the child $v$ to the parent $p(v)$, and a weld edge from its column-$n$ endpoint to its column-$(n+1)$ endpoint.
--
--   An instance is **valid** when
--
--   1. the weld is a single bipartite cycle through all $2^{n+1}$ leaves: every weld pair joins $\mathrm{col}(n)$ to $\mathrm{col}(n+1)$, every leaf lies on exactly two weld edges, and the weld edges connect all leaves;
--   2. the coloring is proper: two distinct edges with a common endpoint have different colors (such colorings exist by Kőnig's theorem, Observation 3.1).
--
--   All statements of the mission quantify over valid instances.
--
--   **Formalization Note** A tree edge is named `tree v` by its child, a weld edge `weld u w`. Colors are `Fin 3`. A connected $2$-regular simple graph on the $2^{n+1}\ge 4$ leaves is exactly one cycle through all of them.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §3.1, pp.14–16 (Observation 3.1, head and tail p.16)

import Mathlib
import Definitions.Def_WeldedPath_parent

namespace WeldedPath

/-- An edge of `G_n` (arXiv:2611.05912 (sha256 b31400a0…), §3.1, pp.14–16).

**Formalization Note.** A tree edge `{v, p(v)}` is `tree v`, named by its child `v`; a weld edge
`{u, w}` with `u ∈ col(n)`, `w ∈ col(n + 1)` is `weld u w`. Which of these are edges of a given
instance is fixed by `WeldedInstance.edges`. -/
inductive Edge
  | tree (v : ℕ)
  | weld (u w : ℕ)
  deriving DecidableEq

/-- `tail(e)` (arXiv:2611.05912 (sha256 b31400a0…), p.16): a tree edge is directed from the child
to the parent, so its tail is the child `v`; a weld edge goes from column `n` to column `n + 1`,
so its tail is the column-`n` endpoint `u`. -/
def Edge.tail : Edge → ℕ
  | .tree v => v
  | .weld u _ => u

/-- `head(e)` (arXiv:2611.05912 (sha256 b31400a0…), p.16): the parent `p(v)` of a tree edge
`{v, p(v)}`, the column-`(n+1)` endpoint `w` of a weld edge.

**Formalization Note.** `p(v)` is `parent n v`; on a tree edge of an instance it is never `⊥`,
and the fallback `v` is never used. -/
def Edge.head (n : ℕ) : Edge → ℕ
  | .tree v => (parent n v).getD v
  | .weld _ w => w

/-- `v` is an endpoint of `e`. -/
def Edge.Incident (n : ℕ) (e : Edge) (v : ℕ) : Prop := v = e.tail ∨ v = e.head n

/-- An instance of the welded trees graph with its edge coloring (arXiv:2611.05912
(sha256 b31400a0…), §3.1, pp.14–15): the weld `E_W`, a set of pairs `(u, w)`, and the coloring
`Color : E_n → C`.

**Formalization Note.** The source fixes one instance and one coloring "for the remainder of the
paper" (pp.14–15); statements of this mission quantify over every valid instance
(`WeldedInstance.IsValid`). Colors `C = {α, β, γ}` are `Fin 3`. The coloring is a function on all
`Edge`s; only its values on `edges` matter. -/
structure WeldedInstance (n : ℕ) where
  /-- The weld edges `E_W`, as pairs `(u, w)` with `u ∈ col(n)` and `w ∈ col(n + 1)`. -/
  weld : Finset (ℕ × ℕ)
  /-- The edge coloring `Color`. -/
  color : Edge → Fin 3

namespace WeldedInstance

variable {n : ℕ}

/-- The tree edges `E_{T_1} ∪ E_{T_2}`: one edge `{v, p(v)}` for each structural index with a
parent. -/
def treeEdges (n : ℕ) : Finset Edge :=
  ((Finset.range (numV n)).filter fun v => (parent n v).isSome).image Edge.tree

/-- The weld edges `E_W`. -/
def weldEdges (G : WeldedInstance n) : Finset Edge :=
  G.weld.image fun p => Edge.weld p.1 p.2

/-- The edge set `E_n = E_{T_1} ∪ E_{T_2} ∪ E_W`. -/
def edges (G : WeldedInstance n) : Finset Edge := treeEdges n ∪ G.weldEdges

/-- `v` is a leaf, i.e. lies in `col(n) ∪ col(n + 1)`. -/
def IsLeaf (n v : ℕ) : Prop := IsVertex n v ∧ (col n v = n ∨ col n v = n + 1)

/-- The simple graph on `ℕ` whose edges are the weld edges. -/
def weldGraph (G : WeldedInstance n) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ G.weld

/-- The weld is a bipartite cycle through all `2^{n+1}` leaves (arXiv:2611.05912
(sha256 b31400a0…), §3.1, p.14: "two binary trees `T_1`, `T_2` of height `n` … whose leaves are
joined by a bipartite cycle"): every pair joins `col(n)` to `col(n + 1)`, every leaf lies on
exactly two weld edges, and the weld graph connects all leaves.

**Formalization Note.** A connected 2-regular simple graph on the `2^{n+1} ≥ 4` leaves is one
cycle through all of them; a `Finset` of pairs has no parallel edges. -/
def IsWeld (G : WeldedInstance n) : Prop :=
  (∀ p ∈ G.weld, IsVertex n p.1 ∧ col n p.1 = n ∧ IsVertex n p.2 ∧ col n p.2 = n + 1) ∧
  (∀ v, IsLeaf n v → (G.weld.filter fun p => p.1 = v ∨ p.2 = v).card = 2) ∧
  (∀ a b, IsLeaf n a → IsLeaf n b → G.weldGraph.Reachable a b)

/-- `Color` is a proper edge coloring of `G_n` (Observation 3.1, arXiv:2611.05912
(sha256 b31400a0…), p.14): two distinct edges with a common endpoint have different colors. -/
def IsProperColoring (G : WeldedInstance n) : Prop :=
  ∀ e ∈ G.edges, ∀ e' ∈ G.edges, e ≠ e' → (∃ v, e.Incident n v ∧ e'.Incident n v) →
    G.color e ≠ G.color e'

/-- A valid instance: the weld is a single bipartite cycle on the leaves and the coloring is
proper. -/
def IsValid (G : WeldedInstance n) : Prop := G.IsWeld ∧ G.IsProperColoring

end WeldedInstance

end WeldedPath


