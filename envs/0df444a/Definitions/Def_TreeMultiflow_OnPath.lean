-- Prove2me | Definitions.Def_TreeMultiflow_OnPath
-- name    : TreeMultiflow_OnPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:06.10421+00:00
-- url     : https://prove2.me/theorems/390d859d-7e40-444c-8957-d7c22f342b9c
-- title:
--   Edge on the tree path between two vertices
-- statement:
--   Let $T$ be a tree, given as a simple graph on a vertex set $V$, and let $s,t\in V$. An edge $e$ **lies on the path between $s$ and $t$** if some path of $T$ (a walk without repeated vertices) from $s$ to $t$ uses $e$. Since a tree has exactly one path between any two vertices, this is the relation $e\in\mathrm{Path}(f)$ for a request $f$ with endpoints $s$ and $t$.
--
--   This relation defines the load of a set of requests and the constraints of the LP relaxation (1).
--
--   **Formalization Note** Edges are unordered pairs of vertices (`Sym2 V`). When $s=t$ the only path is the empty one, so no edge lies on it.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (Path(f), the unique path between the endpoints)

import Mathlib

namespace TreeMultiflow

/-- **The edge `e` lies on the tree path between `s` and `t`.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2: "Path(f), the unique path between its endpoints on the tree"; "e ∈ Path(f)".

`OnPath G s t e` holds when some path (a walk without repeated vertices) of `G` from `s` to `t`
uses the edge `e`. In a tree the path between two vertices is unique, so this is `e ∈ Path(f)` for
a request `f` with endpoints `s`, `t`.

**Formalization Note.** The tree is a `SimpleGraph V` and edges are elements of `Sym2 V`. For
`s = t` the only path is the empty walk, so no edge lies on it (the paper's empty path, p.5). -/
def OnPath {V : Type*} (G : SimpleGraph V) (s t : V) (e : Sym2 V) : Prop :=
  ∃ p : G.Walk s t, p.IsPath ∧ e ∈ p.edges

end TreeMultiflow


