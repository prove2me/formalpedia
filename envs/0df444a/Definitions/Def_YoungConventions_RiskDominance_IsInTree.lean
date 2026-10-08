-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsInTree
-- name    : YoungConventions_RiskDominance_IsInTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:09.143989+00:00
-- url     : https://prove2.me/theorems/a6e104d5-9d55-4d44-b8dd-fcb0827f446b
-- title:
--   $i$-tree (in-tree rooted at $i$)
-- statement:
--   Let $V$ be a finite set of vertices and $i\in V$. An **$i$-tree** is a spanning tree on $V$ such that from every vertex $j\neq i$ there is a unique path directed from $j$ to $i$. Equivalently, it is given by a parent map $j\mapsto\pi(j)\in V$ on $V\setminus\{i\}$ such that following parents from any vertex $j$ eventually reaches $i$; the edges of the tree are $(j,\pi(j))$.
--
--   **Formalization Note** Trees point to the root. With exactly one outgoing edge per non-root vertex, the path to the root is unique, so the two descriptions agree.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 69, displayed definition (i-tree)

import Mathlib

namespace YoungConventions.RiskDominance

/-- **`i`-tree (in-arborescence), parent-map encoding.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 69 (PDF p. 14): "An
`i`-tree in `𝒢` is a spanning tree such that from every vertex `j ≠ i` there is a unique path
directed from `j` to `i`."

`IsInTree V root par` holds iff `root ∈ V` and every vertex `v ∈ V` other than the root has its
parent `par v` in `V` and reaches the root by following parents. The edges of the tree are
`(v, par v)` for `v ∈ V \ {root}`.

**Formalization Note.** Trees point **to** the root. Each non-root vertex has exactly one outgoing
edge, so the path to the root is unique, and every such parent map is a spanning in-tree; conversely
every `i`-tree is of this form (a spanning tree has `|V| − 1` edges and each non-root vertex needs an
out-edge). Values of `par` outside `V \ {root}` are irrelevant. -/
def IsInTree {α : Type*} (V : Finset α) (root : α) (par : α → α) : Prop :=
  root ∈ V ∧ ∀ v ∈ V, v ≠ root → par v ∈ V ∧ ∃ n : ℕ, par^[n] v = root

end YoungConventions.RiskDominance


