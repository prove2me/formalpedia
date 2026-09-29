-- Prove2me | Definitions.Def_HarelTarjan_SymOrder_Sym
-- name    : HarelTarjan_SymOrder_Sym
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:43:15.296285+00:00
-- url     : https://prove2.me/theorems/44fc6ae7-ff0a-47b4-9bd4-602c193d1393
-- title:
--   Symmetric-order (in-order) number $\mathrm{sym}(v)$ of a vertex of a complete binary tree
-- statement:
--   The vertices of the complete binary tree $T$ of depth $d$ are numbered from $1$ to $n$ in **symmetric order** (in-order): for every vertex, first all vertices of its left subtree, then the vertex itself, then all vertices of its right subtree. $\mathrm{sym}(v)$ denotes the number of the vertex $v$ (§3, p. 341, Fig. 1).
--
--   Concretely, give each vertex $s = s_1 s_2 \cdots s_k$ the sort key
--   $$\kappa(s) = (c(s_1), c(s_2), \dots, c(s_k), 1), \qquad c(\mathrm{L}) = 0,\; c(\mathrm{R}) = 2,$$
--   and compare keys lexicographically. A left descendant of $s$ has key $\kappa(s)$'s first $k$ entries followed by $0$, so it precedes $s$; a right descendant has $2$ there, so it follows $s$. Then
--   $$\mathrm{sym}(v) = \#\{u \in T : \kappa(u) \le \kappa(v)\},$$
--   the rank of $v$ in symmetric order, counting from $1$.
--
--   For depth $4$ this reproduces Fig. 1: the root is $16$, its children $8$ and $24$, and the leaves are $1, 3, \dots, 31$ from left to right.
--
--   **Formalization Note** The key is a `List ℕ` and `≤` on `List ℕ` is the lexicographic order. The definition deliberately does not use the closed form or a recursive numbering: those are the content of the milestones. That `sym` is a bijection onto $\{1,\dots,2^{d+1}-1\}$ is the separate theorem `sym_bijective_range`.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 341, §3 and Fig. 1

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree

namespace HarelTarjan.SymOrder

/-- The symmetric-order (in-order) sort key of a path `s`: each turn is written `0` (left) or `2`
(right), and the marker `1` ("the vertex itself") is appended. Comparing keys lexicographically
places, for every vertex, its whole left subtree first, then the vertex, then its whole right
subtree: this is symmetric (in-order) traversal order. -/
def key (s : List Bool) : List ℕ :=
  s.map (fun b => if b then 2 else 0) ++ [1]

/-- The symmetric-order number `sym(v)` of a vertex `v` of the complete binary tree of depth `d`
(Harel–Tarjan, §3, p. 341, Fig. 1): the vertices are numbered from `1` to `n` in symmetric order,
so `sym(v)` is the number of vertices `u` that come no later than `v` in symmetric order, i.e. whose
key is lexicographically `≤` the key of `v` (`≤` on `List ℕ` is the lexicographic order). -/
def sym {d : ℕ} (v : Vertex d) : ℕ :=
  (Finset.univ.filter (fun u : Vertex d => key u.1 ≤ key v.1)).card

end HarelTarjan.SymOrder


