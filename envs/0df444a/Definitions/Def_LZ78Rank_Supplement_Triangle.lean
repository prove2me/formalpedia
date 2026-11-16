-- Prove2me | Definitions.Def_LZ78Rank_Supplement_Triangle
-- name    : LZ78Rank_Supplement_Triangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:56:44.472563+00:00
-- url     : https://prove2.me/theorems/53aa9325-f9c0-4df8-8172-8c546924c0d3
-- title:
--   The All-Edges Sparse Triangle problem on a graph $G=(V,E)$, $V=[1\,.\,.\,n]$, $E\subseteq V\times V$
-- statement:
--   Let $G=(V,E)$ be a graph in the paper's sense (Section 2.2): $V=\{1,\dots,n\}$ and $E\subseteq V\times V$ is a set of $m$ ordered pairs. Its edges are listed as $(u_1,v_1),\dots,(u_m,v_m)$, every pair exactly once.
--
--   An edge $(u,v)\in E$ **lies in a triangle** when some vertex $w$ satisfies
--   $$(v,w)\in E \quad\text{and}\quad (w,u)\in E.$$
--   The **All-Edges Sparse Triangle** problem asks, for every edge, whether it lies in a triangle (Section 2.7). An instance is given to a machine as the words $n,m,u_1,v_1,\dots,u_m,v_m$. The answer is the list of $m$ bits whose $k$-th entry is $1$ exactly when the $k$-th listed edge lies in a triangle.
--
--   All-Edges Sparse Triangle is the source of hardness for the paper's conditional lower bound on rank and occurrence queries (Theorem 6.8). Its fastest known algorithm runs in $O(m^{2\omega/(\omega+1)})$ time.
--
--   An undirected simple graph is the instance that lists both orientations of every edge and no loop; there "lies in a triangle" is the usual notion.
--
--   **Formalization Note** `IsEdgeList n es` requires endpoints in $[1\,.\,.\,n]$ and no pair listed twice; as in the paper, no symmetry and no loop-freeness is imposed. `InTriangle` quantifies over all natural numbers $w$; a witness with $(v,w)$ in the list is automatically in $[1\,.\,.\,n]$.
-- source:
--   De–Kempa, Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive Substructures, STOC 2027 submission (manuscript sha256 db4050af4e62ca74150f041d554ea7b206351a0c4ce7a37cb017488d6330ec6d), Section 2.7, p.12 (PDF p.12); graphs and V = {1, …, n} as in Section 2.2, p.9 (PDF p.9)

import Mathlib

set_option autoImplicit false

namespace LZ78Rank.Supplement

/-!
# The All-Edges Sparse Triangle problem

De–Kempa, *Near-Optimal Compressed Algorithms and Data Structures by Eliminating Recursive
Substructures*, STOC 2027 submission (manuscript sha256 db4050af4e62…330ec6d), Section 2.7,
p.12 (= PDF p.12): "All-Edges Sparse Triangle. Input: An graph G = (V, E) with |V| = n and
|E| = m. Output: Determine for every edge (u, v) ∈ E whether (u, v) is in a triangle, i.e.,
∃w ∈ V such that (v, w) ∈ E and (w, u) ∈ E." Section 2.2, p.9: "A graph is a pair
G = (V, E), where V is the vertex set and E ⊆ V × V is the set of edges over V. We assume the
vertices are labeled as V = {1, . . . , |V|}."

**Formalization Note.**
* A graph is the paper's `G = (V, E)` with `V = {1, …, n}` and `E ⊆ V × V` (Section 2.2, p.9):
  a set of ordered pairs, given as the list of its distinct pairs `((u₁, v₁), …, (u_m, v_m))`
  (`IsEdgeList n es`). No symmetry and no loop-freeness is imposed, because the paper imposes
  none; an undirected simple graph is the instance whose list holds both orientations of every
  edge and no loop, and on it "in a triangle" is the usual notion.
* Machine layout of an instance: `n, m, u₁, v₁, …, u_m, v_m` (`encEdges`).
* Output: `m` words, the `k`-th is `1` iff the `k`-th listed pair `(u_k, v_k)` lies in a
  triangle, i.e. some `w` has `(v_k, w) ∈ E` and `(w, u_k) ∈ E` (Section 2.7, verbatim), else `0`
  (`aestAnswer`).
-/

/-- The edge list of a graph `G = (V, E)` with `V = [1 . . n]` and `E ⊆ V × V` (Section 2.2):
endpoints in `[1 . . n]` and no pair listed twice. -/
def IsEdgeList (n : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ es, 1 ≤ e.1 ∧ e.1 ≤ n ∧ 1 ≤ e.2 ∧ e.2 ≤ n) ∧ es.Nodup

/-- The edge `(u, v)` is in a triangle: some vertex `w` has `(v, w) ∈ E` and `(w, u) ∈ E`
(Section 2.7). -/
def InTriangle (es : List (ℕ × ℕ)) (u v : ℕ) : Prop := ∃ w : ℕ, (v, w) ∈ es ∧ (w, u) ∈ es

/-- The machine layout of an All-Edges Sparse Triangle instance: `n, m, u₁, v₁, …, u_m, v_m`. -/
def encEdges (n : ℕ) (es : List (ℕ × ℕ)) : List ℕ :=
  n :: es.length :: es.flatMap (fun e => [e.1, e.2])

open Classical in
/-- The answer to All-Edges Sparse Triangle: for each listed edge in order, `1` if it lies in a
triangle and `0` otherwise. -/
noncomputable def aestAnswer (es : List (ℕ × ℕ)) : List ℕ :=
  es.map (fun e => if InTriangle es e.1 e.2 then 1 else 0)

end LZ78Rank.Supplement


