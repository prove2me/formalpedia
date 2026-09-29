-- Prove2me | Definitions.Def_HarelTarjan_Compressed_RootedTree
-- name    : HarelTarjan_Compressed_RootedTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:50:11.766176+00:00
-- url     : https://prove2.me/theorems/59e4e3e6-0609-4ee5-844b-b2543ecab7e7
-- title:
--   Rooted trees given by a parent map; ancestors, depth and subtree size $\mathrm{size}_T(v)$
-- statement:
--   The tree model of Harel and Tarjan's Appendix (p. 354) together with the subtree size of §4 (p. 343).
--
--   1. **Rooted tree.** A rooted tree $T$ on a finite vertex set $V$ consists of a root $r \in V$ and a parent map $p$ such that for every vertex $v$ there is an integer $i \ge 0$ with $p^i(v) = r$, where $p^0(v) = v$ and $p^{i+1}(v) = p(p^i(v))$. The edges of $T$ are the pairs $v \to p(v)$ for $v \ne r$.
--   2. **Ancestors.** If $p^i(v) = w$ for some $i \ge 0$, then $v$ is a descendant of $w$ and $w$ is an ancestor of $v$. Every vertex is an ancestor and a descendant of itself.
--   3. **Depth.** The depth of $v$ is the length of the path from $v$ to $r$, i.e. the least $i$ with $p^i(v) = r$.
--   4. **Size.** $\mathrm{size}_T(v)$ is the number of descendants of $v$ in $T$, including $v$ itself.
--
--   These objects underlie the heavy-path decomposition and the compressed tree of §4.
--
--   **Formalization Note** The paper's parent map is defined on $V \setminus \{r\}$ only. Here it is a total map $V \to V$ with the convention $p(r) = r$; no statement of the mission uses the pseudo-edge $r \to r$, and every statement about an edge $v \to p(v)$ carries the hypothesis $v \ne r$. The Appendix prints "$p^0(v) = 0$", a typo for $p^0(v) = v$; Lean's `Function.iterate` uses $p^0(v) = v$. The vertex set is a `Fintype`, so $n = |V|$ is `Fintype.card V` (and $n \ge 1$, since the root exists).
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 354, Appendix (tree terminology); p. 343, §4 (definition of size)

import Mathlib

namespace HarelTarjan.Compressed

/-- A rooted tree on the finite vertex set `V` (Harel–Tarjan, Appendix, p. 354): a root `r` and a
parent map `p` such that every vertex reaches the root by iterating `p` (`pⁱ(v) = r` for some
`i ≥ 0`). The paper's parent map is defined on `V − {r}` only; here it is total, with the
convention `p(r) = r`, and the edges of the tree are the pairs `v → p(v)` for `v ≠ r`. -/
structure RootedTree (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The root `r`. -/
  root : V
  /-- The parent map `p`; its value at the root is the root itself (a convention). -/
  parent : V → V
  /-- Convention for the paper's partial map: `p(r) = r`. -/
  parent_root : parent root = root
  /-- Every vertex reaches the root: `pⁱ(v) = r` for some `i ≥ 0`. -/
  reaches : ∀ v, ∃ i : ℕ, parent^[i] v = root

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsAncestor T w v`: `pⁱ(v) = w` for some `i ≥ 0`, i.e. `v` is a descendant of `w` and `w` an
ancestor of `v` (Appendix, p. 354). Every vertex is an ancestor and a descendant of itself. -/
def IsAncestor (T : RootedTree V) (w v : V) : Prop := ∃ i : ℕ, T.parent^[i] v = w

/-- The depth of `v`: the length of the path from `v` to the root, i.e. the least `i` with
`pⁱ(v) = r` (Appendix, p. 354). -/
def depth (T : RootedTree V) (v : V) : ℕ := Nat.find (T.reaches v)

/-- `size_T(v)`: the number of descendants of `v` in `T`, including `v` itself (§4, p. 343). -/
noncomputable def size (T : RootedTree V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun u => IsAncestor T v u)).card

end HarelTarjan.Compressed


