-- Prove2me | Definitions.Def_WeldedPath_parent
-- name    : WeldedPath_parent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:37.239806+00:00
-- url     : https://prove2.me/theorems/d33562c0-fcb1-4613-8f82-311972800372
-- title:
--   Structural indices, columns and parents of the welded trees graph $G_n$
-- statement:
--   The welded trees graph $G_n$ consists of two binary trees $T_1, T_2$ of height $n$ whose $2^{n+1}$ leaves are joined by a cycle. Its $2^{n+2}-2$ vertices carry **structural indices** $w \in [0, 2^{n+2}-3]$: the entrance $r(T_1)$ has index $0$, the exit $r(T_2)$ has index $2^{n+1}-1$, and the children of a vertex $w'$ are
--   $$
--   2w'+1,\ 2w'+2 \quad (\text{columns } [1,n]), \qquad 2w'-2^{n+1}+2,\ 2w'-2^{n+1}+3 \quad (\text{columns } [n+1,2n]).
--   $$
--   The **column** $\mathrm{col}(w)\in[0,2n+1]$ is the depth in $T_1$ for $T_1$-vertices and $2n+1$ minus the depth in $T_2$ for $T_2$-vertices. The **parent** is
--   $$
--   p(w)=\begin{cases}\lfloor (w-1)/2\rfloor & \mathrm{col}(w)\in[1,n],\\ \lfloor (w-2^{n+1})/2\rfloor+2^{n+1}-1 & \mathrm{col}(w)\in[n+1,2n],\\ \bot & \text{otherwise.}\end{cases}
--   $$
--
--   These indices name the vertices throughout the mission; the algorithm never sees them, only random labels.
--
--   **Formalization Note** Indices are natural numbers; `IsVertex n w` is $w < 2^{n+2}-2$. Both trees are stored in heap order, so the column of a $T_1$-index is $\lfloor\log_2(w+1)\rfloor$ and that of a $T_2$-index $w$ is $2n+1-\lfloor\log_2(w-2^{n+1}+2)\rfloor$. $\bot$ is `none`.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §3.1, p.14

import Mathlib

namespace WeldedPath

/-- The number `|V_n| = 2^{n+2} − 2` of vertices of the welded trees graph `G_n`: the structural
indices are `0, …, 2^{n+2} − 3` (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder,
Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912
(sha256 b31400a0…), §3.1, p.14). -/
def numV (n : ℕ) : ℕ := 2 ^ (n + 2) - 2

/-- `w ∈ V_n`: the natural number `w` is a structural index, `w ≤ 2^{n+2} − 3`
(arXiv:2611.05912 (sha256 b31400a0…), §3.1, p.14). -/
def IsVertex (n w : ℕ) : Prop := w < numV n

instance (n w : ℕ) : Decidable (IsVertex n w) := inferInstanceAs (Decidable (w < numV n))

/-- The column `col(w) ∈ [0, 2n+1]` of the structural index `w` (arXiv:2611.05912
(sha256 b31400a0…), §3.1, p.14: `col(c)` is depth `c` in `T_1` for `c ≤ n` and depth
`2n + 1 − c` in `T_2` for `c ≥ n + 1`).

**Formalization Note.** The structural indexing of p.14 numbers `T_1` in heap order: the root
`r(T_1)` is `0` and the children of `w` are `2w + 1`, `2w + 2`, so `w` has depth
`⌊log₂(w + 1)⌋`. `T_2` occupies `2^{n+1} − 1, …, 2^{n+2} − 3`; shifting by `2^{n+1} − 1` (its root)
gives the same heap order (the children `2w − 2^{n+1} + 2`, `2w − 2^{n+1} + 3` of p.14 become
`2u + 1`, `2u + 2`). The value at a natural number that is not a structural index is not used. -/
def col (n w : ℕ) : ℕ :=
  if w < 2 ^ (n + 1) - 1 then Nat.log 2 (w + 1)
  else 2 * n + 1 - Nat.log 2 (w - (2 ^ (n + 1) - 1) + 1)

/-- The parent `p(w)` of a structural index (arXiv:2611.05912 (sha256 b31400a0…), §3.1, p.14):
`p(w) = ⌊(w − 1)/2⌋` if `col(w) ∈ [1, n]`, `p(w) = ⌊(w − 2^{n+1})/2⌋ + 2^{n+1} − 1` if
`col(w) ∈ [n + 1, 2n]`, and `⊥` otherwise (the two roots, and every number that is not a
structural index).

**Formalization Note.** `⊥` is `none`. Natural-number division is the floor. On columns
`[n + 1, 2n]` every index is at least `2^{n+1}`, so the subtraction `w − 2^{n+1}` is not
truncated. -/
def parent (n w : ℕ) : Option ℕ :=
  if IsVertex n w ∧ 1 ≤ col n w ∧ col n w ≤ n then some ((w - 1) / 2)
  else if IsVertex n w ∧ n + 1 ≤ col n w ∧ col n w ≤ 2 * n then
    some ((w - 2 ^ (n + 1)) / 2 + 2 ^ (n + 1) - 1)
  else none

/-- The entrance `r(T_1)`, structural index `0` (arXiv:2611.05912 (sha256 b31400a0…), p.14). -/
def entrance : ℕ := 0

/-- The exit `r(T_2)`, structural index `2^{n+1} − 1` (arXiv:2611.05912 (sha256 b31400a0…),
p.14). -/
def exitIdx (n : ℕ) : ℕ := 2 ^ (n + 1) - 1

end WeldedPath


