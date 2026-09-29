-- Prove2me | Definitions.Def_HarelTarjan_SymOrder_Algorithms
-- name    : HarelTarjan_SymOrder_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:43:45.827573+00:00
-- url     : https://prove2.me/theorems/ecd8a042-c884-4993-a516-1e0d10cfffe7
-- title:
--   The nca depth algorithm and the depth algorithm of §3, as functions of the numbers
-- statement:
--   The two constant-time procedures of §3 (p. 342) on the complete binary tree $T$ of depth $d$, written as functions of the numbers $\mathrm{sym}(\cdot)$, the heights $h(\cdot)$ and $d$, which the paper assumes known.
--
--   1. **Algorithm to solve the nca depth problem.** Given vertices $v, w$: if $\mathrm{sym}(w) \in [\mathrm{sym}(v) - 2^{h(v)} + 1,\ \mathrm{sym}(v) + 2^{h(v)} - 1]$, return $d - h(v)$; otherwise, if $\mathrm{sym}(v) \in [\mathrm{sym}(w) - 2^{h(w)} + 1,\ \mathrm{sym}(w) + 2^{h(w)} - 1]$, return $d - h(w)$; otherwise return
--   $$d - \lfloor \lg(\mathrm{sym}(v) \oplus \mathrm{sym}(w)) \rfloor,$$
--   where $\oplus$ is bitwise exclusive or.
--   2. **Algorithm to solve the depth problem (its arithmetic part).** Given a vertex $v$ and a depth $d_2$, let $h = d - d_2$ and compute
--   $$2^{h+1} \left\lfloor \mathrm{sym}(v) / 2^{h+1} \right\rfloor + 2^h;$$
--   the algorithm returns the vertex with this number.
--
--   The algorithm to compute $\operatorname{nca}(v,w)$ composes them: Step 1 computes $d_0$ by the first, Step 2 the depth-$d_0$ ancestor of $v$ by the second.
--
--   **Formalization Note** The interval tests are written additively, $\mathrm{sym}(v) + 1 \le \mathrm{sym}(w) + 2^{h(v)}$ and $\mathrm{sym}(w) + 1 \le \mathrm{sym}(v) + 2^{h(v)}$, to avoid truncated subtraction on $\mathbb N$. $\lfloor \lg x \rfloor$ is `Nat.log 2 x` (equal for $x \ge 1$) and $\oplus$ is `^^^`. The subtractions $d - h(v)$ and $d - d_2$ are on $\mathbb N$; they do not truncate for heights and depths of vertices. The final $\mathrm{sym}^{-1}$ lookup is not defined; the goal theorem compares numbers instead.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, §3 (Algorithm to solve the nca depth problem; Algorithm to solve the depth problem)

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- The algorithm to solve the nca depth problem (Harel–Tarjan, §3, p. 342), which uses only the
numbers `sym(·)`, the heights `h(·)` and the depth `d` of the tree:
* if `sym(w) ∈ [sym(v) − 2^{h(v)} + 1, sym(v) + 2^{h(v)} − 1]` (written additively), return
  `d − h(v)`;
* otherwise, if `sym(v) ∈ [sym(w) − 2^{h(w)} + 1, sym(w) + 2^{h(w)} − 1]`, return `d − h(w)`;
* otherwise return `d − ⌊lg (sym(v) ⊕ sym(w))⌋`, where `⊕` is bitwise exclusive or and
  `⌊lg x⌋` is `Nat.log 2 x`. -/
def ncaDepthAlg {d : ℕ} (v w : Vertex d) : ℕ :=
  if sym v + 1 ≤ sym w + 2 ^ height v ∧ sym w + 1 ≤ sym v + 2 ^ height v then
    d - height v
  else if sym w + 1 ≤ sym v + 2 ^ height w ∧ sym v + 1 ≤ sym w + 2 ^ height w then
    d - height w
  else
    d - Nat.log 2 (sym v ^^^ sym w)

/-- The number computed by the algorithm to solve the depth problem (Harel–Tarjan, §3, p. 342):
given a vertex `v` and a depth `d₂`, let `h = d − d₂` and return
`2^{h+1} ⌊sym(v) / 2^{h+1}⌋ + 2^h` (the algorithm then returns `sym⁻¹` of this number). -/
def depthAlgNum {d : ℕ} (v : Vertex d) (d₂ : ℕ) : ℕ :=
  2 ^ (d - d₂ + 1) * (sym v / 2 ^ (d - d₂ + 1)) + 2 ^ (d - d₂)

end HarelTarjan.SymOrder


