-- Prove2me | Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
-- name    : WangKangXue_SpectralTuran_TuranPlusEdges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:21:03.697274+00:00
-- url     : https://prove2.me/theorems/5f08247a-632a-488e-b5f7-82fdf7ff17db
-- title:
--   Standing hypothesis: the extremal graphs for F are T_{n,r} plus a fixed number a of edges
-- statement:
--   Let $F$ be a graph and let $r, a \ge 0$ be integers. Write $\mathrm{ex}(n,F)$ for the **Turán number**, the maximum number of edges of an $F$-free graph on $n$ vertices, and $\mathrm{Ex}(n,F)$ for the set of $F$-free $n$-vertex graphs with exactly $\mathrm{ex}(n,F)$ edges. The **Turán graph** $T_{n,r}$ is the complete $r$-partite graph on $n$ vertices whose parts have $\lfloor n/r\rfloor$ or $\lceil n/r\rceil$ vertices.
--
--   We say that **the extremal graphs for $F$ are $T_{n,r}$ plus $a$ edges** if there is $N$ such that for every $n \ge N$:
--
--   1. $\mathrm{ex}(n,F) = e(T_{n,r}) + a$, and
--   2. every graph $H \in \mathrm{Ex}(n,F)$ contains a copy of $T_{n,r}$ (necessarily spanning, since both have $n$ vertices); together with 1, $H$ is obtained from $T_{n,r}$ by adding $a$ edges.
--
--   This is the hypothesis of Theorem 1.2 as fixed at the start of Section 3 of the paper (p. 4): "We may assume that the graphs in $\mathrm{Ex}(n,F)$ are obtained from $T_{n,r}$ by adding $a$ edges." It holds, for instance, for $F = K_{r+1}$ with $a = 0$ (Turán's theorem), and the paper cites further examples (friendship graphs, intersecting cliques).
--
--   **Formalization Note** The Turán graph is Mathlib's `turanGraph n r` on `Fin n` (vertices adjacent iff their residues mod $r$ differ), and $\mathrm{ex}(n,F)$ is Mathlib's `extremalNumber n F`. The number $a$ is a single constant for all large $n$, which is how the paper reads "$O(1)$ edges". A sorry-free check that the hypothesis holds for $F = K_{r+1}$, $a = 0$ was compiled against this definition.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 1 (ex, Ex, T_{n,r}), p. 2 (Theorem 1.2), p. 4 (opening of Section 3)

import Mathlib

namespace WangKangXue.SpectralTuran

open Classical in
/-- The standing hypothesis of Section 3 of Wang–Kang–Xue (arXiv:2203.10831v1, p. 4):
"the graphs in `Ex(n, F)` are obtained from `T_{n,r}` by adding `a` edges", for a fixed
number `a` and all sufficiently large `n`. Concretely, there is `N` such that for every
`n ≥ N`:
* `ex(n, F) = e(T_{n,r}) + a`, and
* every extremal graph for `F` on `n` vertices (an `F`-free `H` on `Fin n` with
  `e(H) = ex(n, F)`) contains a copy of the Turán graph `T_{n,r}`; as both graphs have `n`
  vertices the copy is spanning, so `H` is `T_{n,r}` plus `a` extra edges.

Mathlib's `turanGraph n r` lives on `Fin n` with `v ~ w ↔ v % r ≠ w % r`: the complete
`r`-partite graph whose parts (residue classes) have `⌊n/r⌋` or `⌈n/r⌉` vertices.
`extremalNumber n F` is the maximum number of edges of an `F`-free graph on `Fin n`. -/
def TuranPlusEdges {W : Type*} (F : SimpleGraph W) (r a : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    SimpleGraph.extremalNumber n F = (SimpleGraph.turanGraph n r).edgeFinset.card + a ∧
    ∀ H : SimpleGraph (Fin n), F.Free H →
      H.edgeFinset.card = SimpleGraph.extremalNumber n F →
      (SimpleGraph.turanGraph n r).IsContained H

end WangKangXue.SpectralTuran


