-- Prove2me | Definitions.Def_SpecExtremalConj_ContainsSpanningTuran
-- name    : SpecExtremalConj_ContainsSpanningTuran
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:41.612293+00:00
-- url     : https://prove2.me/theorems/5e712848-fb22-4505-add0-7e49ce6bb208
-- title:
--   $H$ is obtained from $T_{n,r}$ by adding edges
-- statement:
--   The **Turán graph** $T_{n,r}$ is the complete $r$-partite graph on $n$ vertices in which each part has $\lfloor n/r\rfloor$ or $\lceil n/r\rceil$ vertices and the edges are all pairs joining distinct parts.
--
--   A graph $H$ on $n$ vertices is **obtained from $T_{n,r}$ by adding edges** if, after relabelling its vertices, $H$ contains every edge of $T_{n,r}$; that is, there is a bijection $e$ of the vertex set with
--
--   $$uv\in E(T_{n,r})\ \Longrightarrow\ e(u)e(v)\in E(H).$$
--
--   The number of added edges is then $e(H)-e(T_{n,r})$.
--
--   This is the shape the hypothesis of Theorem 1.2 imposes on the extremal graphs for $F$.
--
--   **Formalization Note** $T_{n,r}$ is Mathlib's `turanGraph n r` on `Fin n` (vertices $v,w$ adjacent iff $v \bmod r\ne w \bmod r$); the relabelling is a permutation of `Fin n`.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §1, p. 1 (Turán graph T_{n,r}) and Theorem 1.2, p. 2

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **"Obtained from T_{n,r} by adding edges".** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §1, p. 1 (Turán graph T_{n,r}: "the complete
r-partite graph on n vertices where each partite set has either ⌊n/r⌋ or ⌈n/r⌉ vertices and the
edge set consists of all pairs joining distinct parts") and Theorem 1.2, p. 2 ("obtained from
T_{n,r} by adding … edges").

`ContainsSpanningTuran r H` says that some relabelling `e` of `Fin n` maps every edge of Mathlib's
`turanGraph n r` (vertices `v, w` adjacent iff `v % r ≠ w % r`; parts of sizes ⌊n/r⌋, ⌈n/r⌉) to
an edge of `H`: `H` contains a spanning copy of T_{n,r}, so `H` is T_{n,r} plus the edges of `H`
not in that copy.

**Formalization Note.** Graphs are taken up to isomorphism, as in the paper, hence the
relabelling `e`. The number of added edges is not part of this predicate; it is
`#H.edgeFinset − #(turanGraph n r).edgeFinset`. -/
def ContainsSpanningTuran {n : ℕ} (r : ℕ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ u v, (turanGraph n r).Adj u v → H.Adj (e u) (e v)

end SpecExtremalConj


