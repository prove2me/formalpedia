-- Prove2me | Definitions.Def_SpecExtremalConj_IsMaxCut
-- name    : SpecExtremalConj_IsMaxCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:35.945111+00:00
-- url     : https://prove2.me/theorems/097d4cec-0985-489f-9efe-6934a30c215b
-- title:
--   Maximizing partition (max-cut)
-- statement:
--   A partition $V(G)=V_1\cup\dots\cup V_r$ is **maximizing** if its number of crossing edges $\sum_{1\le i<j\le r}e(V_i,V_j)$ is at least that of every other partition of $V(G)$ into $r$ labelled (possibly empty) parts.
--
--   Lemmas 3.3–3.10 are statements about such a partition of a spectral extremal graph.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Lemma 3.3, p. 4 ("a partition V(G) = V_1 ∪ … ∪ V_r such that Σ_{1≤i<j≤r} e(V_i, V_j) attains the maximum")

import Mathlib
import Definitions.Def_SpecExtremalConj_crossEdges
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Maximizing partition.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Lemma 3.3, p. 4: "G has a partition V(G) = V_1 ∪ … ∪ V_r such
that Σ_{1≤i<j≤r} e(V_i, V_j) attains the maximum".

`IsMaxCut G P` says that the partition `P : V → Fin r` has at least as many crossing edges as
every other partition `P'` of the vertex set into `r` (possibly empty) parts.

**Formalization Note.** The maximum is over all maps `V → Fin r`, i.e. all ordered partitions into
`r` labelled, possibly empty parts, which is the paper's maximum. -/
def IsMaxCut {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : V → Fin r) : Prop :=
  ∀ P' : V → Fin r, crossEdges G P' ≤ crossEdges G P

end SpecExtremalConj


