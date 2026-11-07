-- Prove2me | Definitions.Def_MetricMSO_IsShortestPathSet
-- name    : MetricMSO_IsShortestPathSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:21.219455+00:00
-- url     : https://prove2.me/theorems/709c752f-79e2-4bce-a15c-65f4e69ba6b5
-- title:
--   The meaning of $\mathsf{SP}(P,s,t)$: $P$ is a shortest $s$-$t$ path set
-- statement:
--   A vertex set $P$ is a **shortest $s$-$t$ path set** if either $s=t$ and $P=\{s\}$, or $s\ne t$, the induced subgraph $G[P]$ is a path with endpoints exactly $s$ and $t$, and its length equals $d_G(s,t)$.
--
--   **Formalization Note** "$G[P]$ is a path" is a path walk from $s$ to $t$ with vertex set $P$ such that every edge of $G$ inside $P$ is an edge of the walk. Mathlib's `G.dist` is $0$ on unreachable pairs, but here a walk joins $s$ and $t$, so it is the true distance.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.1, p.12 (PDF 14); Definition 2.10, p.18 (PDF 20)

import Mathlib

namespace MetricMSO

/-- **Shortest `s`-`t` path set** (the meaning of the atom SP(P, s, t)).

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.1, p.12 (PDF 14):
"we say that P is an s-t path set if either (i) s = t and P = {s}, or (ii) s ≠ t, the graph G[P] is
a path, and its two endpoints are exactly s and t. … We call an s-t path set P shortest if its
length equals dG(s, t)." Definition 2.10, p.18 (PDF 20): "Thus G[P] must be a path with endpoints
s, t and length dG(s, t), where for s = t we require P = {s}."

`IsShortestPathSet G P s t` holds iff either `s = t` and `P = {s}`, or `s ≠ t` and there is a path
`p` from `s` to `t` in `G` whose vertex set is `P`, such that every edge of `G` between two vertices
of `P` is an edge of `p` (so the induced subgraph `G[P]` is exactly the path `p`), and the length of
`p` is `d_G(s, t)`.

**Formalization Note** `G.dist` is Mathlib's graph distance; it is `0` for unreachable pairs, but
here a walk from `s` to `t` exists, so it is the true distance `d_G(s, t)`. -/
def IsShortestPathSet {V : Type} [DecidableEq V] (G : SimpleGraph V) (P : Finset V) (s t : V) :
    Prop :=
  (s = t ∧ P = {s}) ∨
  (s ≠ t ∧ ∃ p : G.Walk s t, p.IsPath ∧ p.support.toFinset = P ∧
    (∀ u ∈ P, ∀ w ∈ P, G.Adj u w → s(u, w) ∈ p.edges) ∧ p.length = G.dist s t)

end MetricMSO


