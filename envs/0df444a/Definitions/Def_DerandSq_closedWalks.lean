-- Prove2me | Definitions.Def_DerandSq_closedWalks
-- name    : DerandSq_closedWalks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:33.658072+00:00
-- url     : https://prove2.me/theorems/6b59c920-0dcc-4310-b4d2-2402d33e6139
-- title:
--   Number of closed walks of length $n$
-- statement:
--   For a graph $G$, a vertex $v$ and $n \in \mathbb N$, this is the number of **closed walks of length $n$** in $G$ that start and end at $v$ (sequences $v = v_0, v_1, \dots, v_n = v$ of vertices with $v_{t-1} \sim v_t$).
--
--   **Formalization Note** Encoded as `Nat.card` of the type of walks from $v$ to $v$ of length $n$. This is the true count when the type is finite, which is the case for every locally finite graph, in particular $T_d \circledS H$ and the pruned graph $X$ (every vertex has at most $d^2$ neighbours).
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Proposition 4.6 and (4.11), pp.22–23

import Mathlib

namespace DerandSq

/-- The number of closed walks of length `n` from `v` in a graph `G` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), Proposition 4.6 and
(4.11), pp.22–23).

**Formalization Note** `Nat.card` of the type of walks `v → v` of length `n`. It is the true count
whenever that type is finite, which holds for every locally finite graph, in particular for
`dsTree H` and `prunedX H i₀` (every vertex has at most `d²` neighbours); on an infinite type
`Nat.card` would be `0`. -/
noncomputable def closedWalks {V : Type*} (G : SimpleGraph V) (v : V) (n : ℕ) : ℕ :=
  Nat.card {w : G.Walk v v // w.length = n}

end DerandSq


