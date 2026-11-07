-- Prove2me | Definitions.Def_OnlineColoringKYY_prefixGraph
-- name    : OnlineColoringKYY_prefixGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:30.875676+00:00
-- url     : https://prove2.me/theorems/8ef4f89c-bd5b-4205-84f4-b2c80de09081
-- title:
--   Prefix graph $G[\{0,\dots,v\}]$ seen at the arrival of $v$
-- statement:
--   Let $G$ be a graph on the vertices $0, 1, \dots, n-1$, which arrive in this order. For a vertex $v$, the **prefix graph** of $G$ at $v$ is the induced subgraph
--   $$
--   G[\{0, 1, \dots, v\}]
--   $$
--   on the first $v+1$ arrivals: the part of the input an online algorithm has seen when it must color $v$. The vertex $v$ is its last vertex.
--
--   **Formalization Note** The prefix graph lives on `Fin (v + 1)` and is the pullback of `G` along `Fin.castLE`.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The **prefix graph** of `G` at vertex `v` (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 = PDF p.12):
the subgraph of `G` induced on the first `v + 1` arrivals `0, 1, …, v`, which is what the online
algorithm has seen when it colors `v`.

**Formalization Note** The vertices of `G : SimpleGraph (Fin n)` arrive in the order
`0, 1, …, n − 1`; the prefix graph lives on `Fin (v + 1)`, embedded in `Fin n` by `Fin.castLE`, so
that `v` itself is `Fin.last v`. -/
def prefixGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin (v.val + 1)) :=
  G.comap (Fin.castLE (Nat.succ_le_of_lt v.isLt))

end OnlineColoringKYY


