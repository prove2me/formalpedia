-- Prove2me | Definitions.Def_OnlineColoringKYY_run
-- name    : OnlineColoringKYY_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:29.772198+00:00
-- url     : https://prove2.me/theorems/41973499-922f-43ea-bd4a-7d4736fe6720
-- title:
--   Color $c(v)$ assigned by an online algorithm
-- statement:
--   Let $A$ be a deterministic online coloring algorithm and let $G$ be a graph on the vertices $0, 1, \dots, n-1$, presented in this order. The color that $A$ assigns to the vertex $v$ is
--   $$
--   c_A^G(v) = A\bigl(v,\, G[\{0, \dots, v\}]\bigr),
--   $$
--   the output of $A$ on the prefix graph at $v$. It depends only on the graph induced on the vertices that arrived up to and including $v$.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 (PDF p.12)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The color `c(v)` that the online algorithm `A` assigns to vertex `v` when the vertices of
`G : SimpleGraph (Fin n)` arrive in the order `0, 1, …, n − 1` (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed
p.10 = PDF p.12).

**Formalization Note** `c(v)` is `A.color v (prefixGraph G v)`: it depends only on the graph induced
on the vertices `0, …, v` (causality is built into the type of `A`). -/
def run (A : OnlineColoringAlg) {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  A.color v.val (prefixGraph G v)

end OnlineColoringKYY


