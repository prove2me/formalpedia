-- Prove2me | Definitions.Def_OnlineColoringKYY_numColors
-- name    : OnlineColoringKYY_numColors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:14.506597+00:00
-- url     : https://prove2.me/theorems/eea134de-2b48-4e4f-8a3a-767e9228174d
-- title:
--   Number of colors $|\{c(v) : v \in V\}|$ used by an online algorithm
-- statement:
--   The **number of colors** that the online algorithm $A$ uses on the input $G$ (vertices $0, \dots, n-1$ in arrival order) is
--   $$
--   \mathrm{ALG}(G) = \bigl|\{c_A^G(v) : v \in V\}\bigr|,
--   $$
--   the number of distinct colors it assigns. This is the objective of Definition 3.1 and the performance $\mathrm{ALG}(I)$ of Definition 3.2.
--
--   **Formalization Note** The cardinality of the image of $v \mapsto c_A^G(v)$, not the largest color plus one.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 (PDF p.12)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The **number of colors** `|{c(v) : v ∈ V}|` that the online algorithm `A` uses on the input
`G : SimpleGraph (Fin n)` (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 = PDF p.12). This is `ALG(I)` in
Definition 3.2.

**Formalization Note** The cardinality of the image of `v ↦ run A G v` over all `n` vertices
(not the largest color plus one). -/
def numColors (A : OnlineColoringAlg) {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.image (run A G)).card

end OnlineColoringKYY


