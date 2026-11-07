-- Prove2me | Definitions.Def_OnlineColoringKYY_stepGraph
-- name    : OnlineColoringKYY_stepGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:05.435925+00:00
-- url     : https://prove2.me/theorems/20f5fc9d-04b5-42eb-9621-d77aafabf0f7
-- title:
--   Graph built by the adversary on the first $m+1$ arrivals
-- statement:
--   Given the player's colors $c(0), \dots, c(m-1)$ of the first $m$ arrivals and the codes $x_0, \dots, x_m$, the graph built by the Section 4.2 adversary on the vertices $\{0, \dots, m\}$ joins $i < j$ exactly when the edge rule holds for $(i, j)$: $i$ is paired by some $w < j$ and $\varphi(i) \notin X_j$. It is the graph the player sees when the vertex $m$ arrives.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineColoringKYY_admits
import Definitions.Def_OnlineColoringKYY_baseColor
import Definitions.Def_OnlineColoringKYY_advEdge

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The graph the adversary has built after the `(m+1)`-st arrival, given the player's colors `cs`
of the earlier arrivals (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 = PDF p.15): on
`Fin (m + 1)`, vertices `i < j` are adjacent iff `advEdge code cs i j`.

**Formalization Note** `SimpleGraph.fromRel` symmetrizes the relation `i < j ∧ …` and removes
loops. -/
def stepGraph {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (cs : ℕ → ℕ) (m : ℕ) :
    SimpleGraph (Fin (m + 1)) :=
  SimpleGraph.fromRel fun i j => advEdge code cs i.val j.val

end OnlineColoringKYY


