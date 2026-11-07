-- Prove2me | Definitions.Def_OnlineColoringKYY_advColors
-- name    : OnlineColoringKYY_advColors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:21.411495+00:00
-- url     : https://prove2.me/theorems/44e43074-cd3e-4970-b1e2-8c6c8b80c783
-- title:
--   Player's colors in the Section 4.2 adversary process
-- statement:
--   Fix a deterministic online coloring algorithm $A$ and codes $x_0, x_1, \dots$. The **adversary process** of Section 4.2 runs as follows. Vertex $v$ arrives with its edges to $0, \dots, v-1$ given by the edge rule applied to the colors $c(0), \dots, c(v-1)$ chosen so far, and the player colors it
--   $$
--   c(v) = A\bigl(v,\ \text{the graph built on } \{0, \dots, v\}\bigr).
--   $$
--   The colors are defined by recursion on $v$; after $v$ steps the first $v$ colors are fixed and never change.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_admits
import Definitions.Def_OnlineColoringKYY_baseColor
import Definitions.Def_OnlineColoringKYY_advEdge
import Definitions.Def_OnlineColoringKYY_stepGraph

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The player's colors in the **adversary process** of Section 4.2 (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2,
"Adversary algorithm", printed p.13 = PDF p.15), against the deterministic algorithm `A` and the
code `code` (the choice of the sets `X_v`).

`advColors A code v` is the list of the colors of the first `v` arrivals (entries `≥ v` are `0`):
the `(v+1)`-st arrival `v` receives `A.color v (stepGraph code (advColors A code v) v)`, the color
`A` chooses on the graph the adversary has built from the colors of the arrivals `0, …, v − 1`.

**Formalization Note** The process is defined by recursion on the arrival index, by the
construction itself and not by its properties. -/
def advColors {ℓ : ℕ} (A : OnlineColoringAlg) (code : ℕ → Fin ℓ → Bool) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | v + 1 => Function.update (advColors A code v) v (A.color v (stepGraph code (advColors A code v) v))

end OnlineColoringKYY


