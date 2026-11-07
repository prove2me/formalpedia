-- Prove2me | Definitions.Def_OnlineColoringKYY_IsProper
-- name    : OnlineColoringKYY_IsProper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:08.409655+00:00
-- url     : https://prove2.me/theorems/6431002a-3b4b-41ba-a2da-60ebba6ca56c
-- title:
--   Proper online coloring algorithm
-- statement:
--   A deterministic online coloring algorithm $A$ is **proper** if on every input it assigns adjacent vertices different colors: for every $n$, every graph $G$ on $\{0, \dots, n-1\}$ and every edge $uv$ of $G$,
--   $$
--   c_A^G(u) \ne c_A^G(v).
--   $$
--   This is the requirement of Definition 3.1 that the color of each new vertex "differs from the colors of all adjacent vertices". It is imposed on every input, not only on a particular one; without it the constant algorithm would use a single color.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 (PDF p.12)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run

set_option autoImplicit false

namespace OnlineColoringKYY

/-- An online coloring algorithm is **proper** if on every input graph, of every size, it gives
adjacent vertices different colors (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 = PDF p.12: "we must
assign a color `c(v) ∈ ℕ` that differs from the colors of all adjacent vertices").

**Formalization Note** Properness is required on every input (every `n` and every graph on
`Fin n`), as Definition 3.1 requires of an online coloring algorithm. -/
def IsProper (A : OnlineColoringAlg) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n), G.Adj u v → run A G u ≠ run A G v

end OnlineColoringKYY


