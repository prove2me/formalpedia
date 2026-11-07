-- Prove2me | Definitions.Def_OnlineColoringKYY_advEdge
-- name    : OnlineColoringKYY_advEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:31.403372+00:00
-- url     : https://prove2.me/theorems/ccc49bc9-3688-40bd-97bb-b34881695041
-- title:
--   Edge rule of the Section 4.2 adversary
-- statement:
--   Let $c(0), c(1), \dots$ be the player's online colors of the arrivals. In the adversary of Section 4.2, when vertex $j$ arrives it is joined to every earlier vertex $i < j$ that is **already paired** and whose base color is **not admissible** for $j$:
--   $$
--   i \sim j \iff i < j \text{ and } \exists\, w < j,\ w \ne i,\ c(w) = c(i),\ \varphi(i) = 2s + x_i(s) \notin X_j ,
--   $$
--   where $\varphi(i)$ is the base color fixed when $i$ was paired with $w$. No edges go to unpaired vertices. Only the colors of vertices that arrived before $j$ are consulted.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineColoringKYY_admits
import Definitions.Def_OnlineColoringKYY_baseColor

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The **edge rule of the adversary** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 =
PDF p.15: "they make all the previous paired vertices with base colors in `{1, …, 2ℓ} \ X_v`
adjacent to `v`. No edges are added to unpaired vertices").

For arrival indices `i < j` and the player's colors `cs` so far, `advEdge code cs i j` holds iff
vertex `i` is already paired when `j` arrives, that is some `w < j`, `w ≠ i`, has the same color
`cs w = cs i`, and the base color `φ(i) = baseColor code i w` is not in `X_j`.

**Formalization Note** Vertices are arrival indices in `ℕ`; `cs w` is the player's color of the
`w`-th arrival. Only colors of vertices `< j` are consulted. -/
def advEdge {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (cs : ℕ → ℕ) (i j : ℕ) : Prop :=
  i < j ∧ ∃ w, w < j ∧ w ≠ i ∧ cs w = cs i ∧ ¬ admits code j (baseColor code i w)

end OnlineColoringKYY


