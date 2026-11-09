-- Prove2me | Definitions.Def_MWCSherali_IsNonOppCut
-- name    : MWCSherali_IsNonOppCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:20.490936+00:00
-- url     : https://prove2.me/theorems/9e983552-76d3-4ea0-9c1c-785a690b4dd0
-- title:
--   Non-opposite cuts (Definition 2.1)
-- statement:
--   **Definition 2.1.** A function $P:\Delta_{k,n}\to[k+1]$ is a **non-opposite cut** if $P(x)\in L^{\mathrm{no}}(x)$ for every $x\in\Delta_{k,n}$: every terminal gets its own label, and every other point gets either the neutral label or a label of a coordinate in its support.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Definition 2.1, p.14

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_Lno

namespace MWCSherali

/-- **Non-opposite cuts.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3,
2026), Definition 2.1, p.14: "A function `P : Δ_{k,n} → [k+1]` is called a non-opposite cut if
`P(x) ∈ L^no(x)` for every `x ∈ Δ_{k,n}`."

**Formalization Note.** Labels are `Fin (k+1)` with the neutral label `k+1` as `Fin.last k`. -/
def IsNonOppCut {k n : ℕ} (P : Grid k n → Fin (k + 1)) : Prop :=
  ∀ x, P x ∈ Lno x

end MWCSherali


