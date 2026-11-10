-- Prove2me | Definitions.Def_NashOrTriangle_upper
-- name    : NashOrTriangle_upper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:20.036219+00:00
-- url     : https://prove2.me/theorems/2d932ed0-5d2a-4a66-bc68-215c388d1de3
-- title:
--   Upper value $U(q)=\sup_a M(a,q)$
-- statement:
--   For a column mixture $q$,
--   $$
--   U(q) = \sup_{a \in A} M(a, q)
--   $$
--   is the most the row player can get against $q$; the supremum runs over all pure row strategies of the game, not only the known ones.
--
--   **Formalization Note** For a payoff function, a mixture $q$ and nonempty $A$ the values $M(a, q)$ lie in $[0,1]$, so the supremum is a real number; every theorem of the mission is in this situation.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_NashOrTriangle_payoffRow

namespace NashOrTriangle

/-- `U(q) = sup_{a ∈ A} M(a, q)`: the most the row player can get against the column mixture
`q`, the supremum over **all** pure row strategies of the game.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4).

**Formalization Note** This is the real `⨆` of the family `a ↦ M(a, q)`. When `M` is a payoff
function (values in `[0, 1]`), `q` is a mixture and `A` is nonempty, the family is nonempty
and bounded in `[0, 1]`, so `⨆` is the true supremum; every theorem of the mission assumes
this. -/
noncomputable def upper {A B : Type*} (M : A → B → ℚ) (q : B →₀ ℚ) : ℝ :=
  ⨆ a, payoffRow M a q

end NashOrTriangle


