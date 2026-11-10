-- Prove2me | Definitions.Def_NashOrTriangle_lower
-- name    : NashOrTriangle_lower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:28.578243+00:00
-- url     : https://prove2.me/theorems/f58d08cc-131c-48ba-8176-aaf1eb57e256
-- title:
--   Lower value $L(p)=\inf_b M(p,b)$
-- statement:
--   For a row mixture $p$,
--   $$
--   L(p) = \inf_{b \in B} M(p, b)
--   $$
--   is what $p$ guarantees to the row player whatever pure column strategy the opponent plays.
--
--   **Formalization Note** For a payoff function, a mixture $p$ and nonempty $B$ the values lie in $[0,1]$, so the infimum is a real number.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_NashOrTriangle_payoffCol

namespace NashOrTriangle

/-- `L(p) = inf_{b ∈ B} M(p, b)`: what the row mixture `p` guarantees to the row player against
every pure column strategy of the game.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4).

**Formalization Note** This is the real `⨅` of the family `b ↦ M(p, b)`; for a payoff function,
a mixture `p` and nonempty `B` the family is nonempty and bounded in `[0, 1]`, so `⨅` is the
true infimum. -/
noncomputable def lower {A B : Type*} (M : A → B → ℚ) (p : A →₀ ℚ) : ℝ :=
  ⨅ b, payoffCol M p b

end NashOrTriangle


