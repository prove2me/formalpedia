-- Prove2me | Definitions.Def_PorteusGenSS_IsOrderingCost
-- name    : PorteusGenSS_IsOrderingCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:13:53.956707+00:00
-- url     : https://prove2.me/theorems/61d53be6-ac92-4806-99ee-3952e639cff9
-- title:
--   Concave increasing ordering cost with $c(0)=0$
-- statement:
--   An **ordering cost** is a function $c$ giving the cost $c(z)$ of ordering $z\ge0$ units, which is concave and increasing on $[0,\infty)$ with $c(0)=0$. Setup costs (a jump at $0$), quantity discounts and learning effects are all covered.
--
--   **Formalization Note** "Increasing" is read as nondecreasing. Values of $c$ on $(-\infty,0)$ are never used. No continuity at $0$ is required.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412

import Mathlib

namespace PorteusGenSS

/-- **Concave increasing ordering cost with c(0) = 0 (§II).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412: "Let c denote the concave increasing ordering cost function; i.e., the cost
of ordering (producing) z (z ≥ 0) units is c(z). We assume c(0) = 0."

`IsOrderingCost c` says `c` is concave and nondecreasing on `[0, ∞)` and `c 0 = 0`.

**Formalization Note.** "Increasing" is read as nondecreasing (`MonotoneOn`); the paper never
defines it, and nondecreasing is the weaker requirement, so every strictly increasing cost is
covered. `c` is only ever evaluated at arguments `≥ 0`; its values on `(−∞, 0)` are
irrelevant. No continuity at `0` is required: a setup cost (a jump at `0`) is allowed, as in the
paper's example on p. 412. -/
def IsOrderingCost (c : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici 0) c ∧ MonotoneOn c (Set.Ici 0) ∧ c 0 = 0

end PorteusGenSS


