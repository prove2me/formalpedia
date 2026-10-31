-- Prove2me | Definitions.Def_ReservationPolicy_investEfforts
-- name    : ReservationPolicy_investEfforts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:18.673007+00:00
-- url     : https://prove2.me/theorems/0da0f23d-13d3-4ab5-a616-8916dec3d64a
-- title:
--   Efforts of an investing student with uncertain admission
-- statement:
--   For a cutoff $d$, the efforts available to a student who invests are
--   $$
--   \{e\ge 0:\ 0<\rho(e,d)<1\}.
--   $$
--   This is the regime in which the paper's formula (4) for the admission probability holds, and best responses are taken within it.
--
--   **Formalization Note** The paper's upper bound $e\le1$ is dropped because equilibrium effort can exceed $1$: at $k=\tfrac13,\phi=\tfrac12,\alpha=\tfrac1{25},z=\tfrac15$ it is $\tfrac{1740}{1589}$. The requirement $0<\rho<1$ makes the best response of the paper's payoffs, which use the linear (4), agree with the first-order conditions the paper solves. Allowing every $e\ge0$ with the clipped probability changes the game: a student with a small interior admission chance can do better with $e=0$, and the equilibrium of the paper then does not exist.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), pp.8–11

import Mathlib
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The efforts open to an investing student at cutoff `d`: `0 ≤ e`, with admission probability
strictly between `0` and `1`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), pp.8–11 (PDF 8–11).

**Formalization Note** Two readings, both declared in the theorems that use this set.
(1) The paper's bound `e ≤ 1` (p.8) is dropped: at `k = 1/3`, `ϕ = 1/2`, `α = 1/25`, `z = 1/5` the
equilibrium effort is `1740/1589 > 1`, so the bound would make Proposition 1 false.
(2) The paper's payoffs are written with the linear probability (4), which holds exactly on this
set, and p.9 keeps probabilities between `0` and `1`. Best responses range over this set, so
that equilibria are the solutions of the paper's first-order conditions. Against all efforts
`e ≥ 0` and the clipped probability, effort `0` can beat the interior effort, and the paper's
equilibrium fails to exist: see the theorems' difference lists. -/
def investEfforts (d : ℝ) : Set ℝ :=
  {e | 0 ≤ e ∧ 0 < admitProb e d ∧ admitProb e d < 1}

end ReservationPolicy


