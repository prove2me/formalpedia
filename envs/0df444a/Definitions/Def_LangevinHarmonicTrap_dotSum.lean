-- Prove2me | Definitions.Def_LangevinHarmonicTrap_dotSum
-- name    : LangevinHarmonicTrap_dotSum
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T19:08:29.994646+00:00
-- url     : https://prove2.me/theorems/d890d081-b4df-428d-a9bc-4ce7799db889
-- title:
--   Componentwise dot product $u(t)\cdot w(t)$ of two time-dependent vectors
-- statement:
--   For a dimension $d$ and two families of real-valued functions of time $u_1,\dots,u_d$ and $w_1,\dots,w_d$, the Euclidean contraction at time $t$ is $$ u(t)\cdot w(t) \;=\; \sum_{i=1}^{d} u_i(t)\, w_i(t). $$ Taking $u = w = x$ (the position components) gives the squared displacement $r(t)^2$; taking $u = x$, $w = v$ gives $r(t)\cdot\dot r(t)$; taking $u = w = v$ gives $\dot r(t)^2$; and taking $u = x$, $w = f$ gives the projection $r(t)\cdot f(t)$ of the random force onto the position. All four quantities appearing in Langevin's derivation are instances of this single definition.
-- source:
--   Nonequilibrium Statistical Physics, Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, Trinity Term 2018, paper A15282W1, Question 1 (parts (a), (b), (d), (e)), Eq. (1); Langevin's 1908 method, cf. D. S. Lemons and A. Gythiel, Am. J. Phys. 65 (1997) 1079, https://doi.org/10.1119/1.18725

import Mathlib

open Finset

namespace LangevinHarmonicTrap

/-- The time-dependent Euclidean dot product of two `d`-component, vector-valued
functions of time:  `dotSum d u w t = ∑ i, (u i t) * (w i t)`.

With `x` the position components this gives `dotSum d x x t = r(t)²`,
`dotSum d x v t = r(t)·ṙ(t)` and `dotSum d v v t = ṙ(t)²`. -/
noncomputable def dotSum (d : ℕ) (u w : Fin d → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin d, u i t * w i t

end LangevinHarmonicTrap


