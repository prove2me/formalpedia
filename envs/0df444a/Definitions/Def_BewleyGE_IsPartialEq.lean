-- Prove2me | Definitions.Def_BewleyGE_IsPartialEq
-- name    : BewleyGE_IsPartialEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:37.756983+00:00
-- url     : https://prove2.me/theorems/0a800256-fcc3-46dc-b39a-97670d4d3c8a
-- title:
--   Definition 1(i)–(ii) — optimal choices and an invariant distribution at given prices
-- statement:
--   At prices $(p,r)$, a tuple $(x,V,g,\mu)$ satisfies **Definition 1(i)–(ii)** if $x$ is the demand function, $V$ is the value function, $g$ is a savings policy satisfying (1), and $\mu$ is an invariant wealth distribution for $g$.
--
--   These are the agents' optimal behaviour and the stationary cross-section at given prices; the excess demand $\zeta(p,r)$ is computed from them.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Definition 1(i)–(ii), pp.8–9

import Mathlib
import Definitions.Def_BewleyGE_IsDemand
import Definitions.Def_BewleyGE_IsValueFunction
import Definitions.Def_BewleyGE_IsSavingsPolicy
import Definitions.Def_BewleyGE_IsInvariantDist

open MeasureTheory

namespace BewleyGE

/-- **Optimal behaviour and invariance at given prices**: clauses (i) and (ii) of Definition 1.
Light, arXiv:1906.06810v2, Definition 1(i)–(ii), pp.8–9.

At prices `(p, r)`: `x` is the demand function, `V` the value function (bounded fixed point of
`T`), `g` a savings policy satisfying (1), and `μ` an invariant wealth distribution, `μ = Mμ`.
These are the objects from which the excess demand `ζ(p, r)` of §3.1 is computed. -/
structure IsPartialEq {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ)
    (x : ℝ → Fin n → ℝ) (V g : ℝ → ℝ) (μ : Measure ℝ) : Prop where
  /-- `x` is the demand function at `p`. -/
  demand : IsDemand E p x
  /-- `V` is the value function at `(p, r)`. -/
  value : IsValueFunction E p r x V
  /-- `g` satisfies equation (1). -/
  policy : IsSavingsPolicy E p r x V g
  /-- `μ ∈ P(A(p, r))` and `μ = Mμ`. -/
  invariant : IsInvariantDist E p r g μ

end BewleyGE


