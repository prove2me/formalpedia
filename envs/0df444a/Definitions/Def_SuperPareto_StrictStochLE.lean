-- Prove2me | Definitions.Def_SuperPareto_StrictStochLE
-- name    : SuperPareto_StrictStochLE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:19.851725+00:00
-- url     : https://prove2.me/theorems/cb646f38-37d0-4bc2-8b67-ffb189698f89
-- title:
--   §2.2, p.5 — strict stochastic dominance $X <_{\mathrm{st}} Y$
-- statement:
--   For random variables $X$ and $Y$ on $(\Omega,\mathcal F,P)$, $X$ is **strictly smaller than $Y$ in stochastic dominance**, written $X<_{\mathrm{st}}Y$, if
--
--   $$
--   P(X>x)<P(Y>x)\qquad\text{for all }x\in\mathbb R\text{ with }P(X>x)\in(0,1).
--   $$
--
--   This is stronger than "$X\le_{\mathrm{st}}Y$ and not $Y\le_{\mathrm{st}}X$": the survival functions must differ at every level where the survival function of $X$ is strictly between $0$ and $1$, including an atom of $X$ at its essential infimum. It is the order in the strict clause of the main theorem.
--
--   **Formalization Note** Probabilities are the $[0,\infty]$-valued measure $P$; the set of levels is exactly $\{x: 0<P(X>x)<1\}$.
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.2, p.5 (definition of <st)

import Mathlib

open MeasureTheory

namespace SuperPareto

/-- **Strict stochastic dominance** `X <st Y`. Chen, Embrechts, Wang, *An unexpected stochastic
dominance*, arXiv:2208.08471v4, §2.2, p.5: for random variables `X` and `Y`, `X <st Y` if
`P(X > x) < P(Y > x)` for all `x ∈ ℝ` satisfying `P(X > x) ∈ (0, 1)`.

**Formalization Note.** Every `x` with `P(X > x) ∈ (0, 1)` is covered, including an atom of `X` at
its essential infimum. Probabilities are those of the measure `P` (`ℝ≥0∞`-valued). -/
def StrictStochLE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ x : ℝ, 0 < P {ω | x < X ω} → P {ω | x < X ω} < 1 → P {ω | x < X ω} < P {ω | x < Y ω}

end SuperPareto


