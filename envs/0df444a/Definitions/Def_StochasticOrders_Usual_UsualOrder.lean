-- Prove2me | Definitions.Def_StochasticOrders_Usual_UsualOrder
-- name    : StochasticOrders_Usual_UsualOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:46.330989+00:00
-- url     : https://prove2.me/theorems/62d803de-7bc8-4f9d-a0f1-7f956fc2888f
-- title:
--   The usual stochastic order
-- statement:
--   Let $X$ be a real-valued random variable on a probability space $(\Omega,\mu)$ and let $Y$ be
--   a real-valued random variable on a (possibly different) probability space $(\Omega',\nu)$. $X$
--   is said to be **smaller than $Y$ in the usual stochastic order**, written $X \le_{st} Y$, if
--
--   $$P\{X > x\} \le P\{Y > x\} \quad \text{for all } x \in (-\infty,\infty).$$
--
--   Roughly speaking, this says $X$ is less likely than $Y$ to take on large values, for every
--   threshold $x$ simultaneously. This is the weakest and most basic of the stochastic orders
--   studied in the book, and every later order in the series (hazard rate, likelihood ratio,
--   convex, and their multivariate generalizations) is compared against it or implies it.
--
--   **Formalization Note** `UsualOrder μ ν X Y` quantifies over every real `x` and compares the
--   two measures' values on the tail sets `{ω | x < X ω}` and `{ω | x < Y ω}` directly — `X` and
--   `Y` need not share a probability space, matching the book's treatment of `≤st` as a comparison
--   of two distributions rather than two jointly defined variables.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 3, Eq. (1.A.1)

import Mathlib

namespace StochasticOrders.Usual

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The usual stochastic order `X ≤st Y` (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 3, Eq. (1.A.1)): a random variable `X` on `(Ω, μ)` is smaller than a random variable `Y`
on a (possibly different) probability space `(Ω', ν)` in the usual stochastic order if
`P{X > x} ≤ P{Y > x}` for every real `x`. -/
def UsualOrder (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) : Prop :=
  ∀ x : ℝ, μ {ω | x < X ω} ≤ ν {ω | x < Y ω}

end StochasticOrders.Usual


