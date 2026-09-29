-- Prove2me | Definitions.Def_StochasticOrders_MeanResidualLife_DMRL
-- name    : StochasticOrders_MeanResidualLife_DMRL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:40.413986+00:00
-- url     : https://prove2.me/theorems/909034f6-b035-4f90-8b97-9ac810614991
-- title:
--   Decreasing mean residual life (DMRL)
-- statement:
--   A random variable $X$ on $(\Omega,\mu)$ is said to be **DMRL** (decreasing mean residual
--   life) if its mean residual life function $m$ is decreasing in $t$.
--
--   **Formalization Note** `DMRL μ X := Antitone (mrl μ X)`, the weak (non-strict) monotone
--   sense the book uses throughout for "increasing"/"decreasing".
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 87

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl

namespace StochasticOrders.MeanResidualLife

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random variable `X` on `(Ω, μ)` is DMRL (decreasing mean residual life; Shaked &
Shanthikumar, *Stochastic Orders*, Springer 2007, p. 87) if its mean residual life function `m` is
decreasing (in the weak, non-strict sense used throughout the book for "increasing"/"decreasing"). -/
def DMRL (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Antitone (mrl μ X)

end StochasticOrders.MeanResidualLife


