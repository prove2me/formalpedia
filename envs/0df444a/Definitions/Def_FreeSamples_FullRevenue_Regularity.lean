-- Prove2me | Definitions.Def_FreeSamples_FullRevenue_Regularity
-- name    : FreeSamples_FullRevenue_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:51:55.787175+00:00
-- url     : https://prove2.me/theorems/9b41c11f-ebb0-4be2-bc25-75560863d981
-- title:
--   Assumption 1: continuous and twice differentiable on positive variance
-- statement:
--   For a real function $F(m,v)$ of mean $m$ and positive variance $v$, twice differentiable means that its joint first derivative exists and is differentiable at every point of $\mathbb R\times(0,\infty)$. The source also states continuity on that domain. Assumption 1 requires this of both the optimized utility $U$ and the Bayes risk $BR$ derived from $u$:
--   $$U,BR:\mathbb R\times(0,\infty)\longrightarrow\mathbb R\quad\text{are continuous and twice differentiable}.$$
--   There is no continuity assumption on second derivatives and no growth condition. These are exactly the standing regularity assumptions for the drift and revenue statements.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.15, Assumption 1

import Definitions.Def_FreeSamples_FullRevenue_Utility

open MeasureTheory

namespace FreeSamples.FullRevenue

/-- Twice differentiable on the open positive-variance domain, without continuity
of the second derivative. The first derivative is the Fréchet derivative. -/
def TwiceDifferentiable (F : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Ioi 0) ∧
  ∀ z : ℝ × ℝ, 0 < z.2 →
    DifferentiableAt ℝ (Function.uncurry F) z ∧
    DifferentiableAt ℝ (fderiv ℝ (Function.uncurry F)) z

/-- Assumption 1, p.15, literally continuous and twice differentiable, not C². -/
def Assumption1 (u : ℝ → ℝ → ℝ) : Prop :=
  TwiceDifferentiable (U u) ∧ TwiceDifferentiable (BR u)

end FreeSamples.FullRevenue


