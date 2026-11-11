-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_SeparationGrid
-- name    : MoneyBurningTrade_IndependentSurplus_SeparationGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:12.242207+00:00
-- url     : https://prove2.me/theorems/e6f148e2-9ad6-4228-8ef0-28af27a4baac
-- title:
--   Definition 4.4 — separation grid
-- statement:
--   A normalized grid of length $n\ge4$ is a separation grid with slack $\tau$ if there exists $\delta$ such that
--
--   $$0<\delta\le\frac1{100n},\qquad0<\tau\le\frac{\delta L}{100},\qquad q_{j-1}-q_i\le4\delta(q_j-q_{i-1})\ (1\le i<j\le n).$$
--
--   Here $L$ is the minimum consecutive gap. The small-slack and complete pair-index conditions are retained exactly. This predicate is the standing hypothesis of Lemma 4.5 and Claims A.1–A.2.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Definition 4.4, equation (19), printed p. 25 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Definition 4.4, including n≥4 and the source's existential δ. -/
def IsSeparationGrid (G : Grid) (τ : ℝ) : Prop :=
  IsGrid G ∧ 4 ≤ G.n ∧ ∃ δ : ℝ,
    0 < δ ∧ δ ≤ 1 / (100 * (G.n : ℝ)) ∧
    0 < τ ∧ τ ≤ δ * minGap G / 100 ∧ gridCondition G δ

end MoneyBurningTrade.IndependentSurplus


