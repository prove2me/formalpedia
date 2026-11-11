-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_GrowthFactor
-- name    : MoneyBurningTrade_IndependentSurplus_GrowthFactor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:21.102303+00:00
-- url     : https://prove2.me/theorems/764f63c5-bd67-416d-9834-bc1edb0332ff
-- title:
--   Equation (17) — growth factor
-- statement:
--   For a normalized grid $q$ of length $n\ge2$ and $0<\tau<L/2$, the growth factor is
--
--   $$\Gamma=1+\max_{1\le i<j\le n}\frac{q_{j-1}-q_i+2\tau}{q_j-q_{i-1}-\tau\mathbf1_{i>1}-\tau\mathbf1_{j<n}}.$$
--
--   The finite maximum is represented by a real supremum. Its index set is nonempty, and the source's slack condition makes every denominator positive. Positivity and the resulting mechanism's validity are conclusions of Lemma 4.3.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.3, equation (17), printed p. 24 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Equation (17). Under IsGrid and 0<τ<minGap/2 the finite set is nonempty
(pair i=1,j=2), all denominators are positive, and its supremum is its maximum. -/
noncomputable def growthFactor (G : Grid) (τ : ℝ) : ℝ :=
  1 + sSup {v : ℝ | ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ G.n ∧
    v = (G.q (j - 1) - G.q i + 2 * τ) /
      (G.q j - G.q (i - 1) - (if 1 < i then τ else 0) -
        (if j < G.n then τ else 0))}

end MoneyBurningTrade.IndependentSurplus


