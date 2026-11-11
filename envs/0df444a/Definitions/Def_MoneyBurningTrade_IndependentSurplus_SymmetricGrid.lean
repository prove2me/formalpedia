-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_SymmetricGrid
-- name    : MoneyBurningTrade_IndependentSurplus_SymmetricGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:23.42811+00:00
-- url     : https://prove2.me/theorems/75e69e39-ac11-46f0-aa34-01a55231c9e9
-- title:
--   Equation (20) — symmetric geometric grid
-- statement:
--   For an integer $k\ge2$, put $n=2k$ and $\delta=1/(100n)$. The symmetric grid is
--
--   $$q_0=0,\quad q_n=1,\quad q_k=\tfrac12,\quad q_i=\tfrac12-\delta^i\ (1\le i<k),\quad q_i=\tfrac12+\delta^{2k-i}\ (k<i<n).$$
--
--   Its normalization and condition (19) are conclusions of Lemma 4.6. The formula is defined without assuming either result. A constant extension beyond index $n$ has no role in the statements.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §4.2, equation (20), printed p. 26 (PDF p. 27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- §4.2 fixes n=2k and δ=1/(100n). -/
noncomputable def symmetricDelta (k : ℕ) : ℝ := 1 / (100 * (2 * k : ℕ))

/-- Equation (20), defined on 0,...,2k. Values beyond the final endpoint
are an irrelevant constant extension. -/
noncomputable def symmetricGrid (k : ℕ) : Grid where
  n := 2 * k
  q := fun i =>
    if i = 0 then 0 else if i < k then 1 / 2 - symmetricDelta k ^ i
    else if i = k then 1 / 2
    else if i < 2 * k then 1 / 2 + symmetricDelta k ^ (2 * k - i)
    else 1

end MoneyBurningTrade.IndependentSurplus


