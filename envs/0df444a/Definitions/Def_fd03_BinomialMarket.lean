-- Prove2me | Definitions.Def_fd03_BinomialMarket
-- name    : fd03_BinomialMarket
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:53:58.567737+00:00
-- url     : https://prove2.me/theorems/5cb117d3-37af-4240-882e-9e76f4056b0c
-- title:
--   Strictly arbitrage-free repeated binomial market
-- statement:
--   A dividend-free stock begins at a strictly positive spot price S₀ and changes by a strictly positive down multiplier d or up multiplier u per period. The bank grows by factor R. The market parameters obey 0 < d < R < u, so every descendant stock price remains positive and every step admits a unique positive two-state pricing measure.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 10 §§10.1–10.3, printed pp. 180–188, doi:10.1017/CBO9780511812545. Original derived strict-positive finite-market definition.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD03

/-- Strictly positive stock and nondegenerate no-arbitrage binomial step. -/
structure BinomialMarket where
  initialSpot : ℝ
  down : ℝ
  up : ℝ
  growth : ℝ
  initialSpot_pos : 0 < initialSpot
  down_pos : 0 < down
  down_lt_growth : down < growth
  growth_lt_up : growth < up

end FinancialDerivatives.FD03


