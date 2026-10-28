-- Prove2me | Definitions.Def_fd02_toFD01PriceSystem
-- name    : fd02_toFD01PriceSystem
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:51:05.402015+00:00
-- url     : https://prove2.me/theorems/7d574c78-30be-4ddb-a2f2-f242efe6b461
-- title:
--   Construct the FD-01 state-price system from positive risk-neutral weights
-- statement:
--   Given a two-state market and proof that its unique up weight q lies strictly between zero and one, construct an FD-01 FinitePriceSystem on Bool with positive Arrow-state prices q/R and (1-q)/R and discount factor 1/R. No-arbitrage implies the required two inequalities through separate theorems T12 and T13. The constructor itself does not assume that the derivative price is correct.
-- source:
--   Original derived construction from Wilmott, Howison and Dewynne (1995), §10.1–10.2, printed pp. 182–184, equations (10.2), (10.4) and (10.8). https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp

namespace FinancialDerivatives.FD02

/-- Positive two-state martingale weights construct the FD-01 price system. -/
noncomputable def toFD01PriceSystem (m : TwoStateMarket)
    (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1) :
    FinancialDerivatives.FD01.FinitePriceSystem Bool where
  statePrice := fun ω => match ω with
    | true => riskNeutralUp m / m.growth
    | false => (1 - riskNeutralUp m) / m.growth
  statePrice_nonneg := by
    intro ω
    cases ω with
    | false =>
        exact div_nonneg (sub_nonneg.mpr (le_of_lt hq1)) (le_of_lt m.growth_pos)
    | true =>
        exact div_nonneg (le_of_lt hq0) (le_of_lt m.growth_pos)
  discount := 1 / m.growth
  discount_pos := div_pos zero_lt_one m.growth_pos
  statePrice_sum := by
    simp only [Fintype.sum_bool]
    ring

end FinancialDerivatives.FD02


