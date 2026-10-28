-- Prove2me | Definitions.Def_fd03_oneStepValue
-- name    : fd03_oneStepValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:54:42.055116+00:00
-- url     : https://prove2.me/theorems/1bb146ca-3ed7-49b9-a60a-ef73a96c8914
-- title:
--   One-step discounted risk-neutral cashflow valuation
-- statement:
--   At a binomial node, the current value of signed up- and down-state cash payments (Vᵤ,Vₔ) is (qVᵤ+(1-q)Vₔ)/R, where q=(R-d)/(u-d). This is a definition of the valuation operator; a separate theorem must prove replication and arbitrage uniqueness.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189, equation (10.16). Original explicit operator underlying backward induction.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_upWeight

namespace FinancialDerivatives.FD03

/-- The discounted two-state value at one binomial market node. -/
noncomputable def oneStepValue
    (m : BinomialMarket) (upValue downValue : ℝ) : ℝ :=
  (upWeight m * upValue + (1 - upWeight m) * downValue) / m.growth

end FinancialDerivatives.FD03


