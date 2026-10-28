-- Prove2me | Definitions.Def_fd05_upperAbsorbingValue
-- name    : fd05_upperAbsorbingValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:13:29.977502+00:00
-- url     : https://prove2.me/theorems/25d7d067-e9ad-4cf7-b120-fe26c4e8f865
-- title:
--   Independent absorbing binomial pricing recursion
-- statement:
--   An independently defined dynamic valuation checks for barrier activation before discounting the risk-neutral two-child continuation value.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_oneStepValue
import Definitions.Def_fd05_upperTouch

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Backward price recursion with absorbing zero as soon as B is hit. -/
noncomputable def upperAbsorbingValue (m : BinomialMarket) (B : ℝ)
    (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    (n : ℕ) → ℕ → ℝ → Bool → ℝ
  | 0, t, S, hit =>
      if hit || upperTouch B S monitor t then 0 else g S
  | n + 1, t, S, hit =>
      if hit || upperTouch B S monitor t then 0
      else oneStepValue m
        (upperAbsorbingValue m B monitor g n (t + 1) (S * m.up) false)
        (upperAbsorbingValue m B monitor g n (t + 1) (S * m.down) false)

end FinancialDerivatives.FD05


