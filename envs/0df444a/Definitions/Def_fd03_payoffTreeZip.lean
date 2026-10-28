-- Prove2me | Definitions.Def_fd03_payoffTreeZip
-- name    : fd03_payoffTreeZip
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:01:49.137783+00:00
-- url     : https://prove2.me/theorems/54d36008-019d-4d8b-b1d8-24d7c769728d
-- title:
--   Combine two same-horizon payoff trees path by path
-- statement:
--   Given two payoff trees with identical horizon and branching histories, combine their respective terminal amounts using an arbitrary binary real operation. Addition yields the cashflows of a portfolio formed by holding both claims.
-- source:
--   Original finite-tree algebra for portfolios of terminal claims, motivated by Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed pp. 187–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Pointwise binary combination of two full-history terminal claims. -/
noncomputable def payoffTreeZip (f : ℝ → ℝ → ℝ) :
    (n : ℕ) → PayoffTree n → PayoffTree n → PayoffTree n
  | 0, .leaf x, .leaf y => .leaf (f x y)
  | n + 1, .branch xu xd, .branch yu yd =>
      .branch (payoffTreeZip f n xu yu) (payoffTreeZip f n xd yd)

end FinancialDerivatives.FD03


