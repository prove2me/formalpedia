-- Prove2me | Definitions.Def_fd03_PayoffTree
-- name    : fd03_PayoffTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:54:06.320996+00:00
-- url     : https://prove2.me/theorems/6956af36-3ad8-4a17-b466-1eebc44608d4
-- title:
--   Finite full binary tree of terminal payoffs
-- statement:
--   A payoff tree of depth N associates a real-valued terminal payment with each of the 2ᴺ market histories. Its constructors are a single maturity payment at depth zero and an ordered pair of up/down subtrees at positive depth. Keeping histories distinct permits path-dependent contingent payments.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10, printed pp. 180–188, especially Figures 10.4 and equation (10.16). Original full-history indexed-tree abstraction.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD03

/-- Signed terminal payoffs indexed by a fixed finite binary-tree depth. -/
inductive PayoffTree : ℕ → Type where
  | leaf : ℝ → PayoffTree 0
  | branch {n : ℕ} : PayoffTree n → PayoffTree n → PayoffTree (n + 1)

end FinancialDerivatives.FD03


