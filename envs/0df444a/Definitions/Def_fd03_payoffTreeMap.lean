-- Prove2me | Definitions.Def_fd03_payoffTreeMap
-- name    : fd03_payoffTreeMap
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:01:38.73637+00:00
-- url     : https://prove2.me/theorems/c84bbf89-0e56-4430-83b5-b5c7ab3952f2
-- title:
--   Apply a real payoff transformation at every terminal history
-- statement:
--   For a finite payoff tree and a real-valued function f, retain the entire up/down branching structure while replacing every terminal cashflow x by f(x). This supports signed scaling, payoff transformations and stock-dependent claims.
-- source:
--   Original finite-tree operation formalising the full-history payoff transformations used in Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed pp. 187–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Transform all terminal cash amounts without changing market histories. -/
noncomputable def payoffTreeMap (f : ℝ → ℝ) :
    (n : ℕ) → PayoffTree n → PayoffTree n
  | 0, .leaf x => .leaf (f x)
  | n + 1, .branch up down =>
      .branch (payoffTreeMap f n up) (payoffTreeMap f n down)

end FinancialDerivatives.FD03


