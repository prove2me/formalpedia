-- Prove2me | Definitions.Def_fd03_constantPayoffTree
-- name    : fd03_constantPayoffTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:02:17.495093+00:00
-- url     : https://prove2.me/theorems/86a3eceb-655a-4172-a032-263bf6de749d
-- title:
--   Constant signed terminal claim at every history
-- statement:
--   For any real cash amount c and finite horizon N, construct a payoff tree paying c on every path. Its risk-neutral value must be c discounted by the bank growth factor to the Nth power.
-- source:
--   Original full-tree constant payoff used to prove the discount-factor check of equation (10.16), Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed p. 188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- The same signed terminal cash payment on each of the 2^n histories. -/
noncomputable def constantPayoffTree :
    (n : ℕ) → ℝ → PayoffTree n
  | 0, c => .leaf c
  | n + 1, c => .branch (constantPayoffTree n c) (constantPayoffTree n c)

end FinancialDerivatives.FD03


