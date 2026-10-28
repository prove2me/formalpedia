-- Prove2me | Definitions.Def_fd03_payoffTreeLe
-- name    : fd03_payoffTreeLe
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:02:05.300115+00:00
-- url     : https://prove2.me/theorems/fb63aa39-2fad-4d99-9752-c79832351c4a
-- title:
--   Pathwise order on signed terminal payoff trees
-- statement:
--   Two payoff trees of equal horizon are ordered when the first claim's cash payment is no greater than the second at every possible up/down terminal history. Both child subtrees must satisfy the relation at every interior node.
-- source:
--   Original pathwise inequality interface for binomial contingent claims, motivated by Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed pp. 187–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- Every terminal history of the first tree pays no more than the second. -/
def payoffTreeLe :
    (n : ℕ) → PayoffTree n → PayoffTree n → Prop
  | 0, .leaf x, .leaf y => x ≤ y
  | n + 1, .branch xu xd, .branch yu yd =>
      payoffTreeLe n xu yu ∧ payoffTreeLe n xd yd

end FinancialDerivatives.FD03


