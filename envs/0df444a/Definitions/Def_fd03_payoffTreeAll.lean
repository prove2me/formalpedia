-- Prove2me | Definitions.Def_fd03_payoffTreeAll
-- name    : fd03_payoffTreeAll
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:02:27.248251+00:00
-- url     : https://prove2.me/theorems/1c766f54-db17-4622-9c8b-df6aab6ebd73
-- title:
--   Pathwise terminal predicate on a full binary payoff tree
-- statement:
--   A property P of real terminal values holds throughout a depth-N payoff tree when P holds at its only leaf in depth zero and holds recursively for every leaf in both successor subtrees at positive depth. This will express the strictly positive stock condition along all histories.
-- source:
--   Original full-history tree property supporting positivity and order checks in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.1–10.4, printed pp. 180–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_PayoffTree

namespace FinancialDerivatives.FD03

/-- A real predicate holds at every leaf, including unrecombined histories. -/
def payoffTreeAll (P : ℝ → Prop) :
    (n : ℕ) → PayoffTree n → Prop
  | 0, .leaf x => P x
  | n + 1, .branch up down =>
      payoffTreeAll P n up ∧ payoffTreeAll P n down

end FinancialDerivatives.FD03


