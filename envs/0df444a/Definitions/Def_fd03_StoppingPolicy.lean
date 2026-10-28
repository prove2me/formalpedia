-- Prove2me | Definitions.Def_fd03_StoppingPolicy
-- name    : fd03_StoppingPolicy
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:54:18.838844+00:00
-- url     : https://prove2.me/theorems/d05d23c7-804c-4b40-94d4-3ca4e749c120
-- title:
--   Nonanticipating stopping policy on a finite binary tree
-- statement:
--   A stopping policy at maturity has no further decision. At any earlier node the holder either stops now or continues, in which case a separate policy is prescribed for the up and down successors. This representation is adapted to the market tree and cannot depend on future stock moves before they occur.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191. Original finite nonanticipating stopping-policy datatype for equation (10.17).

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD03

/-- Holder stop/continue choices, branching only after the next move. -/
inductive StoppingPolicy : ℕ → Type where
  | maturity : StoppingPolicy 0
  | stop {n : ℕ} : StoppingPolicy (n + 1)
  | continue {n : ℕ} : StoppingPolicy n → StoppingPolicy n →
      StoppingPolicy (n + 1)

end FinancialDerivatives.FD03


