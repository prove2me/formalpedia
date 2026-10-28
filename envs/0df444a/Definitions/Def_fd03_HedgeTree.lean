-- Prove2me | Definitions.Def_fd03_HedgeTree
-- name    : fd03_HedgeTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:00:13.853245+00:00
-- url     : https://prove2.me/theorems/28d892c4-87a1-42e3-996c-0f84b8619d42
-- title:
--   Finite tree of adapted stock-bank holdings and terminal wealth
-- statement:
--   At each pre-maturity market node a strategy records a real stock holding and a real bank-account balance, with separate successor strategies after the up/down move. At maturity the strategy records its realised cash wealth. The tree structure ensures decisions depend only on the history so far.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189. Original finite adapted trading strategy tree with terminal cash account.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD03

/-- Adapted stock/bank holdings at each interior node and liquidated cash at maturity. -/
inductive HedgeTree : ℕ → Type where
  | terminal : ℝ → HedgeTree 0
  | node {n : ℕ} : ℝ → ℝ → HedgeTree n → HedgeTree n →
      HedgeTree (n + 1)

end FinancialDerivatives.FD03


