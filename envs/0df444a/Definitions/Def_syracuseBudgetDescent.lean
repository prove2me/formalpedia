-- Prove2me | Definitions.Def_syracuseBudgetDescent
-- name    : syracuseBudgetDescent
-- status  : Definition
-- author  : @Siyuan Chen
-- created : 2026-11-23T13:08:02.627692+00:00
-- url     : https://prove2.me/theorems/34913c49-d1fb-487d-8f21-524f8f68a993
-- title:
--   Variable-length Syracuse descent certificate with a fixed exponent budget
-- statement:
--   For a residue representative and a total power-of-two exponent budget, this Boolean search tests for a Syracuse descent certificate. At each row it tries the largest available divisor allowed by the remaining budget. If the terminal quotient does not fall below the starting representative, the search continues with the exact odd quotient when that row fits the budget.
-- source:
--   Original executable search based on the terminal-divisor criterion of CollatzFrontier.syracuse_terminal_budget_of_descent, https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c.

import Mathlib.Data.Nat.Basic

namespace SyracuseBudget

/-- Count up to `fuel` factors of two in `x`. -/
def valuation : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
    if x % 2 = 0 then valuation fuel (x / 2) + 1 else 0

def exponent (x : ℕ) : ℕ := valuation 64 (3 * x + 1)

def quotient (x : ℕ) : ℕ := (3 * x + 1) / 2 ^ exponent x

/-- Try a terminal divisor at each row. Continue only when an exact step
    with an odd quotient fits the remaining budget. -/
def search : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, x, remaining, start =>
    decide ((3 * x + 1) / 2 ^ min (exponent x) remaining < start)
  | fuel + 1, x, remaining, start =>
    decide ((3 * x + 1) / 2 ^ min (exponent x) remaining < start) ||
      (decide (exponent x ≤ remaining) &&
        (decide (quotient x % 2 = 1) &&
          search fuel (quotient x) (remaining - exponent x) start))

end SyracuseBudget

/-- Test for a uniform Syracuse descent certificate on the class of `r`
    modulo `2 ^ budget`, allowing any prefix length up to `budget`. -/
def syracuseBudgetDescent (budget r : ℕ) : Bool :=
  SyracuseBudget.search budget r budget r


