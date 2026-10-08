-- Prove2me | Definitions.Def_LRC_GW
-- name    : LRC_GW
-- status  : Definition
-- author  : @Whunt003
-- created : 2026-10-06T01:04:24.459085+00:00
-- url     : https://prove2.me/theorems/6dbec7df-ea00-4338-9a8c-2c7dc9173c41
-- title:
--   Goddyn–Wong acceleration window
-- statement:
--   For natural numbers $n,r,m$, the Goddyn–Wong window condition asserts that every integer $b$ with $n-r\le b<m(n-r)$ has a common factor with $r$. This predicate expresses the individual acceleration criterion used in the Lonely Runner problem.
-- source:
--   Wade Hunter, AI-assisted Lonely Runner research, lean/LonelyRunner/SeparatedReplacements.lean, definition GW; https://github.com/huntrontrakkr/lonely-runner

import Mathlib.Data.Nat.GCD.Basic
namespace LonelyRunner.SeparatedReplacements
def GW (n r m : ℕ) : Prop :=
  ∀ b : ℕ, n-r ≤ b → b < m*(n-r) → ¬ Nat.Coprime r b
end LonelyRunner.SeparatedReplacements


