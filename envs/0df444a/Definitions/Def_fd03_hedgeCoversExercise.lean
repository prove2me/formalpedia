-- Prove2me | Definitions.Def_fd03_hedgeCoversExercise
-- name    : fd03_hedgeCoversExercise
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:04:34.695998+00:00
-- url     : https://prove2.me/theorems/9458ca47-5a56-409e-9763-1728263deca1
-- title:
--   Pathwise coverage of every permitted exercise claim
-- statement:
--   A hedge covers an exercise tree if its cash at every maturity leaf is at least the terminal reward, and at every earlier node where the holder may exercise its current portfolio wealth is at least the immediate reward. Both up and down successor strategies must satisfy the same condition. This represents the writer's exercise-contingent coverage obligation.
-- source:
--   Original finite-market writer-superhedging predicate derived from Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, equation (10.17), printed pp. 189–191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_HedgeTree
import Definitions.Def_fd03_ExerciseTree

namespace FinancialDerivatives.FD03

/-- Portfolio wealth covers the claim on every admissible exercise history. -/
def hedgeCoversExercise (m : BinomialMarket) :
    (n : ℕ) → ℝ → HedgeTree n → ExerciseTree n → Prop
  | 0, _, .terminal cash, .maturity reward => reward ≤ cash
  | n + 1, spot, .node shares bank upH downH,
      .node allowed reward upE downE =>
      (allowed = true → reward ≤ shares * spot + bank) ∧
      hedgeCoversExercise m n (spot * m.up) upH upE ∧
      hedgeCoversExercise m n (spot * m.down) downH downE

end FinancialDerivatives.FD03


