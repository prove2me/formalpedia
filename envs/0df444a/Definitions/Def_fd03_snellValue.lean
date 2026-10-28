-- Prove2me | Definitions.Def_fd03_snellValue
-- name    : fd03_snellValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:55:55.169624+00:00
-- url     : https://prove2.me/theorems/ffcd0dbe-22b3-4673-a744-d430a06bb44f
-- title:
--   Finite Snell recursion for American and Bermudan option value
-- statement:
--   At maturity, the value is the contracted terminal reward. At a node without exercise permission, the value is the discounted risk-neutral continuation. When exercise is allowed, the value is the maximum of immediate exercise reward and discounted continuation. The recursion includes American, Bermudan and maturity-only European schedules.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, equation (10.17), Figure 10.7. Finite Snell-envelope-style restatement.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_oneStepValue
import Definitions.Def_fd03_ExerciseTree

namespace FinancialDerivatives.FD03

/-- Optimal stopping value from exercise reward and continuation. -/
noncomputable def snellValue (m : BinomialMarket) :
    (n : ℕ) → ExerciseTree n → ℝ
  | 0, .maturity reward => reward
  | n + 1, .node allowed reward up down =>
      let continuation := oneStepValue m (snellValue m n up)
                                              (snellValue m n down)
      match allowed with
      | true => max reward continuation
      | false => continuation

end FinancialDerivatives.FD03


