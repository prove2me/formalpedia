-- Prove2me | Definitions.Def_fd03_policyValue
-- name    : fd03_policyValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:55:40.497385+00:00
-- url     : https://prove2.me/theorems/bcf939cd-fb0c-453e-93b5-21c0f5982b43
-- title:
--   Discounted value of a prescribed finite stopping policy
-- statement:
--   At maturity, the value of a stopping policy is the maturity reward. If the policy stops at an interior node, its value is that node's immediate exercise reward. If it continues, its value is the risk-neutral discounted value of the successor policies. This is defined syntactically even for policies later ruled ineligible; admissibility is checked separately.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191. Original policy-valuation fold underlying the optimal exercise calculation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_oneStepValue
import Definitions.Def_fd03_ExerciseTree
import Definitions.Def_fd03_StoppingPolicy

namespace FinancialDerivatives.FD03

/-- Price of a fixed (not necessarily admissible) exercise policy. -/
noncomputable def policyValue (m : BinomialMarket) :
    (n : ℕ) → ExerciseTree n → StoppingPolicy n → ℝ
  | 0, .maturity reward, .maturity => reward
  | _ + 1, .node _ reward _ _, .stop => reward
  | n + 1, .node _ _ up down, .continue pUp pDown =>
      oneStepValue m (policyValue m n up pUp)
                     (policyValue m n down pDown)

end FinancialDerivatives.FD03


