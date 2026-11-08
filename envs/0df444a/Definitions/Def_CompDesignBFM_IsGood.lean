-- Prove2me | Definitions.Def_CompDesignBFM_IsGood
-- name    : CompDesignBFM_IsGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:58.464182+00:00
-- url     : https://prove2.me/theorems/e755e23a-f070-4fb0-b014-4f6909c8f1a6
-- title:
--   Truthful, individually rational, budget-feasible deterministic mechanism
-- statement:
--   The conjunction of the four properties a deterministic mechanism must have: truthful, individually rational, paying only selected agents nonnegative amounts, and budget feasible for $B$. The goal theorem requires it of every realized mechanism.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_IsTruthful
import Definitions.Def_CompDesignBFM_IsIR
import Definitions.Def_CompDesignBFM_PaysWinnersOnly
import Definitions.Def_CompDesignBFM_IsBudgetFeasible

namespace CompDesignBFM

/-- The four properties a deterministic mechanism must have (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3): truthful,
individually rational, paying only winners nonnegative amounts, and budget feasible. -/
def IsGood {n : ℕ} (B : ℝ) (m : Mechanism n) : Prop :=
  IsTruthful m ∧ IsIR m ∧ PaysWinnersOnly m ∧ IsBudgetFeasible B m

end CompDesignBFM


