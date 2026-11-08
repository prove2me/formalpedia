-- Prove2me | Definitions.Def_CompDesignBFM_IsBudgetFeasible
-- name    : CompDesignBFM_IsBudgetFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:11.404196+00:00
-- url     : https://prove2.me/theorems/f8ec2f59-bfab-4947-849e-df0a18f5d380
-- title:
--   Budget feasibility
-- statement:
--   A mechanism is **budget feasible** for the budget $B$ if $\sum_{i\in S(b)}p_i(b)\le B$ at every nonnegative bid vector $b$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism

namespace CompDesignBFM

/-- Budget feasibility (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3): the payments to the selected agents sum to at most `B`
at every nonnegative bid vector. -/
def IsBudgetFeasible {n : ℕ} (B : ℝ) (m : Mechanism n) : Prop :=
  ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∑ i ∈ m.alloc b, m.pay b i ≤ B

end CompDesignBFM


