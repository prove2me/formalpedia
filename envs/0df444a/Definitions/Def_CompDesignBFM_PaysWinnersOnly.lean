-- Prove2me | Definitions.Def_CompDesignBFM_PaysWinnersOnly
-- name    : CompDesignBFM_PaysWinnersOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:16.858725+00:00
-- url     : https://prove2.me/theorems/752ec418-af23-4503-886d-73606e686cbe
-- title:
--   Nonnegative payments to selected agents only
-- statement:
--   At every nonnegative bid vector, all payments are nonnegative and agents outside $S(b)$ are paid zero. This is the payment convention of the model: the mechanism pays $p_i(b)\ge0$ to each agent $i\in S(b)$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism

namespace CompDesignBFM

/-- Payments are nonnegative and only selected agents are paid (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3: "pays
`pᵢ(b) ≥ 0` to each agent `i ∈ S`"). -/
def PaysWinnersOnly {n : ℕ} (m : Mechanism n) : Prop :=
  ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∀ i, 0 ≤ m.pay b i ∧ (i ∉ m.alloc b → m.pay b i = 0)

end CompDesignBFM


