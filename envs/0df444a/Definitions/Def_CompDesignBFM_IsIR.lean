-- Prove2me | Definitions.Def_CompDesignBFM_IsIR
-- name    : CompDesignBFM_IsIR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:07.422575+00:00
-- url     : https://prove2.me/theorems/e8bcebc0-ca46-4d82-96ea-73de02928ce6
-- title:
--   Individual rationality
-- statement:
--   A mechanism is **individually rational** if, at every nonnegative bid vector $b$, each selected agent is paid at least their bid: $p_i(b)\ge b_i$ for $i\in S(b)$. Under truthful bidding this says a selected agent never loses.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism

namespace CompDesignBFM

/-- Individual rationality (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3): a selected agent is paid at least their bid, at
every nonnegative bid vector. -/
def IsIR {n : ℕ} (m : Mechanism n) : Prop :=
  ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∀ i ∈ m.alloc b, b i ≤ m.pay b i

end CompDesignBFM


