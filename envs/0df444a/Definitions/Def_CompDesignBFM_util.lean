-- Prove2me | Definitions.Def_CompDesignBFM_util
-- name    : CompDesignBFM_util
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:11.874592+00:00
-- url     : https://prove2.me/theorems/b884a876-8e01-41d0-9ce9-e81caf1cf08a
-- title:
--   Utility of an agent
-- statement:
--   The **utility** of agent $i$ with true cost $t$ at bids $b$ is
--
--   $$u_i(b)=\begin{cases}p_i(b)-t & i\in S(b),\\ p_i(b) & i\notin S(b).\end{cases}$$
--
--   Truthfulness compares this quantity across the agent's own bids.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism

namespace CompDesignBFM

/-- The utility of agent `i` with true cost `t` at the bid vector `b`
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3): the payment minus the cost when selected, and the payment otherwise. -/
noncomputable def util {n : ℕ} (m : Mechanism n) (i : Fin n) (t : ℝ) (b : Fin n → ℝ) : ℝ :=
  if i ∈ m.alloc b then m.pay b i - t else m.pay b i

end CompDesignBFM


