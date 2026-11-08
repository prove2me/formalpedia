-- Prove2me | Definitions.Def_CompDesignBFM_thresholdMech
-- name    : CompDesignBFM_thresholdMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:18.623102+00:00
-- url     : https://prove2.me/theorems/9af84b61-6a57-4e53-851a-006c207ceab7
-- title:
--   Threshold mechanism
-- statement:
--   The **threshold mechanism** of an allocation rule $A$ selects $A(b)$, pays every selected agent the threshold $\tau_i(b_{-i})$, and pays every other agent zero.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 2.1, p.12 (PDF 14)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_tau

namespace CompDesignBFM

/-- The threshold mechanism of an allocation rule (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 2.1, p.12, PDF 14): every selected agent
is paid their threshold (5) and every other agent is paid zero. -/
noncomputable def thresholdMech {n : ℕ} (A : (Fin n → ℝ) → Finset (Fin n)) : Mechanism n where
  alloc := A
  pay := fun b i => if i ∈ A b then tau A b i else 0

end CompDesignBFM


