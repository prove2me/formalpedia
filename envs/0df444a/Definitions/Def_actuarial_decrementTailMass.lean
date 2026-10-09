-- Prove2me | Definitions.Def_actuarial_decrementTailMass
-- name    : actuarial_decrementTailMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:00:08.830329+00:00
-- url     : https://prove2.me/theorems/ce8c5681-c4f6-4260-979e-b52e6a761a5b
-- title:
--   Survival tail for countable death years with finite cause set
-- statement:
--   The probability of being in force at the beginning of year t is the tail sum of all annual cause masses from t onwards. Each policy has a finite realised termination year, but possible termination years are not uniformly bounded.
--
--   **Mathematical statement**
--
--   $$
--   S_t=\sum_{k\ge t}\sum_cw_{k,c}
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementYearMass

namespace ActuarialValuation

noncomputable def decrementTailMass {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) : ℝ :=
  ∑' k : ℕ, if t ≤ k then decrementYearMass w k else 0

end ActuarialValuation


