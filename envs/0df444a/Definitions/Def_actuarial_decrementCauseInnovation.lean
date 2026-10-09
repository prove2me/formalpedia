-- Prove2me | Definitions.Def_actuarial_decrementCauseInnovation
-- name    : actuarial_decrementCauseInnovation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:01:04.172407+00:00
-- url     : https://prove2.me/theorems/256a3c83-c23b-4b5d-ba47-2cafd8ce8774
-- title:
--   Centred indicator for a named cause in one policy year
-- statement:
--   The scenario contains both its termination year k and the actual cause d. The year-t, cause-c innovation subtracts the conditional incidence of that cause from its observed incidence while the policy remains active. Distinct causes in the same year are dependent through exclusivity.
--
--   **Mathematical statement**
--
--   $$
--   I_{t,c}(k,d)=\mathbf1_{\{(k,d)=(t,c)\}}-(w_{t,c}/S_t)\mathbf1_{\{k\ge t\}}
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementTailMass

namespace ActuarialValuation

noncomputable def decrementCauseInnovation {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c : C) (k : ℕ) (d : C) : ℝ := by
  classical
  exact (if k = t ∧ d = c then 1 else 0) -
    (w t c / decrementTailMass w t) * (if t ≤ k then 1 else 0)

end ActuarialValuation


