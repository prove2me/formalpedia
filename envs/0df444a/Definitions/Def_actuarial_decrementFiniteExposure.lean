-- Prove2me | Definitions.Def_actuarial_decrementFiniteExposure
-- name    : actuarial_decrementFiniteExposure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:01:44.07399+00:00
-- url     : https://prove2.me/theorems/39920885-3457-46c1-ad4a-6e506a7cb7db
-- title:
--   Discounted cause-weighted reserve surprise before a horizon
-- statement:
--   For every policy year before n, the insurer sums distinct cause-specific net amounts at risk multiplied by their corresponding centred termination surprises. Contributions after the realised termination year vanish because the policy is no longer in force.
--
--   **Mathematical statement**
--
--   $$
--   Z_n(k,d)=\sum_{t<n}\sum_c\rho_{t,c}I_{t,c}(k,d)
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation

namespace ActuarialValuation

noncomputable def decrementFiniteExposure {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (n k : ℕ) (d : C) : ℝ :=
  ∑ t ∈ Finset.range n, ∑ c : C,
    rho t c * decrementCauseInnovation w t c k d

end ActuarialValuation


