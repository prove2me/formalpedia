-- Prove2me | Definitions.Def_actuarial_decrementAnnualRisk
-- name    : actuarial_decrementAnnualRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:02:22.748791+00:00
-- url     : https://prove2.me/theorems/91a6f79f-5285-4638-a697-1366af73f996
-- title:
--   Annual competing-decrement risk allocation including covariance
-- statement:
--   The first component is the cause-weighted squared net amount at risk. The second subtracts a squared conditional-mean adjustment, accounting for negative covariance between mutually exclusive termination causes in the same policy year. It is not the naive sum of single-decrement variances.
--
--   **Mathematical statement**
--
--   $$
--   A_t=\sum_cw_{t,c}\rho_{t,c}^2-(\sum_cw_{t,c}\rho_{t,c})^2/S_t
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementTailMass

namespace ActuarialValuation

noncomputable def decrementAnnualRisk {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (t : ℕ) : ℝ :=
  (∑ c : C, w t c * (rho t c) ^ 2) -
    (∑ c : C, w t c * rho t c) ^ 2 / decrementTailMass w t

end ActuarialValuation


