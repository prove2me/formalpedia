-- Prove2me | Definitions.Def_actuarial_wholeLifeCompleteInnovation
-- name    : actuarial_wholeLifeCompleteInnovation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:01:28.711987+00:00
-- url     : https://prove2.me/theorems/ba6d3607-be6a-44c1-b1e4-d60a3da1529e
-- title:
--   Pathwise stabilised complete-life mortality reserve surprise
-- statement:
--   For a finite realised death year k, the complete-life centred loss is already attained when the truncation first includes that event. The death year varies unboundedly over the countable outcome space, so this construction has no common deterministic terminal horizon.
--
--   **Mathematical statement**
--
--   $$
--   Z_\infty(k)=\sum_{t=0}^k\rho_tI_t(k)
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation

namespace ActuarialValuation

noncomputable def wholeLifeCompleteInnovation
  (w rho : ℕ → ℝ) (k : ℕ) : ℝ :=
  wholeLifeFiniteInnovation w rho (k + 1) k

end ActuarialValuation


