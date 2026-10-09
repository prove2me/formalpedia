-- Prove2me | Definitions.Def_actuarial_wholeLifeFiniteInnovation
-- name    : actuarial_wholeLifeFiniteInnovation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:00:43.775692+00:00
-- url     : https://prove2.me/theorems/8205d72a-8cda-46e0-a3b9-0d19f1f434c0
-- title:
--   Truncated discounted sum of annual mortality surprises
-- statement:
--   The centred reserve loss up to horizon n is the finite sum over earlier years of a mortality innovation multiplied by that year's discounted net amount at risk. The in-force indicator inside each innovation automatically ends the cashflow exposure on actual death.
--
--   **Mathematical statement**
--
--   $$
--   Z_n(k)=\sum_{t<n}\rho_tI_t(k)
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, 319-323, DOI https://doi.org/10.1007/s13385-020-00256-9; original countable-L2 extension in this mission

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation

namespace ActuarialValuation

noncomputable def wholeLifeFiniteInnovation
  (w rho : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, rho t * wholeLifeYearInnovation w t k

end ActuarialValuation


