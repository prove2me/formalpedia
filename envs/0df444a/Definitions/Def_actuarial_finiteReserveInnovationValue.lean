-- Prove2me | Definitions.Def_actuarial_finiteReserveInnovationValue
-- name    : actuarial_finiteReserveInnovationValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:56:06.45392+00:00
-- url     : https://prove2.me/theorems/51de0d94-0090-4b28-b616-7bd52d5914e9
-- title:
--   Aggregate discounted net-amount-at-risk innovation
-- statement:
--   Sum of time-zero discounted net-amounts-at-risk times annual mortality surprises through the finite term.
--
--   **Mathematical statement**
--
--   $$
--   Z_n=\sum_{t<n}v^{t+1}(b_{t+1}-V_{t+1})I_t
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteReserveInnovationValue
  (K n : ℕ) (v : ℝ) (benefit reserve q : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range n,
    v ^ (t + 1) * (benefit (t + 1) - reserve (t + 1)) *
      finiteReserveYearInnovation K t q

end ActuarialValuation


