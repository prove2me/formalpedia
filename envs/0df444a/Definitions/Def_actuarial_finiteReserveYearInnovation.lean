-- Prove2me | Definitions.Def_actuarial_finiteReserveYearInnovation
-- name    : actuarial_finiteReserveYearInnovation
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:54:44.918551+00:00
-- url     : https://prove2.me/theorems/49cb59ff-648e-4512-be37-7b4721b5ed9f
-- title:
--   Curtate death-year surprise conditional on in-force event
-- statement:
--   Year-t realised death indicator less its expected conditional rate q_t multiplied by the year-t in-force indicator.
--
--   **Mathematical statement**
--
--   $$
--   I_t(K)=D_t(K)-q_tS_t(K)
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteReserveYearInnovation
  (K t : ℕ) (q : ℕ → ℝ) : ℝ :=
  finiteLifeDeathIndicator K t - q t * finiteLifeInForceIndicator K t

end ActuarialValuation


