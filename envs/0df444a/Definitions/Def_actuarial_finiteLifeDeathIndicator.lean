-- Prove2me | Definitions.Def_actuarial_finiteLifeDeathIndicator
-- name    : actuarial_finiteLifeDeathIndicator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:52:42.292329+00:00
-- url     : https://prove2.me/theorems/07847738-8a88-4c70-9959-5b66068454e6
-- title:
--   Indicator for death during year t
-- statement:
--   Pays one precisely for death in year t, with a year-end benefit payable at time t+1.
--
--   **Mathematical statement**
--
--   $$
--   D_t(K)=\mathbf1_{\{K=t\}}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
open MeasureTheory

namespace ActuarialValuation

def finiteLifeDeathIndicator (K t : ℕ) : ℝ := if K = t then 1 else 0

end ActuarialValuation


