-- Prove2me | Definitions.Def_actuarial_finiteLifeInForceIndicator
-- name    : actuarial_finiteLifeInForceIndicator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:52:29.599948+00:00
-- url     : https://prove2.me/theorems/0fa9090c-d5a4-4082-8cd1-77544e335678
-- title:
--   Year-start in-force indicator
-- statement:
--   For given curtate death year K, the insurer is still at risk at the beginning of policy year t precisely when t≤K.
--
--   **Mathematical statement**
--
--   $$
--   S_t(K)=\mathbf1_{\{t\le K\}}
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
open MeasureTheory

namespace ActuarialValuation

def finiteLifeInForceIndicator (K t : ℕ) : ℝ := if t ≤ K then 1 else 0

end ActuarialValuation


