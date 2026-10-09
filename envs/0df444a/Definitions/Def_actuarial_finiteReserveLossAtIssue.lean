-- Prove2me | Definitions.Def_actuarial_finiteReserveLossAtIssue
-- name    : actuarial_finiteReserveLossAtIssue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:54:01.372115+00:00
-- url     : https://prove2.me/theorems/80e31345-a8d9-4c99-a743-951024f30829
-- title:
--   Finite-horizon net insurer loss including terminal liability
-- statement:
--   Insurer loss at issue through n years: discounted year-end death benefits less beginning-of-year premiums while in force, plus discounted terminal reserve if the policy remains in force at n.
--
--   **Mathematical statement**
--
--   $$
--   L_n=\sum_{t<n}(v^{t+1}b_{t+1}D_t-v^t\pi_tS_t)+v^nV_nS_n
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteReserveLossAtIssue
  (K n : ℕ) (v : ℝ) (premium benefit reserve : ℕ → ℝ) : ℝ :=
  (∑ t ∈ Finset.range n,
    (v ^ (t + 1) * benefit (t + 1) * finiteLifeDeathIndicator K t -
      v ^ t * premium t * finiteLifeInForceIndicator K t)) +
  v ^ n * reserve n * finiteLifeInForceIndicator K n

end ActuarialValuation


