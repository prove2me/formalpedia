-- Prove2me | Definitions.Def_actuarial_finiteReserveAnnualBalance
-- name    : actuarial_finiteReserveAnnualBalance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:54:16.261408+00:00
-- url     : https://prove2.me/theorems/14acf50b-9443-44a0-8206-e210fdd3d4b1
-- title:
--   One-year conditional actuarial reserve balance
-- statement:
--   Opening reserve plus premium equals discounted expected next reserve on survival plus year-end death benefit, given conditional p and q.
--
--   **Mathematical statement**
--
--   $$
--   V_t+\pi_t=v(p_tV_{t+1}+q_tb_{t+1})
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
open MeasureTheory

namespace ActuarialValuation

def finiteReserveAnnualBalance
  (v : ℝ) (reserve premium benefit p q : ℕ → ℝ) (t : ℕ) : Prop :=
  reserve t + premium t =
    v * (p t * reserve (t + 1) + q t * benefit (t + 1))

end ActuarialValuation


