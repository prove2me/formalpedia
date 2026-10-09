-- Prove2me | Definitions.Def_actuarial_decrementAnnualPremium
-- name    : actuarial_decrementAnnualPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:18:51.974767+00:00
-- url     : https://prove2.me/theorems/b123e457-5bd8-4a21-9f66-5e4847f4c8f0
-- title:
--   One-year multiple-decrement net reserve premium
-- statement:
--   Premium required immediately before year k so opening reserve plus premium funds discounted death/exit benefits and next-year survival reserve.
--
--   **Mathematical statement**
--
--   $$
--   \Pi=v(pR_+ + \sum_jq_jb_j)-R
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementExpectedBenefit
open MeasureTheory

namespace ActuarialValuation

noncomputable def decrementAnnualPremium {J : Type*} [Fintype J]
  (p : ℝ) (q b : J → ℝ)
  (v R Rnext : ℝ) : ℝ :=
  v * (p * Rnext + decrementExpectedBenefit q b) - R

end ActuarialValuation


