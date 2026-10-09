-- Prove2me | Definitions.Def_actuarial_decrementExpectedBenefit
-- name    : actuarial_decrementExpectedBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:16:53.72207+00:00
-- url     : https://prove2.me/theorems/48ada365-6b28-42b7-8e1c-791cfc5c98a9
-- title:
--   Cause-specific expected end-year benefit
-- statement:
--   Weighted end-year benefit paid for one of the mutually exclusive exit causes.
--
--   **Mathematical statement**
--
--   $$
--   B=\sum_jq_jb_j
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def decrementExpectedBenefit {J : Type*} [Fintype J]
  (q : J → ℝ) (b : J → ℝ) : ℝ :=
  ∑ j : J, q j * b j

end ActuarialValuation


