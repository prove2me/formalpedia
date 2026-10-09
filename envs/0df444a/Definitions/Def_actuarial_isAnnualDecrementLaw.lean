-- Prove2me | Definitions.Def_actuarial_isAnnualDecrementLaw
-- name    : actuarial_isAnnualDecrementLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:16:37.50265+00:00
-- url     : https://prove2.me/theorems/ccc83bf9-6740-471d-a3bf-7f2a08343312
-- title:
--   One-year survival and mutually exclusive cause probabilities
-- statement:
--   Surviving in force or exiting for exactly one cause exhausts the conditional one-year outcomes.
--
--   **Mathematical statement**
--
--   $$
--   p\ge0,\quad q_j\ge0,\quad p+\sum_jq_j=1
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
open MeasureTheory

namespace ActuarialValuation

def isAnnualDecrementLaw {J : Type*} [Fintype J]
  (p : ℝ) (q : J → ℝ) : Prop :=
  0 ≤ p ∧ (∀ j : J, 0 ≤ q j) ∧ p + (∑ j : J, q j) = 1

end ActuarialValuation


