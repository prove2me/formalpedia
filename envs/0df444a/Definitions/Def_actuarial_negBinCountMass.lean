-- Prove2me | Definitions.Def_actuarial_negBinCountMass
-- name    : actuarial_negBinCountMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:36.268512+00:00
-- url     : https://prove2.me/theorems/83818348-b513-4f91-a08f-3b57b35ea5a0
-- title:
--   Negative-binomial claim count coefficient
-- statement:
--   Defines a negative-binomial frequency coefficient for n claims and positive integer shape r, with p the count probability parameter and 1−p the Bernoulli success probability. The finite choose expression is mathematically the conventional formula only for shape r≥1.
--
--   **Mathematical statement**
--
--   $$
--   f_r(n)=\binom{n+r-1}{n}(1-p)^r p^n
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration actuarial_negBinCountMass is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def negBinCountMass (shape : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (Nat.choose (n + shape - 1) n : ℝ) * (1 - p) ^ shape * p ^ n

end ActuarialValuation


