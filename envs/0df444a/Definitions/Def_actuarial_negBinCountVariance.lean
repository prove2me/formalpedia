-- Prove2me | Definitions.Def_actuarial_negBinCountVariance
-- name    : actuarial_negBinCountVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:55.800734+00:00
-- url     : https://prove2.me/theorems/dd98cb9f-c4b8-482a-9993-4cee504b61fe
-- title:
--   Negative-binomial count variance
-- statement:
--   For valid negative-binomial parameters, the variance exceeds the mean because uncertainty in the Poisson event frequency introduces additional dispersion. The exact variance is r p divided by (1−p) squared.
--
--   **Mathematical statement**
--
--   $$
--   \sigma^2=rp/(1-p)^2
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration actuarial_negBinCountVariance is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def negBinCountVariance (shape : ℕ) (p : ℝ) : ℝ :=
  (shape : ℝ) * p / (1 - p) ^ 2

end ActuarialValuation


