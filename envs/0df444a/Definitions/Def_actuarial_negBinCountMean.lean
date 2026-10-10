-- Prove2me | Definitions.Def_actuarial_negBinCountMean
-- name    : actuarial_negBinCountMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:27:45.574984+00:00
-- url     : https://prove2.me/theorems/d463cb23-4182-4965-be09-89a8ba63f6d9
-- title:
--   Expected claim count under NB size and count parameter
-- statement:
--   For 0≤p<1 and positive integer shape, the negative-binomial mean count equals r p divided by one minus p. This p denotes count rather than Bernoulli success probability, so the formula differs from sources that reverse the parametrisation.
--
--   **Mathematical statement**
--
--   $$
--   \mu=rp/(1-p)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration actuarial_negBinCountMean is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def negBinCountMean (shape : ℕ) (p : ℝ) : ℝ :=
  (shape : ℝ) * p / (1 - p)

end ActuarialValuation


