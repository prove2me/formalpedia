-- Prove2me | Definitions.Def_actuarial_negBinGammaProbability
-- name    : actuarial_negBinGammaProbability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:28:05.500302+00:00
-- url     : https://prove2.me/theorems/0ce90953-55b3-4c3b-8e5e-c05e66bdd589
-- title:
--   Unit-exposure Gamma-Poisson predictive count parameter
-- statement:
--   A Gamma mixing distribution with positive rate beta and positive integer shape yields a negative-binomial mixed-Poisson count law at one exposure unit with the count parameter p=1/(beta+1). This is the reciprocal rate-plus-one, not beta/(beta+1), which is the complementary success parameter.
--
--   **Mathematical statement**
--
--   $$
--   p=1/(\beta+1)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration actuarial_negBinGammaProbability is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def negBinGammaProbability (priorRate : ℝ) : ℝ :=
  1 / (priorRate + 1)

end ActuarialValuation


