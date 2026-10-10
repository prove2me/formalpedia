-- Prove2me | Definitions.Def_actuarial_negBinGammaPredictive
-- name    : actuarial_negBinGammaPredictive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:28:21.055049+00:00
-- url     : https://prove2.me/theorems/48e0147a-dcad-4352-8c43-888cffc12c47
-- title:
--   Integer-shape Gamma-Poisson predictive count coefficient
-- statement:
--   The model uses a shape/rate Gamma prior for a Poisson rate at unit exposure. The predictive count mass is the integer-shape negative-binomial coefficient evaluated at the rate-derived count parameter. The declaration encodes the known mixture result algebraically without asserting an integral identity.
--
--   **Mathematical statement**
--
--   $$
--   g(n)=\binom{n+r-1}{n}(\beta/(\beta+1))^r(1/(\beta+1))^n
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration actuarial_negBinGammaPredictive is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass
import Definitions.Def_actuarial_negBinGammaProbability

namespace ActuarialValuation

noncomputable def negBinGammaPredictive (shape : ℕ) (priorRate : ℝ) (n : ℕ) : ℝ :=
  negBinCountMass shape (negBinGammaProbability priorRate) n

end ActuarialValuation


