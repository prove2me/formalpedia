-- Prove2me | Definitions.Def_actuarial_gammaPoissonExperienceWeight
-- name    : actuarial_gammaPoissonExperienceWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:20:52.801406+00:00
-- url     : https://prove2.me/theorems/69f92a51-92d8-4988-a1e4-3be0874decb9
-- title:
--   Exposure-dependent exact Bayesian credibility coefficient
-- statement:
--   The exact credibility weight in the Poisson-Gamma conjugate model is E divided by β+E. When β>0 and E≥0 this lies between zero and one, approaching greater reliance on claim experience as accumulated exposure increases.
--
--   **Mathematical statement**
--
--   $$
--   Z=\frac{E}{\beta+E}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration actuarial_gammaPoissonExperienceWeight is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gammaPoissonExperienceWeight (priorRate exposure : ℝ) : ℝ :=
  exposure / (priorRate + exposure)

end ActuarialValuation


