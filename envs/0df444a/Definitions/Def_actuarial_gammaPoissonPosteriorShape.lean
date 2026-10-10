-- Prove2me | Definitions.Def_actuarial_gammaPoissonPosteriorShape
-- name    : actuarial_gammaPoissonPosteriorShape
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:20:19.652696+00:00
-- url     : https://prove2.me/theorems/e3b7e6ec-b1b6-4efc-adbd-a9af183d301e
-- title:
--   Gamma posterior shape after observing claim count
-- statement:
--   The Gamma prior uses the shape-and-rate parameterisation and starts with prior shape α. Observing a nonnegative integer aggregate count C increases the posterior shape to α+C. This is an algebraic conjugacy update rather than a complete formalisation of the Gamma probability density.
--
--   **Mathematical statement**
--
--   $$
--   \alpha'=\alpha+C
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration actuarial_gammaPoissonPosteriorShape is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gammaPoissonPosteriorShape (priorShape : ℝ) (claims : ℕ) : ℝ :=
  priorShape + (claims : ℝ)

end ActuarialValuation


