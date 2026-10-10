-- Prove2me | Definitions.Def_actuarial_gammaPoissonPosteriorRate
-- name    : actuarial_gammaPoissonPosteriorRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:20:27.490529+00:00
-- url     : https://prove2.me/theorems/0e290b3c-9595-46fa-a173-78c4c6016b82
-- title:
--   Gamma posterior rate after exposure volume
-- statement:
--   The Gamma distribution's second parameter is a *rate*, not a scale. The posterior rate is prior rate β plus observed insured exposure E; this explicit convention prevents the common reciprocal-scale error in Poisson-Gamma credibility.
--
--   **Mathematical statement**
--
--   $$
--   \beta'=\beta+E
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration actuarial_gammaPoissonPosteriorRate is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def gammaPoissonPosteriorRate (priorRate exposure : ℝ) : ℝ :=
  priorRate + exposure

end ActuarialValuation


