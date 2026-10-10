-- Prove2me | Definitions.Def_actuarial_gammaPoissonPosteriorMean
-- name    : actuarial_gammaPoissonPosteriorMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:20:41.373083+00:00
-- url     : https://prove2.me/theorems/d865c254-49ba-4f71-935b-f24df2b7b767
-- title:
--   Posterior expected claim frequency per exposure unit
-- statement:
--   For a Poisson count model and shape/rate Gamma prior, the posterior expected frequency per unit exposure is updated shape divided by updated rate. Positive prior rate and nonnegative exposure ensure an ordinary positive denominator.
--
--   **Mathematical statement**
--
--   $$
--   \hat\lambda=\frac{\alpha+C}{\beta+E}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration actuarial_gammaPoissonPosteriorMean is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

noncomputable def gammaPoissonPosteriorMean
  (priorShape priorRate exposure : ℝ) (claims : ℕ) : ℝ :=
  gammaPoissonPosteriorShape priorShape claims /
    gammaPoissonPosteriorRate priorRate exposure

end ActuarialValuation


