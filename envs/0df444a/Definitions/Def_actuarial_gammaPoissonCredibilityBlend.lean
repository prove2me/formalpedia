-- Prove2me | Definitions.Def_actuarial_gammaPoissonCredibilityBlend
-- name    : actuarial_gammaPoissonCredibilityBlend
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T14:21:07.052885+00:00
-- url     : https://prove2.me/theorems/ecbcbb59-5ade-43c5-96cd-afc466648e38
-- title:
--   Weighted experience and collective frequency
-- statement:
--   The credibility premium combines observed aggregate claims per unit exposure C/E and the Gamma prior population frequency α/β, with respective weights E/(β+E) and β/(β+E). The usual representation requires E>0 and β>0; at zero exposure the claim rate C/E is not a valid observed experience statistic.
--
--   **Mathematical statement**
--
--   $$
--   \hat\lambda=Z\,C/E+(1-Z)\alpha/\beta
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration actuarial_gammaPoissonCredibilityBlend is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

namespace ActuarialValuation

noncomputable def gammaPoissonCredibilityBlend
  (priorShape priorRate exposure : ℝ) (claims : ℕ) : ℝ :=
  gammaPoissonExperienceWeight priorRate exposure *
       ((claims : ℝ) / exposure) +
    (1 - gammaPoissonExperienceWeight priorRate exposure) *
       (priorShape / priorRate)

end ActuarialValuation


