-- Prove2me | Definitions.Def_levy_foundations_arrivalSurvivalPolynomial
-- name    : levy_foundations_arrivalSurvivalPolynomial
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:48:50.994001+00:00
-- url     : https://prove2.me/theorems/6464a26d-97b2-4c59-bfc1-47d349a43b3e
-- title:
--   Finite exponential survival polynomial for an arrival time
-- statement:
--   Finite exponential survival polynomial for an arrival time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L98

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
namespace LevyFoundations
/-- Tail of the Gamma(n+1,R) arrival-time law, expressed as a finite sum. -/
noncomputable def arrivalSurvivalPolynomial (R : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(R * t)) *
    ∑ k ∈ Finset.range (n + 1), (R * t) ^ k / (k.factorial : ℝ)
end LevyFoundations


