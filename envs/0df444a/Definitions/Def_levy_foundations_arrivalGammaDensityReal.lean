-- Prove2me | Definitions.Def_levy_foundations_arrivalGammaDensityReal
-- name    : levy_foundations_arrivalGammaDensityReal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:48:25.831989+00:00
-- url     : https://prove2.me/theorems/94e19fe9-3aba-49f8-b64c-777379df32e4
-- title:
--   Real Gamma density for the n-th exponential arrival
-- statement:
--   Real Gamma density for the n-th exponential arrival.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L74

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
namespace LevyFoundations
/-- Gamma(n+1,R) density with rate R as a real-valued function. -/
noncomputable def arrivalGammaDensityReal (R : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  R ^ (n + 1) * s ^ n * Real.exp (-(R * s)) / n.factorial
end LevyFoundations


