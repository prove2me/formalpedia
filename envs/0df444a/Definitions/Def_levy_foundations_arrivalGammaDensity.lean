-- Prove2me | Definitions.Def_levy_foundations_arrivalGammaDensity
-- name    : levy_foundations_arrivalGammaDensity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:48:41.639886+00:00
-- url     : https://prove2.me/theorems/cd8f90c0-5989-4372-8b1c-488084b9d844
-- title:
--   Nonnegative Gamma arrival-time density supported on the nonnegative axis
-- statement:
--   Nonnegative Gamma arrival-time density supported on the nonnegative axis.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L79

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_levy_foundations_arrivalGammaDensityReal
namespace LevyFoundations
/-- Gamma arrival density, zero outside the nonnegative half-line. -/
noncomputable def arrivalGammaDensity (R : ℝ) (n : ℕ) (s : ℝ) : ENNReal :=
  (Set.Ici 0).indicator
    (fun y => ENNReal.ofReal (arrivalGammaDensityReal R n y)) s
end LevyFoundations


