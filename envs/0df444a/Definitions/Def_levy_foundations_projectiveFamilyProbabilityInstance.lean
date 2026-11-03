-- Prove2me | Definitions.Def_levy_foundations_projectiveFamilyProbabilityInstance
-- name    : levy_foundations_projectiveFamilyProbabilityInstance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:17:40.846162+00:00
-- url     : https://prove2.me/theorems/9f771c06-3a71-4565-8458-80b7a35f7562
-- title:
--   Each projective-family finite-dimensional marginal is a probability measure
-- statement:
--   Register the probability property of each finite marginal of a projective probability-measure family as a typeclass instance.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/ProjectiveFamily.lean#L58

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory
namespace LevyFoundations.ProjectiveFamily
/-- Every finite marginal of a projective probability family is a probability. -/
instance isProbabilityMeasure {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (pf : LevyFoundations.ProjectiveFamily ι α)
    (J : Finset ι) : IsProbabilityMeasure (pf.measure J) := pf.prob J
end LevyFoundations.ProjectiveFamily


