-- Prove2me | Definitions.Def_levy_foundations_projectiveFamily
-- name    : levy_foundations_projectiveFamily
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T12:34:27.563238+00:00
-- url     : https://prove2.me/theorems/34792465-4504-442d-93d0-2e5897b4247e
-- title:
--   Consistent projective family of finite-dimensional probability laws
-- statement:
--   For an arbitrary index type and measurable state space at each index, a projective family records a probability measure on every finite product. The consistency field requires all finite-dimensional marginalisations to agree. This is the input to the Kolmogorov extension theorem.
-- source:
--   Shmuel Link, LeanLevy, `LeanLevy/Processes/ProjectiveFamily.lean`, `ProbabilityTheory.ProjectiveFamily`, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4: https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/ProjectiveFamily.lean

import Mathlib.MeasureTheory.Constructions.Projective

open MeasureTheory

namespace LevyFoundations
/-- A probability measure on each finite coordinate set, consistent under marginalisation. -/
structure ProjectiveFamily (ι : Type*) (α : ι → Type*)
    [∀ i, MeasurableSpace (α i)] where
  measure : ∀ J : Finset ι, Measure (∀ j : J, α j)
  consistent : IsProjectiveMeasureFamily measure
  prob : ∀ J : Finset ι, IsProbabilityMeasure (measure J)
end LevyFoundations


