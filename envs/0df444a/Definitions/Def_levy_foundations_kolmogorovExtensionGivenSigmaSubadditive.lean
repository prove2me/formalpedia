-- Prove2me | Definitions.Def_levy_foundations_kolmogorovExtensionGivenSigmaSubadditive
-- name    : levy_foundations_kolmogorovExtensionGivenSigmaSubadditive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:27:33.804561+00:00
-- url     : https://prove2.me/theorems/daccd932-7528-4375-aa4f-0daa9fce9116
-- title:
--   Kolmogorov extension from a sigma-subadditive projective content
-- statement:
--   Construct the projective extension measure from a supplied proof of sigma-subadditivity, without importing an Open theorem.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Kolmogorov.lean#L362

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily

open MeasureTheory
namespace LevyFoundations
/-- The canonical projective extension, conditional on the required content theorem. -/
noncomputable def kolmogorovExtensionGivenSigmaSubadditive
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)] [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (hσ : (projectiveFamilyContent pf.consistent).IsSigmaSubadditive) : Measure (∀ i, α i) :=
  (projectiveFamilyContent pf.consistent).measure
    isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    hσ
end LevyFoundations


