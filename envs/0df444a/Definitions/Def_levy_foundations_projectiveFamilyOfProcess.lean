-- Prove2me | Definitions.Def_levy_foundations_projectiveFamilyOfProcess
-- name    : levy_foundations_projectiveFamilyOfProcess
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:35:59.865981+00:00
-- url     : https://prove2.me/theorems/85cd3b3d-80c4-4c23-9ad2-ac1c6146eee9
-- title:
--   Projective family of process finite-dimensional laws
-- statement:
--   Construct a consistent probability-measure family from the finite-dimensional distributions of a measurable stochastic process.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/ProjectiveFamily.lean#L87

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_projectiveFamily
import Definitions.Def_levy_foundations_finiteDimMap
import Definitions.Def_levy_foundations_finiteDimDistribution

open MeasureTheory
open scoped NNReal
namespace LevyFoundations
/-- Bundle the finite-dimensional laws of a measurable process into a projective family. -/
noncomputable def projectiveFamilyOfProcess
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℝ≥0 → Ω → E) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ t, Measurable (X t)) :
    ProjectiveFamily ℝ≥0 (fun _ : ℝ≥0 => E) where
  measure := finiteDimDistribution X μ
  consistent := by
    intro I J hJI
    have hmeasI : Measurable (finiteDimMap X I) := by
      change Measurable (fun (ω : Ω) (i : I) => X i ω)
      exact measurable_pi_lambda _ (fun i => hX i)
    change μ.map (finiteDimMap X J) =
      (μ.map (finiteDimMap X I)).map
        (Finset.restrict₂ (π := fun _ : ℝ≥0 => E) hJI)
    symm
    rw [Measure.map_map
      (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 => E) hJI)
      hmeasI]
    rfl
  prob := by
    intro J
    have hmeasJ : Measurable (finiteDimMap X J) := by
      change Measurable (fun (ω : Ω) (i : J) => X i ω)
      exact measurable_pi_lambda _ (fun i => hX i)
    exact Measure.isProbabilityMeasure_map hmeasJ.aemeasurable
end LevyFoundations


