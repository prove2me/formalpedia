-- Prove2me | Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
-- name    : levy_foundations_compoundPoissonTripleGivenLevyMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:56:41.989816+00:00
-- url     : https://prove2.me/theorems/ef9ed0fc-65f6-4c84-928d-f3b489e94034
-- title:
--   Finite-activity Levy-Khintchine triple with an explicit Levy-measure witness
-- statement:
--   Construct the existing Prove2Me triple with supplied finite Levy-measure evidence.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L617

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory
open scoped ENNReal NNReal
namespace LevyFoundations
/-- Finite-activity triple with its Levy-measure proof explicitly supplied. -/
noncomputable def compoundPoissonTripleGivenLevyMeasure
    (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    [IsProbabilityMeasure ν']
    (hlevy : isLevyMeasure ((r : ℝ≥0∞) • ν')) : LevyKhintchineTriple where
  drift := b + ∫ x in {x : ℝ | |x| < 1}, x ∂((r : ℝ≥0∞) • ν')
  gaussianVariance := 0
  levyMeasure := (r : ℝ≥0∞) • ν'
  levyMeasure_condition := hlevy
end LevyFoundations


