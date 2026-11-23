-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:00.531217+00:00
-- url     : https://prove2.me/theorems/9dc72683-160b-496f-99f5-e2eb121ce0c5
-- title:
--   JOrb Bound A
-- statement:
--   Definitions and structural lemmas for JOrb Bound A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
section Scale
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
def kI (b : ℝ) : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖ ^ 2) ^ (-b / 2)) ∂μ
end Scale
instance pairBorel (m : ℕ) : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace
instance pairHaar (m : ℕ) : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB


