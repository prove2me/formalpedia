-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:11.960803+00:00
-- url     : https://prove2.me/theorems/f69218c0-3c66-4774-8b1e-869429071fa6
-- title:
--   Volume Univ Fin Zero
-- statement:
--   Definitions and structural lemmas for Volume Univ Fin Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
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
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2
instance xpBorel (p m : ℕ) : BorelSpace (Xp p m) := by
  have : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace
  have : BorelSpace ((Fin p → ℂ) × (Fin m → ℂ) × ℝ) := Prod.borelSpace
  exact Prod.borelSpace
instance xpHaar (p m : ℕ) : (volume : Measure (Xp p m)).IsAddHaarMeasure := by
  have : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure ((Fin p → ℂ) × (Fin m → ℂ) × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _
def kc (s : ℝ) : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-s / 2))
def sclL (p m : ℕ) (t : ℝ) : Xp p m →ₗ[ℝ] Xp p m :=
  (t • LinearMap.id).prodMap ((t • LinearMap.id).prodMap ((t • LinearMap.id).prodMap ((t ^ 2) • LinearMap.id)))
end J2
end ReciprocityTheory.ChartRestriction.DS.Xi


