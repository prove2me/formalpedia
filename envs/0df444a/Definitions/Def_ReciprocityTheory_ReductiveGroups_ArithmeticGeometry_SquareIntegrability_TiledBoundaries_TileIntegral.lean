-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:33.615825+00:00
-- url     : https://prove2.me/theorems/5065ec5d-d903-492d-8713-7fd65104ca55
-- title:
--   Tile Integral
-- statement:
--   Definitions and structural lemmas for Tile Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
section Tile
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
def reps (bA bB : Basis ι ℝ V) : Finset V :=
  (ZSpan.setFinite_inter bB (ZSpan.fundamentalDomain_isBounded bA)).toFinset
def tileT (bA bB : Basis ι ℝ V) : Set V :=
  ⋃ c ∈ reps bA bB, (fun x => x - c) ⁻¹' ZSpan.fundamentalDomain bB
instance cntA (bA : Basis ι ℝ V) : Countable (span ℤ (range bA)).toAddSubgroup :=
  inferInstanceAs (Countable (span ℤ (range bA)))
variable (μ : Measure V) [μ.IsAddHaarMeasure]
end Tile
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries


