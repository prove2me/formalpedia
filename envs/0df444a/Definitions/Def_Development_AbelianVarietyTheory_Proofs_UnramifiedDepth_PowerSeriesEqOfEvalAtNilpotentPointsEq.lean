-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEq
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEq
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:25.966885+00:00
-- url     : https://prove2.me/theorems/8280e302-9408-5bd4-93ff-5879f0b9b1c4
-- title:
--   Power Series Eq Of Eval At Nilpotent Points Eq
-- statement:
--   Definitions and structural lemmas for Power Series Eq Of Eval At Nilpotent Points Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSeriesEqOfEvalAtNilpotentPointsEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
def lowZero {A κ : Type} [CommRing A] (e : κ →₀ ℕ) : Ideal (MvPowerSeries κ A) where
  carrier := {g | ∀ e' ≤ e, MvPowerSeries.coeff e' g = 0}
  add_mem' {a b} ha hb e' h := by rw [map_add, ha e' h, hb e' h, add_zero]
  zero_mem' e' _ := map_zero _
  smul_mem' c x hx e' h := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2 (le_trans (le_of_le_of_eq le_add_self (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)) h), mul_zero]
end GlobalTheory.ChF


