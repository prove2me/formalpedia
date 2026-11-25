-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfDirectionsLe
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfDirectionsLe
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:54:37.373416+00:00
-- url     : https://prove2.me/theorems/1c5ab7df-c55d-42fe-83e2-d3457ae2f2d1
-- title:
--   Smooth Of Relative Dimension Of Dim Of Directions Le
-- statement:
--   Definitions and structural lemmas for Smooth Of Relative Dimension Of Dim Of Directions Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfDirectionsLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.SmoothDirections
noncomputable def derivationPoint {k R K : Type} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {r : ℕ}
    (D : Fin r → Derivation k R K) : R →+* TrivSqZeroExt K (Fin r → K) where
  toFun a := TrivSqZeroExt.inl (algebraMap R K a) + TrivSqZeroExt.inr fun i ↦ D i a
  map_one' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp [Algebra.smul_def, mul_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_add' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
end GlobalTheory.SmoothDirections
namespace GlobalTheory
open SmoothDirections
end GlobalTheory


