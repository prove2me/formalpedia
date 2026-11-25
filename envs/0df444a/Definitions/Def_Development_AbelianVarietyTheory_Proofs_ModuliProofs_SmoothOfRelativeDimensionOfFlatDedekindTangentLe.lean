-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:02.377903+00:00
-- url     : https://prove2.me/theorems/a976f192-9982-4c94-b8c4-57a354ab07ee
-- title:
--   Smooth Of Relative Dimension Of Flat Dedekind Tangent Le
-- statement:
--   Definitions and structural lemmas for Smooth Of Relative Dimension Of Flat Dedekind Tangent Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
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
namespace GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
def pointOfDerivations {k B C : Type} [CommRing k] [CommRing B] [Field C] [Algebra k B]
    [Algebra k C] [Algebra B C] [IsScalarTower k B C] {r : ℕ} (D : Fin r → Derivation k B C) :
    B →+* TrivSqZeroExt C (Fin r → C) where
  toFun b := (algebraMap B C b, fun i ↦ D i b)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap B C)) (funext fun i ↦ (D i).map_one_eq_zero)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap B C) a b) (funext fun i ↦ by
    change D i (a * b) = algebraMap B C a * D i b + D i a * algebraMap B C b
    rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def, mul_comm (D i a)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap B C)) (funext fun i ↦ map_zero (D i))
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap B C) a b)
    (funext fun i ↦ map_add (D i) a b)
end GlobalTheory.SmoothDedekind


