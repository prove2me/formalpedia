-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:44.548239+00:00
-- url     : https://prove2.me/theorems/76175ef5-3ad2-4952-8e84-6cf8b3ae3e8f
-- title:
--   Loc Der Regular Coeff
-- statement:
--   Definitions and structural lemmas for Loc Der Regular Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LocDerRegularCoeff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.VertReg
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
def ptOf (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (y : Sp ℂ ⟶ Y) (W : X.Opens) (f : Γ(X, W)) : ℂ :=
  valAt' y (m ⁻¹ᵁ (W ⊓ W₀)) (d (W ⊓ W₀) (resG X inf_le_left f))
end GlobalTheory.KS.VertReg
namespace GlobalTheory.KS
open VertReg
end GlobalTheory.KS
end


