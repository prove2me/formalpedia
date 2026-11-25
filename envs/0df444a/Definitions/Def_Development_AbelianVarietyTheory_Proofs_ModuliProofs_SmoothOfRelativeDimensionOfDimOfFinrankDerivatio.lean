-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:56.963113+00:00
-- url     : https://prove2.me/theorems/e2f95523-e1ee-4388-ba99-8a7eed231c7d
-- title:
--   Smooth Of Relative Dimension Of Dim Of Finrank Derivatio
-- statement:
--   Definitions and structural lemmas for Smooth Of Relative Dimension Of Dim Of Finrank Derivatio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfFinrankDerivatio.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
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
namespace GlobalTheory.SmoothTangent
noncomputable def derivationEquivDual (k R C : Type*) [CommRing k] [CommRing R] [CommRing C]
    [Algebra k R] [Algebra k C] [Algebra R C] [IsScalarTower k R C] :
    Derivation k R C ≃ₗ[C] Module.Dual C (C ⊗[R] Ω[R⁄k]) :=
  (({ (KaehlerDifferential.linearMapEquivDerivation k R (M := C)).toAddEquiv with
      map_smul' := fun _ _ ↦ rfl } : (Ω[R⁄k] →ₗ[R] C) ≃ₗ[C] Derivation k R C).symm).trans
    (LinearMap.liftBaseChangeEquiv C)
end GlobalTheory.SmoothTangent
namespace GlobalTheory
open SmoothTangent
end GlobalTheory


