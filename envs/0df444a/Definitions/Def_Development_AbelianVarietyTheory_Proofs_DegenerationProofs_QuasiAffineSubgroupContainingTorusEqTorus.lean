-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:06.182281+00:00
-- url     : https://prove2.me/theorems/92ecd392-065a-4c74-a432-9f65d7344987
-- title:
--   Quasi Affine Subgroup Containing Torus Eq Torus
-- statement:
--   Definitions and structural lemmas for Quasi Affine Subgroup Containing Torus Eq Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.QuasiAffineTorus
section Algebra
variable {k : Type} [Field k] [IsAlgClosed k] {X : Type} [AddCommGroup X]
variable {H : Type} [CommGroup H] (τ : (Multiplicative X →* kˣ) →* H) (A : Subalgebra k (H → k))
end Algebra
section Geometry
open RationalPoint
variable {k : Type} [Field k]
noncomputable def ev {N : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ N) : Γ(N.left, ⊤) →+* k :=
  (Scheme.ΓSpecIso (.of k)).hom.hom.comp (Scheme.Hom.appTop (X := Sp k) x.left).hom
noncomputable def const (N : Over (Sp k)) : k →+* Γ(N.left, ⊤) :=
  N.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
variable [IsAlgClosed k]
end Geometry
section Main
open RationalPoint
variable {k : Type} [Field k] {X : Type} [AddCommGroup X]
noncomputable def torusPt (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  ((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans (MulEquiv.monoidHomCongrRight
    (Units.mapEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv))).symm
end Main
end GlobalTheory.QuasiAffineTorus


