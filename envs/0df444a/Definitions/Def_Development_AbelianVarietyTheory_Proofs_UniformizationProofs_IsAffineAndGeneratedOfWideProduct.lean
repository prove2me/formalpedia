-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineAndGeneratedOfWideProduct
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineAndGeneratedOfWideProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:45.233539+00:00
-- url     : https://prove2.me/theorems/e11ac1f0-07dd-4a9a-b391-4487418dbc8f
-- title:
--   Is Affine And Generated Of Wide Product
-- statement:
--   Definitions and structural lemmas for Is Affine And Generated Of Wide Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineAndGeneratedOfWideProduct.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AffineProduct
noncomputable def subringLift {Y X : Scheme.{0}} [IsAffine X] (B : Subring Γ(Y, ⊤)) (f : Y ⟶ X)
    (h : ∀ a, f.appTop.hom a ∈ B) : Spec (CommRingCat.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom (f.appTop.hom.codRestrict B h)) ≫ X.isoSpec.inv
noncomputable def toSpecSubring {Y : Scheme.{0}} (B : Subring Γ(Y, ⊤)) :
    Y ⟶ Spec (CommRingCat.of B) :=
  Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.subtype)
end GlobalTheory.AffineProduct
namespace GlobalTheory
open AffineProduct
end GlobalTheory


