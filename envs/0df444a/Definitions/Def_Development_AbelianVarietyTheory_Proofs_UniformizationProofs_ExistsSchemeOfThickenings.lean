-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:08.529899+00:00
-- url     : https://prove2.me/theorems/aec15898-0963-465f-8460-0f8269b356b1
-- title:
--   Exists Scheme Of Thickenings
-- statement:
--   Definitions and structural lemmas for Exists Scheme Of Thickenings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickGlue
noncomputable def specDiagram {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens)
    (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) : 𝒰 ⥤ Scheme.{0} where
  obj U := Spec (𝒜.obj (Opposite.op U.1))
  map {U V} f := Spec.map (𝒜.map (homOfLE (show U.1 ≤ V.1 from f.le)).op)
  map_id U := by
    rw [← Spec.map_id, ← 𝒜.map_id]; rfl
  map_comp f g := by
    rw [← Spec.map_comp, ← 𝒜.map_comp]; rfl
noncomputable def toSpec {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) (U : B₀.Opens) : U.toScheme ⟶ Spec (𝒜.obj (Opposite.op U)) :=
  U.toSpecΓ ≫ Spec.map (p.app (Opposite.op U))
end GlobalTheory.ThickGlue


