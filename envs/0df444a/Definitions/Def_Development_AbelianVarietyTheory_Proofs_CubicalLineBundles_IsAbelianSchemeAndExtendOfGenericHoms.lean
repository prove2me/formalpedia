-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:15.874722+00:00
-- url     : https://prove2.me/theorems/ecf7940b-5a9e-542a-b510-fb044e35ced5
-- title:
--   Is Abelian Scheme And Extend Of Generic Homs
-- statement:
--   Definitions and structural lemmas for Is Abelian Scheme And Extend Of Generic Homs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory
theorem isIso_toUnit_splitTorus_punit (S : Scheme.{0}) : IsIso (toUnit (splitTorus S PUnit)) := by
  have h : 𝟙 (splitTorus S PUnit) = 1 := by
    rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
    congr 1
  exact ⟨η, h.symm, toUnit_unique _ _⟩
noncomputable def torusExtensionOfAbelian {K : Type} [Field K] (A : Over (Spec (.of K))) [GrpObj A]
    (h : IsAbelianScheme A) : TorusExtension A where
  X := PUnit
  B := A
  isAbelian := h
  q := 𝟙 A
  q_hom := inferInstance
  q_flat := by rw [Over.id_left]; infer_instance
  q_surjective := by rw [Over.id_left]; infer_instance
  q_quasiCompact := by rw [Over.id_left]; infer_instance
  i := toUnit _ ≫ η
  i_hom := by have := h.comm; infer_instance
  isKernel := by
    have := isIso_toUnit_splitTorus_punit (Spec (.of K))
    exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
end GlobalTheory


