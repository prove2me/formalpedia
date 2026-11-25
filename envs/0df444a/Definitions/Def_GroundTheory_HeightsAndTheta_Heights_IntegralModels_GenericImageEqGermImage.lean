-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:54.087172+00:00
-- url     : https://prove2.me/theorems/e2875930-7c58-478c-99e1-249c0fb000a5
-- title:
--   Generic Image Eq Germ Image
-- statement:
--   Definitions and structural lemmas for Generic Image Eq Germ Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GenericImageEqGermImage.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
section Objects
variable {X : Scheme.{u}}
variable [IrreducibleSpace X]
theorem germ_smul_generic (E : X.Modules) {U : X.Opens} (hU : genericPoint X ∈ U) (r : Γ(X, U))
    (s : Γ(E, U)) :
    E.presheaf.germ U _ hU (r • s) = X.presheaf.germ U _ hU r • E.presheaf.germ U _ hU s :=
  PresheafOfModules.germ_smul (M := E.val) _ U hU r s
theorem GenericStalkIso.map_smul_stalk {E E' : X.Modules} (φ : GenericStalkIso E E')
    (c : X.presheaf.stalk (genericPoint X)) (v : E.presheaf.stalk (genericPoint X)) :
    φ.toAddEquiv (c • v) = c • φ.toAddEquiv v := by
  obtain ⟨U, hU, r, rfl⟩ := X.presheaf.exists_germ_eq c
  obtain ⟨V, hV, s, rfl⟩ := E.presheaf.exists_germ_eq v
  obtain ⟨W, hW, t, ht⟩ := E'.presheaf.exists_germ_eq (φ.toAddEquiv (E.presheaf.germ V _ hV s))
  have hO : genericPoint X ∈ U ⊓ V ⊓ W := ⟨⟨hU, hV⟩, hW⟩
  have iU : U ⊓ V ⊓ W ≤ U := inf_le_left.trans inf_le_left
  have iV : U ⊓ V ⊓ W ≤ V := inf_le_left.trans inf_le_right
  have iW : U ⊓ V ⊓ W ≤ W := inf_le_right
  rw [← X.presheaf.germ_res_apply (homOfLE iU) _ hO r,
    ← E.presheaf.germ_res_apply (homOfLE iV) _ hO s] at *
  rw [← E'.presheaf.germ_res_apply (homOfLE iW) _ hO t] at ht
  rw [← germ_smul_generic, φ.map_smul_germ _ hO _ _ _ ht.symm, germ_smul_generic, ht]
variable {E E' : X.Modules}
def GenericStalkIso.toLinearEquiv (φ : GenericStalkIso E E') :
    E.presheaf.stalk (genericPoint X) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X) :=
  { φ.toAddEquiv with map_smul' := φ.map_smul_stalk }
def GenericStalkIso.ofLinearEquiv
    (φ : E.presheaf.stalk (genericPoint X) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X)) : GenericStalkIso E E' where
  toAddEquiv := φ.toAddEquiv
  map_smul_germ U hU r s t h := by
    simp only [LinearEquiv.coe_toAddEquiv] at h ⊢
    rw [germ_smul_generic, germ_smul_generic, ← h]
    exact φ.map_smul _ _
end Objects
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model


