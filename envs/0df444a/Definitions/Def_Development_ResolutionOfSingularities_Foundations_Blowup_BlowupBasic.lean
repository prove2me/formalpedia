-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:56.937426+00:00
-- url     : https://prove2.me/theorems/ce7342bc-7f21-44f9-85ff-21a7aaa29734
-- title:
--   Blowup Basic
-- statement:
--   Definitions and structural lemmas for Blowup Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace FunctorialResolution.Blowup
theorem appLE_eq_id_of_eq_id {Z : Scheme.{u}} (g : Z ⟶ Z) (hg : g = 𝟙 Z) (U : Z.Opens)
    (h : U ≤ g ⁻¹ᵁ U) : g.appLE U U h = 𝟙 _ := by
  subst hg
  simp [Scheme.Hom.appLE]
  exact (Category.id_comp _).trans (Z.presheaf.map_id _)
theorem le_preimage_inv_preimage_hom {A B : Scheme.{u}} (e : A ≅ B) (U : B.Opens) :
    U ≤ e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ U) := by
  intro y hy
  show e.hom.base (e.inv.base y) ∈ U
  have hb : e.hom.base (e.inv.base y) = y := by simp
  rw [hb]
  exact hy
noncomputable def sectionsIsoPreimage {A B : Scheme.{u}} (e : A ≅ B) (U : B.Opens) :
    Γ(B, U) ≅ Γ(A, e.hom ⁻¹ᵁ U) where
  hom := e.hom.appLE U (e.hom ⁻¹ᵁ U) le_rfl
  inv := e.inv.appLE (e.hom ⁻¹ᵁ U) U (le_preimage_inv_preimage_hom e U)
  hom_inv_id := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ e.inv_hom_id U _
  inv_hom_id := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ e.hom_inv_id _ _
end FunctorialResolution.Blowup


