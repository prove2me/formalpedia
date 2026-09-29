-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.comp_ne_zero_of_ne_zero_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c7ac424a-53e0-550d-b9a2-866a22db92ef

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comp_ne_zero_of_ne_zero_of_isIntegral

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace P2mWs30LBPairing

variable {X : Scheme.{u}}

theorem unitEnd_eq_zero_of (c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (h : (show Γ(X, ⊤) from c.app ⊤ (1 : Γ(X, ⊤))) = 0) : c = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (show Γ(X, U) from c.app U m) = (show Γ(X, U) from (0 : Γ(𝟙_ X.Modules, U) ⟶ Γ(𝟙_ X.Modules, U)) m)
  rw [AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul c U m, h, map_zero, zero_mul]
  rfl

theorem unitEnd_comp_app (a b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    (show Γ(X, ⊤) from (a ≫ b).app ⊤ (1 : Γ(X, ⊤))) =
      (show Γ(X, ⊤) from b.app ⊤ (1 : Γ(X, ⊤))) * (show Γ(X, ⊤) from a.app ⊤ (1 : Γ(X, ⊤))) := by
  have h := AlgebraicGeometry.Scheme.Modules.unitHom_app_eq_mul b ⊤ (a.app ⊤ (1 : Γ(X, ⊤)))
  have hid : homOfLE (le_top (a := (⊤ : X.Opens))) = 𝟙 _ := rfl
  rw [hid, op_id, CategoryTheory.Functor.map_id] at h
  exact h

theorem restrict_map_zero (U : X.Opens) (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (0 : M ⟶ N) = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  rfl

theorem eq_image_preimage (U V : X.Opens) (hV : V ≤ U) : V = U.ι ''ᵁ (U.ι ⁻¹ᵁ V) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hV]

theorem eq_zero_of_restrict_eq_zero [IsIntegral X] {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N)
    (f : M ⟶ N) (U : X.Opens) (hU : Nonempty U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map f = 0) : f = 0 := by
  refine AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_forall_app_eq_zero_of_isIntegral hN f U hU ?_
  intro V hV
  rw [eq_image_preimage U V hV]
  change ((Scheme.Modules.restrictFunctor U.ι).map f).app (U.ι ⁻¹ᵁ V) = 0
  rw [h]
  rfl

end P2mWs30LBPairing

open P2mWs30LBPairing in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (t : M ⟶ 𝟙_ X.Modules) (hs : s ≠ 0) (ht : t ≠ 0) : s ≫ t ≠ 0 := by
  intro hst

  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.exists_trivialization x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsIntegral (U : Scheme.{u}) := isIntegral_of_isOpenImmersion U.ι
  let R := Scheme.Modules.restrictFunctor U.ι
  let e : R.obj M ≅ 𝟙_ (U : Scheme.{u}).Modules := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ eU
  let rU : R.obj (𝟙_ X.Modules) ≅ 𝟙_ (U : Scheme.{u}).Modules :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (𝟙_ X.Modules) ≪≫ Scheme.Modules.pullbackUnitIso U.ι
  let α : 𝟙_ (U : Scheme.{u}).Modules ⟶ 𝟙_ (U : Scheme.{u}).Modules := rU.inv ≫ R.map s ≫ e.hom
  let β : 𝟙_ (U : Scheme.{u}).Modules ⟶ 𝟙_ (U : Scheme.{u}).Modules := e.inv ≫ R.map t ≫ rU.hom
  have hαβ : α ≫ β = 0 := by
    have : R.map s ≫ R.map t = 0 := by rw [← Functor.map_comp, hst]; exact restrict_map_zero U _ _
    simp only [α, β, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (R.map s), this, Limits.zero_comp, Limits.comp_zero]

  have hprod : (show Γ((U : Scheme.{u}), ⊤) from β.app ⊤ (1 : Γ((U : Scheme.{u}), ⊤))) *
      (show Γ((U : Scheme.{u}), ⊤) from α.app ⊤ (1 : Γ((U : Scheme.{u}), ⊤))) = 0 := by
    rw [← unitEnd_comp_app, hαβ]
    rfl
  rcases mul_eq_zero.mp hprod with hb | ha
  ·
    have hβ : β = 0 := unitEnd_eq_zero_of β hb
    have htU : R.map t = 0 := by
      have : R.map t = e.hom ≫ β ≫ rU.inv := by simp [β]
      rw [this, hβ, Limits.zero_comp, Limits.comp_zero]
    exact ht (eq_zero_of_restrict_eq_zero (Scheme.Modules.isInvertible_unit X) t U inferInstance htU)
  ·
    have hα : α = 0 := unitEnd_eq_zero_of α ha
    have hsU : R.map s = 0 := by
      have : R.map s = rU.hom ≫ α ≫ e.inv := by simp [α]
      rw [this, hα, Limits.zero_comp, Limits.comp_zero]
    exact hs (eq_zero_of_restrict_eq_zero hM s U inferInstance hsU)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comp_ne_zero_of_ne_zero_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comp_ne_zero_of_ne_zero_of_isIntegral (solution)
