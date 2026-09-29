-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_and_nonempty_invModule_iso_tensorUnit_ofIdealTop_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1b53bb74-0988-5412-9f53-95f4c2321f92

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_ofIdealTop_span_singleton
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_nonempty_invModule_iso_tensorUnit_ofIdealTop_span_singleton
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

namespace PrincTriv

variable {X : Scheme.{u}}

noncomputable def unitSections (r : Γ(X, ⊤)) : (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk (M := (SheafOfModules.unit X.ringCatSheaf).val)
    (fun U => (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op r : Γ(X, U.unop)))
    (by
      intro U V f
      change X.presheaf.map f (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op r) =
        X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op r
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl)

noncomputable def mulSection (r : Γ(X, ⊤)) : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  (SheafOfModules.unitHomEquiv (SheafOfModules.unit X.ringCatSheaf)).symm (unitSections r)

theorem mulSection_app_one (r : Γ(X, ⊤)) :
    Scheme.Modules.Hom.app (mulSection r) ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      r • Scheme.Modules.toUnitSection ⊤ 1 := by
  have h1 := SheafOfModules.unitHomEquiv_apply_coe (SheafOfModules.unit X.ringCatSheaf) (mulSection r) (op ⊤)
  rw [mulSection, Equiv.apply_symm_apply] at h1

  have h2 : (unitSections r).val (op ⊤) = r := by
    change X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, op_id, X.presheaf.map_id]
    rfl
  have h3 : r • Scheme.Modules.toUnitSection (X := X) ⊤ 1 = Scheme.Modules.toUnitSection ⊤ r := by
    change r * 1 = r
    rw [mul_one]
  rw [h3]
  change ((mulSection r).val.app (op ⊤)).hom (1 : Γ(X, ⊤)) = r
  rw [mulSection]
  exact h1.symm.trans h2

end PrincTriv

theorem solution
    {X : Scheme.{u}} (r : Γ(X, ⊤))
    (hr : ∀ U : X.affineOpens, X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op r ∈ nonZeroDivisors Γ(X, U)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})).IsInvertible ∧
      Nonempty ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {r})).invModule ≅ 𝟙_ X.Modules) := by
  classical
  set I := Scheme.IdealSheafData.ofIdealTop (Ideal.span {r}) with hI

  have hinv : I.IsInvertible := by
    apply Scheme.IdealSheafData.IsInvertible.of_forall_comap_openCover X.affineCover
    intro i
    rw [hI, Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
    apply Scheme.IdealSheafData.isInvertible_ofIdealTop_span_singleton

    let f := X.affineCover.f i
    have hW : IsAffineOpen (f ''ᵁ (f ⁻¹ᵁ ⊤)) := (isAffineOpen_top (X.affineCover.X i)).image_of_isOpenImmersion f
    refine mem_nonZeroDivisors_of_injective (f := (f.appIso (f ⁻¹ᵁ ⊤)).inv.hom)
      (f.appIso (f ⁻¹ᵁ ⊤)).symm.commRingCatIsoToRingEquiv.injective ?_
    have happ := congrArg (fun φ => φ.hom r) (f.app_appIso_inv ⊤)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at happ
    change (f.appIso (f ⁻¹ᵁ ⊤)).inv.hom ((f.app ⊤).hom r) ∈ _
    rw [happ]
    exact hr ⟨_, hW⟩

  have hZ : Scheme.Modules.zeroSchemeIdeal (PrincTriv.mulSection r) = I :=
    Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul _ r (PrincTriv.mulSection_app_one r)
  have hprod : (∏ _i : PUnit.{u+1}, I ^ (fun _ => 1) _i) = Scheme.Modules.zeroSchemeIdeal (PrincTriv.mulSection r) := by
    rw [hZ, Fintype.prod_subsingleton _ PUnit.unit, pow_one]
  obtain ⟨e⟩ := Scheme.IdealSheafData.nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
    (fun _ : PUnit.{u+1} => I) (fun _ => hinv) (fun _ => 1) (PrincTriv.mulSection r) hprod
  refine ⟨hinv, ⟨?_ ≪≫ e⟩⟩
  exact eqToIso (by rw [Fintype.prod_subsingleton _ PUnit.unit, pow_one])

end S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_nonempty_invModule_iso_tensorUnit_ofIdealTop_span_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_and_nonempty_invModule_iso_tensorUnit_ofIdealTop_span_singleton (solution)
