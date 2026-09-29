-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d6f40b78-813d-561f-8319-6143f452f861

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (B : Type) [CommRing B] (X Y : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B)) (πY : Y ⟶ Spec (CommRingCat.of B))
    (hQP : ∃ (qpm : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)), IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πX)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hρ : ∀ γ : Γ, (ρ γ).hom ≫ πX = πX)
    (q : X ⟶ Y) (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q) (hqπ : q ≫ πY = πX)
    (hint : IsIntegralHom q) (haff : IsAffineHom q) (hsurj : Function.Surjective q.base)
    (hfib : ∀ x x' : X, q.base x = q.base x' ↔ ∃ γ : Γ, (ρ γ).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (q.app V))
    (hrange : ∀ V : Y.Opens, Set.range (q.app V) =
      {t | ∀ γ : Γ, (ρ γ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hq γ]) t = t})
    (hdesc : ∀ U : X.Opens, IsAffineOpen U → (∀ γ : Γ, (ρ γ).hom ⁻¹ᵁ U = U) → ∃ V : Y.Opens, IsAffineOpen V ∧ q ⁻¹ᵁ V = U)
    (hsepY : IsSeparated πY) (hqcY : QuasiCompact πY) (hfpY : LocallyOfFinitePresentation πY) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY := by
  haveI : IsAffineHom q := haff
  haveI : QuasiCompact πY := hqcY
  haveI : CompactSpace ↥Y := QuasiCompact.compactSpace_of_compactSpace πY
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace q
  haveI : LocallyOfFinitePresentation πY := hfpY
  obtain ⟨r, U, hinv, w, hUaff, hcov, hw1, hw2, hw3, hw4⟩ :=
    AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
      B X πX hQP Γ ρ hρ
  obtain ⟨V, v, hVaff, -, hVcov, hv1, hv2, hv3, -⟩ :=
    AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant
      X Y Γ ρ q hq hsurj hinj hrange hdesc r U hUaff hinv hcov w hw1 hw2 hw3 hw4
  exact AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
    B Y πY r V hVaff hVcov v hv1 hv2 hv3

end S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj (solution)
