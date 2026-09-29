-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullback_map_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/77f6cb76-ff68-5e09-afa0-200c9a082dc7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullback_map_of_faithfullyFlat
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace BenchVR

theorem bijective_app
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (θ : L ⟶ M) (hθ : IsIso ((Scheme.Modules.pullback c).map θ))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (θ.app U) := by
  classical
  obtain ⟨hU', hpush⟩ := Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f f' c hc U hU

  have hff : @Module.FaithfullyFlat Γ(X, U) Γ(X', c ⁻¹ᵁ U) _ _
      (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra.toModule := by
    letI aS : Algebra S Γ(X, U) := f.sectionsAlgebra U
    letI aS' : Algebra S' Γ(X', c ⁻¹ᵁ U) := f'.sectionsAlgebra (c ⁻¹ᵁ U)
    letI aRB : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI aSB : Algebra S Γ(X', c ⁻¹ᵁ U) :=
      ((c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.comp (algebraMap S Γ(X, U))).toAlgebra
    haveI : IsScalarTower S Γ(X, U) Γ(X', c ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hsq : CommRingCat.ofHom (algebraMap S S') ≫ (Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫
          f'.appLE ⊤ (c ⁻¹ᵁ U) le_top =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top ≫ c.appLE U (c ⁻¹ᵁ U) le_rfl := by
      have happ : (Spec.map (CommRingCat.ofHom (algebraMap S S'))).appLE ⊤ ⊤ le_top =
          (Spec.map (CommRingCat.ofHom (algebraMap S S'))).appTop := Scheme.Hom.appLE_eq_app _
      have key : ∀ (h₁ h₂ : X' ⟶ Spec (CommRingCat.of S)) (hh : h₁ = h₂)
          (e₁ : c ⁻¹ᵁ U ≤ h₁ ⁻¹ᵁ ⊤) (e₂ : c ⁻¹ᵁ U ≤ h₂ ⁻¹ᵁ ⊤),
          h₁.appLE ⊤ (c ⁻¹ᵁ U) e₁ = h₂.appLE ⊤ (c ⁻¹ᵁ U) e₂ := by
        intros h₁ h₂ hh e₁ e₂; subst hh; rfl
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← happ, Scheme.Hom.appLE_comp_appLE,
        Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact key _ _ hc.w.symm _ _
    haveI : IsScalarTower S S' Γ(X', c ⁻¹ᵁ U) := by
      refine IsScalarTower.of_algebraMap_eq (fun s => ?_)
      change (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom ((f.constToPresheaf.app (op U)).hom s) =
        (f'.constToPresheaf.app (op (c ⁻¹ᵁ U))).hom ((CommRingCat.ofHom (algebraMap S S')).hom s)
      exact congrArg (fun φ => CommRingCat.Hom.hom φ s) hsq.symm
    have hP : Algebra.IsPushout S S' Γ(X, U) Γ(X', c ⁻¹ᵁ U) := hpush
    haveI hP' : Algebra.IsPushout S Γ(X, U) S' Γ(X', c ⁻¹ᵁ U) := hP.symm
    exact Module.FaithfullyFlat.of_linearEquiv (R := Γ(X, U)) (M := Γ(X, U) ⊗[S] S') (N := Γ(X', c ⁻¹ᵁ U))
      (Algebra.IsPushout.equiv (R := S) (S := Γ(X, U)) (R' := S') (S' := Γ(X', c ⁻¹ᵁ U))).toLinearEquiv.symm
  rw [Scheme.Hom.appLE_eq_app] at hff
  letI aRB : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.app U).hom.toAlgebra
  haveI : Module.FaithfullyFlat Γ(X, U) Γ(X', c ⁻¹ᵁ U) := hff
  obtain ⟨βL, hβL⟩ := Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback c hL U hU hU'
  obtain ⟨βM, hβM⟩ := Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback c hM U hU hU'

  let θU : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) :=
    { toFun := fun x => θ.app U x
      map_add' := fun x y => (θ.app U).hom.map_add x y
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul θ r x }
  set θ' := (Scheme.Modules.pullback c).map θ with hθ'

  have hnat : ∀ s : Γ(L, U),
      ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app U (θ.app U s) =
        θ'.app (c ⁻¹ᵁ U) (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app U s) := by
    intro s
    have := congrArg (fun φ => Scheme.Modules.Hom.app φ U s)
      ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.naturality θ)
    exact this
  have hcomm : ∀ t, βM (θU.lTensor Γ(X', c ⁻¹ᵁ U) t) = θ'.app (c ⁻¹ᵁ U) (βL t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b s =>
        rw [LinearMap.lTensor_tmul]
        have e1 : ∀ (N : Type u) [AddCommGroup N] [Module Γ(X, U) N] (n : N),
            b ⊗ₜ[Γ(X, U)] n = b • ((1 : Γ(X', c ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U)] n) := fun N _ _ n => by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e1 _ s, map_smul, map_smul, hβM, hβL, Scheme.Modules.Hom.app_smul]
        congr 1
        exact hnat s
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy, map_add]
        exact ((θ'.app (c ⁻¹ᵁ U)).hom.map_add _ _).symm
  have hbij' : Function.Bijective (θ'.app (c ⁻¹ᵁ U)) := by
    haveI : IsIso θ' := hθ
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hbijT : Function.Bijective (θU.lTensor Γ(X', c ⁻¹ᵁ U)) := by
    have : (fun t => θU.lTensor Γ(X', c ⁻¹ᵁ U) t) = fun t => βM.symm (θ'.app (c ⁻¹ᵁ U) (βL t)) := by
      funext t; rw [← hcomm, LinearEquiv.symm_apply_apply]
    rw [show (θU.lTensor Γ(X', c ⁻¹ᵁ U) : _ → _) = fun t => βM.symm (θ'.app (c ⁻¹ᵁ U) (βL t)) from this]
    exact βM.symm.bijective.comp (hbij'.comp βL.bijective)
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (M := Γ(X', c ⁻¹ᵁ U)) (f := θU)).mp hbijT

end BenchVR

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (θ : L ⟶ M) (hθ : IsIso ((Scheme.Modules.pullback c).map θ)) :
    IsIso θ := by
  let F : TopCat.Sheaf Ab X.carrier := ⟨L.presheaf, Scheme.Modules.isSheaf L⟩
  let G : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  let φ : F ⟶ G := ⟨θ.mapPresheaf⟩
  have hφ : IsIso φ := by
    refine TopCat.Sheaf.isIso_of_isIso_app_of_isBasis (B := fun U : X.affineOpens => (U : X.Opens))
      (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens) φ (fun U => ?_)
    change IsIso (θ.app U)
    rw [ConcreteCategory.isIso_iff_bijective]
    exact BenchVR.bijective_app S' f f' c hc hL hM θ hθ U U.2
  have h1 : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) Ab.{u}).mapIso
      (@asIso _ _ _ _ φ hφ)).hom := inferInstance
  have h2 : IsIso ((Scheme.Modules.toPresheaf X).map θ) := h1
  exact isIso_of_reflects_iso θ (Scheme.Modules.toPresheaf X)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullback_map_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullback_map_of_faithfullyFlat (solution)
