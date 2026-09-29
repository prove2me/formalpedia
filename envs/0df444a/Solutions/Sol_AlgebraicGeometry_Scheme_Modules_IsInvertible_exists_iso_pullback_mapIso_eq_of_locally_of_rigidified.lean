-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_pullback_mapIso_eq_of_locally_of_rigidified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/751c3dd2-59e2-504b-b401-b888c2b218ca

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_app_eq_smul_of_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_pullback_mapIso_eq_of_locally_of_rigidified
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace R1Aux

variable {A : Scheme.{u}} (L : A.Modules) (w : Γ(A, ⊤))

noncomputable abbrev res (U : A.Opens) : Γ(A, U) := A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op w

omit L in
theorem map_res {U V : A.Opens} (i : V ⟶ U) : A.presheaf.map i.op (res w U) = res w V := by
  change (A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ A.presheaf.map i.op) w = _
  rw [← Functor.map_comp]
  rfl

noncomputable def smulPresheafHom : L.presheaf ⟶ L.presheaf where
  app U := AddCommGrpCat.ofHom (DistribMulAction.toAddMonoidHom Γ(L, U.unop) (res w U.unop))
  naturality {U V} i := by
    obtain ⟨U⟩ := U; obtain ⟨V⟩ := V
    ext x
    change res w V • L.presheaf.map i x = L.presheaf.map i (res w U • x)
    rw [show i = i.unop.op from rfl, Scheme.Modules.map_smul L i.unop (res w U) x, map_res]

noncomputable def smulHom : L ⟶ L :=
  ⟨PresheafOfModules.homMk (smulPresheafHom L w) (fun U r m => by
    obtain ⟨U⟩ := U
    exact @smul_comm Γ(A, U) Γ(A, U) Γ(L, U) _ _ (smulCommClass_self _ _) (res w U) r m)⟩

theorem smulHom_app (U : A.Opens) (x : Γ(L, U)) : (smulHom L w).app U x = res w U • x := rfl

end R1Aux

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ₀ : Function.Surjective (f.appTop).hom)
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (ρL : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (ρM : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (hloc : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ φ : L ≅ M, (Scheme.Modules.pullback e).mapIso φ = ρL ≪≫ ρM.symm := by
  classical

  obtain ⟨ψ⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial
    f e he hΓ L M hL hM ⟨ρL⟩ ⟨ρM⟩ hloc

  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback e).obj L) := hL.pullback e
  set γ : (Scheme.Modules.pullback e).obj L ⟶ (Scheme.Modules.pullback e).obj L :=
    (Scheme.Modules.pullback e).map ψ.hom ≫ ρM.hom ≫ ρL.inv with hγ
  set γ' : (Scheme.Modules.pullback e).obj L ⟶ (Scheme.Modules.pullback e).obj L :=
    ρL.hom ≫ ρM.inv ≫ (Scheme.Modules.pullback e).map ψ.inv with hγ'
  have hγγ' : γ' ≫ γ = 𝟙 _ := by
    simp only [hγ, hγ', Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_eq_smul hN γ
  obtain ⟨s', hs'⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_eq_smul hN γ'

  have hss : s * s' = 1 := by
    refine AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_one_of_forall_smul_eq hN (s * s') (fun V t => ?_)
    rw [map_mul, mul_smul, ← hs', ← hs]
    change (γ' ≫ γ).app V t = t
    rw [hγγ', Scheme.Modules.Hom.id_app]
    rfl

  set w : Γ(A, ⊤) := f.appTop s' with hw
  set w' : Γ(A, ⊤) := f.appTop s with hw'
  have hww' : w' * w = 1 := by rw [hw, hw', ← map_mul, hss, map_one]
  have hw'w : w * w' = 1 := by rw [mul_comm, hww']
  let μ : L ≅ L :=
    { hom := R1Aux.smulHom L w
      inv := R1Aux.smulHom L w'
      hom_inv_id := by
        apply Scheme.Modules.hom_ext; intro U; ext x
        change R1Aux.res w' U • (R1Aux.res w U • x) = x
        rw [smul_smul, ← map_mul, hww', map_one, one_smul]
      inv_hom_id := by
        apply Scheme.Modules.hom_ext; intro U; ext x
        change R1Aux.res w U • (R1Aux.res w' U • x) = x
        rw [smul_smul, ← map_mul, hw'w, map_one, one_smul] }
  refine ⟨μ ≪≫ ψ, ?_⟩

  have hes' : e.appTop w = s' := by
    rw [hw, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
    rfl
  have heμ : ∀ (V : (Spec (CommRingCat.of S)).Opens) (t : Γ((Scheme.Modules.pullback e).obj L, V)),
      ((Scheme.Modules.pullback e).map μ.hom).app V t =
        (Spec (CommRingCat.of S)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s' • t := by
    intro V t
    rw [AlgebraicGeometry.Scheme.Modules.pullback_map_app_eq_smul_of_forall_app_eq_smul e L w μ.hom
      (fun U x => rfl) V t, hes']

  have key : (Scheme.Modules.pullback e).map μ.hom ≫ γ = 𝟙 _ := by
    apply Scheme.Modules.hom_ext; intro V; ext t
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app]
    change γ.app V (((Scheme.Modules.pullback e).map μ.hom).app V t) = t
    rw [heμ, Scheme.Modules.Hom.app_smul, hs, smul_smul, ← map_mul, mul_comm, hss, map_one, one_smul]
  ext
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp]
  have : (Scheme.Modules.pullback e).map ψ.hom = γ ≫ ρL.hom ≫ ρM.inv := by
    simp only [hγ, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, ← Category.assoc, key, Category.id_comp]

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_pullback_mapIso_eq_of_locally_of_rigidified
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_pullback_mapIso_eq_of_locally_of_rigidified (solution)
