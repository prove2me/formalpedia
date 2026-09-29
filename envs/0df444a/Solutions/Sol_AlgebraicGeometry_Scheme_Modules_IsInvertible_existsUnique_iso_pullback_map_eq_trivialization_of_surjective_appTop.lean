-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/df4ca510-712c-5ffe-b8c8-a9a6f3880ffc

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_app_eq_smul_of_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_units_forall_app_eq_smul_of_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace BenchR_RP

section scalar

variable {X : Scheme.{u}}

noncomputable def smulHomAb (N : X.Modules) (v : Γ(X, ⊤)) : N.presheaf ⟶ N.presheaf where
  app := fun ⟨U⟩ => AddCommGrpCat.ofHom
    { toFun := fun (s : Γ(N, U)) => X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v • s
      map_zero' := smul_zero _
      map_add' := fun a b => smul_add _ a b }
  naturality := fun {U' V'} i => by
    obtain ⟨U⟩ := U'
    obtain ⟨V⟩ := V'
    ext s
    change X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op v • N.presheaf.map i s =
      N.presheaf.map i (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v • s)
    have : i = i.unop.op := rfl
    rw [this, Scheme.Modules.map_smul]
    congr 1
    change _ = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map i.unop.op) v
    rw [← X.presheaf.map_comp]
    rfl

noncomputable def smulHom (N : X.Modules) (v : Γ(X, ⊤)) : N ⟶ N :=
  ⟨PresheafOfModules.homMk (smulHomAb N v) (fun ⟨U⟩ r m => by
    change (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v) • ((show Γ(X, U) from r) • (show Γ(N, U) from m)) =
      (show Γ(X, U) from r) • ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v) • (show Γ(N, U) from m))
    rw [smul_smul, smul_smul, mul_comm])⟩

lemma smulHom_app (N : X.Modules) (v : Γ(X, ⊤)) (U : X.Opens) (s : Γ(N, U)) :
    (smulHom N v).app U s = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op v • s := by
  simp only [smulHom, Scheme.Modules.Hom.app]
  rfl

lemma smulHom_one (N : X.Modules) : smulHom N 1 = 𝟙 N := by
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [smulHom_app, map_one, one_smul, Scheme.Modules.Hom.id_app]
  rfl

lemma smulHom_mul (N : X.Modules) (v w : Γ(X, ⊤)) :
    smulHom N (v * w) = smulHom N w ≫ smulHom N v := by
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, smulHom_app, smulHom_app, smulHom_app, map_mul, mul_smul]

noncomputable def smulIso (N : X.Modules) (v : Γ(X, ⊤)ˣ) : N ≅ N where
  hom := smulHom N v
  inv := smulHom N ↑v⁻¹
  hom_inv_id := by rw [← smulHom_mul, Units.inv_mul, smulHom_one]
  inv_hom_id := by rw [← smulHom_mul, Units.mul_inv, smulHom_one]

end scalar

section scalar2

variable {X T : Scheme.{u}}

lemma smulHom_comm {N N' : X.Modules} (ψ : N ⟶ N') (v : Γ(X, ⊤)) :
    ψ ≫ smulHom N' v = smulHom N v ≫ ψ := by
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, smulHom_app, smulHom_app, Scheme.Modules.Hom.app_smul]

lemma pullback_map_smulHom (g : T ⟶ X) (N : X.Modules) (v : Γ(X, ⊤)) :
    (Scheme.Modules.pullback g).map (smulHom N v) = smulHom ((Scheme.Modules.pullback g).obj N) (g.appTop v) := by
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [smulHom_app]
  exact AlgebraicGeometry.Scheme.Modules.pullback_map_app_eq_smul_of_forall_app_eq_smul g N v _
    (fun U s => smulHom_app N v U s) U s

lemma exists_units_eq_smulHom (γ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ u : Γ(X, ⊤)ˣ, γ.hom = smulHom _ (u : Γ(X, ⊤)) := by
  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.Modules.exists_units_forall_app_eq_smul_of_iso_unit γ
  refine ⟨u, ?_⟩
  apply Scheme.Modules.hom_ext; intro U; ext s
  rw [hu U s, smulHom_app]

end scalar2

section piece

variable {B A Y : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A)
  (S' : Type u) [CommRing S'] (f' : Y ⟶ Spec (CommRingCat.of S'))
  (ε : Spec (CommRingCat.of S') ⟶ Y) (hε : ε ≫ f' = 𝟙 _)
  (p : Spec (CommRingCat.of S') ⟶ B) (hp : ε ≫ ι = p ≫ e)

variable (L : A.Modules) (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)

noncomputable def triv :
    (Scheme.Modules.pullback ε).obj ((Scheme.Modules.pullback ι).obj L) ≅
      SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf :=
  (Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
    ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
    Scheme.Modules.pullbackUnitIso p

variable (M : A.Modules) (hMe : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)

def IsRigid (φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M) : Prop :=
  (Scheme.Modules.pullback ε).map φ.hom = (triv e ι S' ε p hp L hLe ≪≫ (triv e ι S' ε p hp M hMe).symm).hom

include hε in
lemma IsRigid.unique (hΓ : Function.Surjective (f'.appTop).hom) (hL : Scheme.Modules.IsInvertible L)
    {φ ψ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M}
    (hφ : IsRigid e ι S' ε p hp L hLe M hMe φ) (hψ : IsRigid e ι S' ε p hp L hLe M hMe ψ) : φ = ψ :=
  AlgebraicGeometry.Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop
    f' ε hε hΓ _ _ (hL.pullback _) φ ψ (by rw [hφ, hψ])

include hε in
lemma IsRigid.exists (φ₀ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M) :
    ∃ φ, IsRigid e ι S' ε p hp L hLe M hMe φ := by
  let θ := (Scheme.Modules.pullback ε).mapIso φ₀
  obtain ⟨u, hu⟩ := exists_units_eq_smulHom ((triv e ι S' ε p hp L hLe).symm ≪≫ θ ≪≫ triv e ι S' ε p hp M hMe)
  let w : Γ(Y, ⊤)ˣ := Units.map ((f'.appTop).hom : Γ(Spec (CommRingCat.of S'), ⊤) →* Γ(Y, ⊤)) u⁻¹
  refine ⟨φ₀ ≪≫ smulIso _ w, ?_⟩
  have hw : ε.appTop (w : Γ(Y, ⊤)) =
      ((u⁻¹ : Γ(Spec (CommRingCat.of S'), ⊤)ˣ) : Γ(Spec (CommRingCat.of S'), ⊤)) := by
    change ((f'.appTop) ≫ ε.appTop) _ = _
    rw [← Scheme.Hom.comp_appTop, hε, Scheme.Hom.id_appTop]
    rfl
  have hu' := hu
  simp only [Iso.trans_hom, Iso.symm_hom] at hu'
  have h1 : θ.hom ≫ (triv e ι S' ε p hp M hMe).hom =
      (triv e ι S' ε p hp L hLe).hom ≫ smulHom _ (u : Γ(Spec (CommRingCat.of S'), ⊤)) :=
    (Iso.inv_comp_eq _).1 hu'
  have hθ : θ.hom = ((triv e ι S' ε p hp L hLe).hom ≫ smulHom _ (u : Γ(Spec (CommRingCat.of S'), ⊤))) ≫
      (triv e ι S' ε p hp M hMe).inv := (Iso.eq_comp_inv _).2 h1
  show (Scheme.Modules.pullback ε).map (φ₀.hom ≫ smulHom _ (w : Γ(Y, ⊤))) = _
  rw [Functor.map_comp, pullback_map_smulHom, hw]
  change θ.hom ≫ _ = _
  rw [hθ]
  simp only [Category.assoc]
  rw [← smulHom_comm]
  simp only [Category.assoc]
  rw [← smulHom_mul, Units.mul_inv, smulHom_one, Category.comp_id]
  rfl

end piece

end BenchR_RP

open BenchR_RP in
theorem solution
    {B A Y : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A)
    (S' : Type u) [CommRing S'] (f' : Y ⟶ Spec (CommRingCat.of S'))
    (hΓ : Function.Surjective (f'.appTop).hom)
    (ε : Spec (CommRingCat.of S') ⟶ Y) (hε : ε ≫ f' = 𝟙 _)
    (p : Spec (CommRingCat.of S') ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (hMe : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (h : Nonempty ((Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M)) :
    ∃! φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M,
      (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε ι).app M ≪≫ (Scheme.Modules.pullbackCongr hp).app M ≪≫
            ((Scheme.Modules.pullbackComp p e).app M).symm ≪≫ (Scheme.Modules.pullback p).mapIso hMe ≪≫
            Scheme.Modules.pullbackUnitIso p).inv := by
  obtain ⟨φ₀⟩ := h
  obtain ⟨φ, hφ⟩ := IsRigid.exists e ι S' f' ε hε p hp L hLe M hMe φ₀
  refine ⟨φ, ?_, fun ψ hψ => ?_⟩
  · exact hφ
  · exact IsRigid.unique e ι S' f' ε hε p hp L hLe M hMe hΓ hL hψ hφ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop (solution)
