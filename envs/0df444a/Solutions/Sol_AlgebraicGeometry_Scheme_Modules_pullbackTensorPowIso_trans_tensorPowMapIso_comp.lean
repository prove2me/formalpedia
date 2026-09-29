-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso_trans_tensorPowMapIso_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/727c9a9d-f8c1-5ccd-90d7-536bd40ea027

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X X' X'' : Scheme.{u}} (c : X' ⟶ X) (d : X'' ⟶ X')
    (L : X.Modules) (L' : X'.Modules) (L'' : X''.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L') (e' : (Scheme.Modules.pullback d).obj L' ≅ L'') (n : ℕ) :
    Scheme.Modules.pullbackTensorPowIso (d ≫ c) L n ≪≫
        Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp d c).app L).symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ e') n
      = ((Scheme.Modules.pullbackComp d c).app (L.tensorPow n)).symm ≪≫
          (Scheme.Modules.pullback d).mapIso (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n) ≪≫
          (Scheme.Modules.pullbackTensorPowIso d L' n ≪≫ Scheme.Modules.tensorPowMapIso e' n) := by

  have nat : ∀ {X₁ Y₁ X₂ Y₂ : X'.Modules} (p : X₁ ⟶ Y₁) (q : X₂ ⟶ Y₂) {Z : X''.Modules}
      (h : (Scheme.Modules.pullback d).obj (Y₁ ⊗ Y₂) ⟶ Z),
      (Scheme.Modules.pullbackTensorObjIso d X₁ X₂).inv ≫ (Scheme.Modules.pullback d).map (p ⊗ₘ q) ≫ h
        = ((Scheme.Modules.pullback d).map p ⊗ₘ (Scheme.Modules.pullback d).map q) ≫ (Scheme.Modules.pullbackTensorObjIso d Y₁ Y₂).inv ≫ h := by
    intro X₁ Y₁ X₂ Y₂ p q Z h
    simp only [Scheme.Modules.pullbackTensorObjIso, Iso.symm_inv, Functor.Monoidal.μIso_hom,
      Functor.LaxMonoidal.μ_natural_assoc]

  have step : ∀ (M : X.Modules) (N' M' : X'.Modules) (K N'' M'' : X''.Modules)
      (A1 : (Scheme.Modules.pullback (d ≫ c)).obj M ≅ K) (A2 : K ≅ M'')
      (C1 : (Scheme.Modules.pullback c).obj M ≅ N') (C2 : N' ≅ M')
      (D1 : (Scheme.Modules.pullback d).obj M' ≅ N'') (D2 : N'' ≅ M''),
      A1 ≪≫ A2 = ((Scheme.Modules.pullbackComp d c).app M).symm ≪≫ (Scheme.Modules.pullback d).mapIso (C1 ≪≫ C2) ≪≫ (D1 ≪≫ D2) →
      (Scheme.Modules.pullbackTensorObjIso (d ≫ c) M L ≪≫ whiskerRightIso A1 ((Scheme.Modules.pullback (d ≫ c)).obj L)) ≪≫
          tensorIso A2 (((Scheme.Modules.pullbackComp d c).app L).symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ e')
        = ((Scheme.Modules.pullbackComp d c).app (M ⊗ L)).symm ≪≫
            (Scheme.Modules.pullback d).mapIso ((Scheme.Modules.pullbackTensorObjIso c M L ≪≫ whiskerRightIso C1 ((Scheme.Modules.pullback c).obj L)) ≪≫ tensorIso C2 e) ≪≫
            ((Scheme.Modules.pullbackTensorObjIso d M' L' ≪≫ whiskerRightIso D1 ((Scheme.Modules.pullback d).obj L')) ≪≫ tensorIso D2 e') := by
    intro M N' M' K N'' M'' A1 A2 C1 C2 D1 D2 ih
    have ihh := congrArg Iso.hom ih
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv] at ihh

    have hP := congrArg Iso.inv (AlgebraicGeometry.Scheme.Modules.pullbackComp_app_tensorObj d c M L)
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, tensorIso_inv, Iso.app_inv, Category.assoc] at hP
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, tensorIso_hom, whiskerRightIso_hom,
      Category.assoc]
    rw [hP]
    dsimp only [Functor.comp_obj] at ihh ⊢
    simp only [Category.assoc, Functor.map_comp, Iso.map_inv_hom_id_assoc]
    simp only [← tensorHom_id, ← Functor.map_comp_assoc, tensorHom_comp_tensorHom, Category.id_comp]
    rw [nat]
    simp only [Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom]
    rw [ihh]
  induction n with
  | zero =>
    simp only [Scheme.Modules.pullbackTensorPowIso, Scheme.Modules.tensorPowMapIso]
    dsimp only [Scheme.Modules.tensorPow_zero]
    simp only [AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso, Iso.trans_refl]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    exact (Iso.eq_inv_comp _).mpr (AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom d c)
  | succ n ih =>
    simp only [Scheme.Modules.pullbackTensorPowIso, Scheme.Modules.tensorPowMapIso]
    exact step (L.tensorPow n) _ _ _ _ _ _ _ _ _ _ _ ih

end S_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp (solution)
