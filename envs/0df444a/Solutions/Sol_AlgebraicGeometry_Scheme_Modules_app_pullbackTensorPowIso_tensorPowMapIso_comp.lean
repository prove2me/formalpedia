-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/79a2a9b5-13ea-5697-a1f2-d4038d37507d

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorPowIso_trans_tensorPowMapIso_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_comp
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X X' X'' : Scheme.{u}} (c : X' ⟶ X) (d : X'' ⟶ X')
    (L : X.Modules) (L' : X'.Modules) (L'' : X''.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L') (e' : (Scheme.Modules.pullback d).obj L' ≅ L'')
    (n : ℕ) (s : Γ(L.tensorPow n, ⊤)) :
    ((Scheme.Modules.pullbackTensorPowIso (d ≫ c) L n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp d c).app L).symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ e') n).hom.app ⊤)
        ((((Scheme.Modules.pullbackPushforwardAdjunction (d ≫ c)).unit.app (L.tensorPow n)).app ⊤) s)
      = ((Scheme.Modules.pullbackTensorPowIso d L' n ≪≫ Scheme.Modules.tensorPowMapIso e' n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app (L'.tensorPow n)).app ⊤)
            (((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
              ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) s))) := by

  have h5 := AlgebraicGeometry.Scheme.Modules.unit_app_comp_pullbackComp_inv d c (L.tensorPow n) ⊤
  have h5s := congrArg (fun k => k s) h5
  simp only [CategoryTheory.comp_apply] at h5s
  have ha : (((Scheme.Modules.pullbackComp d c).inv.app (L.tensorPow n)).app ⊤)
        ((((Scheme.Modules.pullbackPushforwardAdjunction (d ≫ c)).unit.app (L.tensorPow n)).app ⊤) s)
      = (((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app ((Scheme.Modules.pullback c).obj (L.tensorPow n))).app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) s) := h5s

  have hb : ∀ y : Γ((Scheme.Modules.pullback c).obj (L.tensorPow n), ⊤),
      (((Scheme.Modules.pullback d).map (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom).app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app ((Scheme.Modules.pullback c).obj (L.tensorPow n))).app ⊤) y)
        = (((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app (L'.tensorPow n)).app ⊤) (((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) y) := by
    intro y
    have h := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ y)
      ((Scheme.Modules.pullbackPushforwardAdjunction d).unit.naturality (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom)
    simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h
    exact h.symm

  rw [AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso_trans_tensorPowMapIso_comp c d L L' L'' e e' n]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply]
  exact congrArg (fun z => (Scheme.Modules.tensorPowMapIso e' n).hom.app ⊤ ((Scheme.Modules.pullbackTensorPowIso d L' n).hom.app ⊤ z))
    ((congrArg (fun z => ((Scheme.Modules.pullback d).map (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom).app ⊤ z) ha).trans (hb _))

end S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_comp
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_comp (solution)
