-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4a56056b-06e4-50a7-bae7-a4078851369d

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (m n : ℕ) (s : Γ(L.tensorPow m, ⊤)) (t : Γ(L.tensorPow n, ⊤)) :
    ((Scheme.Modules.pullbackTensorPowIso c L (m + n) ≪≫ Scheme.Modules.tensorPowMapIso e (m + n)).hom.app ⊤)
        ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow (m + n))).app ⊤)
          (((Scheme.Modules.tensorPowAdd L m n).hom.app ⊤) (Scheme.Modules.tensorSections s t)))
      = ((Scheme.Modules.tensorPowAdd L' m n).hom.app ⊤)
          (Scheme.Modules.tensorSections
            (((Scheme.Modules.pullbackTensorPowIso c L m ≪≫ Scheme.Modules.tensorPowMapIso e m).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow m)).app ⊤) s))
            (((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) t))) := by
  have key := AlgebraicGeometry.Scheme.Modules.map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom c L L' e m n
  have h := congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤)
    (Scheme.Modules.pullbackLocalSection c (Scheme.Modules.tensorSections s t))) key
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h
  have e1 : Scheme.Modules.pullbackLocalSection c ((Scheme.Modules.tensorPowAdd L m n).hom.app ⊤ (Scheme.Modules.tensorSections s t)) =
      ((Scheme.Modules.pullback c).map (Scheme.Modules.tensorPowAdd L m n).hom).app ⊤
        (Scheme.Modules.pullbackLocalSection c (Scheme.Modules.tensorSections s t)) :=
    Scheme.Modules.pullbackLocalSection_app c (Scheme.Modules.tensorPowAdd L m n).hom (Scheme.Modules.tensorSections s t)
  have e2 : (Scheme.Modules.pullbackTensorObjIso c (L.tensorPow m) (L.tensorPow n)).hom.app ⊤
        (Scheme.Modules.pullbackLocalSection c (Scheme.Modules.tensorSections s t)) =
      Scheme.Modules.tensorSections (Scheme.Modules.pullbackLocalSection c s) (Scheme.Modules.pullbackLocalSection c t) :=
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2 c s t
  have e3 := AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections_monoidalV2
    (Scheme.Modules.pullbackTensorPowIso c L m ≪≫ Scheme.Modules.tensorPowMapIso e m).hom
    (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom
    (U := ⊤) (Scheme.Modules.pullbackLocalSection c s) (Scheme.Modules.pullbackLocalSection c t)
  change (Scheme.Modules.pullbackTensorPowIso c L (m + n) ≪≫ Scheme.Modules.tensorPowMapIso e (m + n)).hom.app ⊤
      (Scheme.Modules.pullbackLocalSection c ((Scheme.Modules.tensorPowAdd L m n).hom.app ⊤ (Scheme.Modules.tensorSections s t))) =
    (Scheme.Modules.tensorPowAdd L' m n).hom.app ⊤
      (Scheme.Modules.tensorSections
        ((Scheme.Modules.pullbackTensorPowIso c L m ≪≫ Scheme.Modules.tensorPowMapIso e m).hom.app ⊤ (Scheme.Modules.pullbackLocalSection c s))
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤ (Scheme.Modules.pullbackLocalSection c t)))
  rw [e1, h, e2]
  exact congrArg ((Scheme.Modules.tensorPowAdd L' m n).hom.app ⊤) e3

end S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections (solution)
