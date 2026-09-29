-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3538d5da-9ad9-521e-8c26-84bfee34de00

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange"

namespace ThetaKSketch

noncomputable def dualIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

end ThetaKSketch

open ThetaKSketch in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') (r n : ℕ) :
    Nonempty (thetaBundle (baseChange R c R') (sectionBaseChange R' ε) t' M r n ≅
      thetaBundle c ε (t' ≫ specMap R R') (BaseChange.toR c ε R' M) r n) := by
  obtain ⟨iTw⟩ := RelPicard.nonempty_transport_sectionTwist_baseChange_iso R c ε R' t' r
  obtain ⟨iPush⟩ := Scheme.Modules.nonempty_pushforward_hom_comp_iso (κ c R' t')
    (pullback.snd c (t' ≫ specMap R R')) (M.L ⊗ sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r)

  have hsnd : pullback.snd (baseChange R c R') t' = (κ c R' t').hom ≫ pullback.snd c (t' ≫ specMap R R') :=
    (κ_hom_snd c R' t').symm

  let iE : picardBundle (baseChange R c R') (sectionBaseChange R' ε) t' M
      (sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r) ≅
      picardBundle c ε (t' ≫ specMap R R') (toR c ε R' M) (sectionTwist c ε (t' ≫ specMap R R') r) :=
    (Scheme.Modules.pushforwardCongr hsnd).app _ ≪≫ iPush ≪≫
      (Scheme.Modules.pushforward (pullback.snd c (t' ≫ specMap R R'))).mapIso
        (Scheme.Modules.pullbackTensorObjIso (κ c R' t').inv M.L _ ≪≫ whiskerLeftIso _ iTw)
  exact ⟨dualIso ((Scheme.Modules.exteriorPower T n).mapIso iE)⟩

end S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR (solution)
