-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_pullback_thetaBundle_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b928d7c5-8652-5829-8d32-b15b7ab68278

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pushforward_pullback_iso_of_forall_fibre
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

namespace ThetaBCSketch

noncomputable def dualIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

end ThetaBCSketch

open ThetaBCSketch in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n)
    (ψ : SchemeHomOver t' t) (M' : RigidifiedLineBundle c ε t') (e : M'.L ≅ (M.pullbackAlong ψ).L) :
    Nonempty ((Scheme.Modules.pullback ψ.1).obj (thetaBundle c ε t M r n) ≅ thetaBundle c ε t' M' r n) := by

  have hsec : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance
  have hI : (sectionIdeal c ε t).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t ε) hsec
  have hpow : ∀ k : ℕ, ((sectionIdeal c ε t) ^ k).IsInvertible := fun k => by
    induction k with
    | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
    | succ k ih => rw [pow_succ]; exact ih.mul hI
  have hN : Scheme.Modules.IsInvertible (sectionTwist c ε t r) := (hpow r).isInvertible_invModule
  have hF : Scheme.Modules.IsInvertible (M.L ⊗ sectionTwist c ε t r) := M.isInvertible.tensor hN

  have hE : Scheme.Modules.IsLocallyFreeOfRank n (picardBundle c ε t M (sectionTwist c ε t r)) :=
    RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t (M.L ⊗ sectionTwist c ε t r) hF n hfib
  have hdet : Scheme.Modules.IsInvertible (Scheme.Modules.det n (picardBundle c ε t M (sectionTwist c ε t r))) :=
    Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank hE

  obtain ⟨iDual⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ.1 hdet
  obtain ⟨iDet⟩ := Scheme.Modules.nonempty_pullback_det_iso_det_pullback ψ.1 n hE
  obtain ⟨iPF⟩ := RelPicard.nonempty_pushforward_pullback_iso_of_forall_fibre R c ε h𝔉 ψ
    (M.L ⊗ sectionTwist c ε t r) hF n hfib
  obtain ⟨iTw⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ r

  let iF : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (M.L ⊗ sectionTwist c ε t r) ≅
      M'.L ⊗ sectionTwist c ε t' r :=
    Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) M.L (sectionTwist c ε t r) ≪≫ tensorIso e.symm iTw

  refine ⟨iDual ≪≫ dualIso (iDet ≪≫ (Scheme.Modules.exteriorPower T' n).mapIso
    (iPF.symm ≪≫ (Scheme.Modules.pushforward (pullback.snd c t')).mapIso iF))⟩

end S_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso (solution)
