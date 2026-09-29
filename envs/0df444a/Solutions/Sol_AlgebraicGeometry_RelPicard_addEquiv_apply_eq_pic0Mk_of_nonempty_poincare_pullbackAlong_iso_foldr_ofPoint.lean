-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fcd0f0ed-291a-5359-a754-68da73a44d6a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classify_tensor
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve"

namespace K6H8

noncomputable def isoOfPullbackIso {P Q : Scheme.{u}} (φ : Q ⟶ P) [IsIso φ] {A B : P.Modules}
    (i : (Scheme.Modules.pullback φ).obj A ≅ (Scheme.Modules.pullback φ).obj B) : A ≅ B :=
  ((Scheme.Modules.pullbackId P).app A).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ).symm).app A ≪≫
    ((Scheme.Modules.pullbackComp (inv φ) φ).app A).symm ≪≫
    (Scheme.Modules.pullback (inv φ)).mapIso i ≪≫
    (Scheme.Modules.pullbackComp (inv φ) φ).app B ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id φ)).app B ≪≫
    (Scheme.Modules.pullbackId P).app B

theorem nonempty_rigidify_iso_self {k : Type u} [Field k] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of k) ⟶ P) (q : P ⟶ Spec (CommRingCat.of k)) (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨i⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible σ q L hL k (𝟙 _)
  exact ⟨isoOfPullbackIso (pullback.fst q (𝟙 _)) i⟩

theorem exists_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule
    {k : Type u} [Field k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c)
    (D : RelativePic0Designation k c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∃ g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong g).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule) := by
  have hLm : Scheme.Modules.IsInvertible
      ((RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule) :=
    (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor (RelEffCartierDiv.isInvertible_I _).isInvertible_module
  let N : RigidifiedLineBundle c ε (𝟙 _) := RigidifiedLineBundle.ofInvertible _ hLm
  obtain ⟨eN⟩ := nonempty_rigidify_iso_self (rigSection c (𝟙 _) ε) (pullback.snd c (𝟙 _)) _ hLm
  have hN : FibrewiseAlgEquivZero N :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule N [x]
      (eN ≪≫ (ρ_ _).symm)
  refine ⟨hD.classify (𝟙 _) N hN, ?_⟩
  obtain ⟨i⟩ := hD.classify_spec (𝟙 _) N hN
  exact ⟨i ≪≫ eN⟩

end K6H8

open K6H8 in

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c)
    (D : RelativePic0Designation k c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    {J : Type*} [AddCommGroup J]
    (ptsI : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (haddI : ∀ a b : J, Nonempty
      ((hD.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hD.poincare.pullbackAlong (ptsI a)).L ⊗ (hD.poincare.pullbackAlong (ptsI b)).L))
    (θ : J ≃+ Pic0 k F)
    (hθpin : ∀ (g : J) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c),
      Nonempty ((hD.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := F),
        (Dv : Divisor k F) =
          Finsupp.single (Mdl.pointEquivPlace ⟨x.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl.pointEquivPlace ⟨ε.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact ε.2⟩) 1 ∧
        θ g = Pic0.mk Dv)
    (g : J) (Dv : Divisor.degZero (K := k) (F := F))
    (hg : Nonempty ((hD.poincare.pullbackAlong (ptsI g)).L ≅
          ((((Dv : Divisor k F)).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (((Dv : Divisor k F)) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (-(((Dv : Divisor k F)) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)))) :
    θ g = Pic0.mk Dv := by
  classical
  let Φ : Pic0 k F → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase := fun P => ptsI (θ.symm P)
  have hΦ_add : ∀ a b, Φ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (Φ a) (Φ b) := by
    intro a b
    have hmem : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
        (algEquivZeroCut c ε).P (𝟙 _) (hD.poincare.pullbackAlong x) := fun x =>
      (algEquivZeroCut c ε).pullback_mem _ _ x _ hD.poincare_mem
    have hcl : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
        x = hD.classify (𝟙 _) (hD.poincare.pullbackAlong x) (hmem x) := fun x =>
      hD.classify_unique _ _ (hmem x) x ⟨Iso.refl _⟩
    obtain ⟨iab⟩ := haddI (θ.symm a) (θ.symm b)
    have h1 : Φ (a + b) = hD.classify (𝟙 _)
        ((hD.poincare.pullbackAlong (Φ a)).tensor (hD.poincare.pullbackAlong (Φ b)))
        ((algEquivZeroGroupCut c ε).tensor_mem _ _ _ (hmem (Φ a)) (hmem (Φ b))) := by
      refine hD.classify_unique _ _ _ _ ⟨?_⟩
      show (hD.poincare.pullbackAlong (ptsI (θ.symm (a + b)))).L ≅
        (hD.poincare.pullbackAlong (ptsI (θ.symm a))).L ⊗ (hD.poincare.pullbackAlong (ptsI (θ.symm b))).L
      rw [map_add]
      exact iab
    rw [h1]
    have h2 := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.classify_tensor (P := algEquivZeroGroupCut c ε) hD (𝟙 _)
      (hD.poincare.pullbackAlong (Φ a)) (hD.poincare.pullbackAlong (Φ b)) (hmem (Φ a)) (hmem (Φ b))
    refine h2.trans ?_
    exact congrArg₂ (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x y)
      (hcl (Φ a)).symm (hcl (Φ b)).symm
  have hΦ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl.pointEquivPlace ⟨P.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl.pointEquivPlace ⟨ε.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact ε.2⟩) 1 →
      Nonempty ((hD.poincare.pullbackAlong (Φ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule) := by
    intro P Dv' hDv'
    obtain ⟨g₀', ⟨i₀'⟩⟩ := exists_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule c ε D hD P
    obtain ⟨g₀, i₀⟩ : ∃ g₀ : J, Nonempty ((hD.poincare.pullbackAlong (ptsI g₀)).L ≅
        (RelEffCartierDiv.ofPoint c P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule) :=
      ⟨ptsI.symm g₀', by rw [Equiv.apply_symm_apply]; exact ⟨i₀'⟩⟩
    obtain ⟨i₀⟩ := i₀
    obtain ⟨Dv'', hDv'', hθ⟩ := hθpin g₀ P ⟨i₀⟩
    have hDD : Dv'' = Dv' := Subtype.ext (hDv''.trans hDv'.symm)
    subst hDD
    have hΦg : Φ (Pic0.mk Dv'') = ptsI g₀ := by
      show ptsI (θ.symm (Pic0.mk Dv'')) = ptsI g₀
      rw [← hθ, AddEquiv.symm_apply_apply]
    rw [hΦg]
    exact ⟨i₀⟩
  have key := AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned
    c ε D hD F Mdl e he pt hpt hpt' Φ hΦ_add hΦ Dv
  have heq : ptsI g = Φ (Pic0.mk Dv) := hD.ext_of_iso (𝟙 _) _ _ ⟨hg.some ≪≫ key.some.symm⟩
  have hg' : g = θ.symm (Pic0.mk Dv) := ptsI.injective heq
  rw [hg', AddEquiv.apply_symm_apply]

end S_AlgebraicGeometry_RelPicard_addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_addEquiv_apply_eq_pic0Mk_of_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint (solution)
