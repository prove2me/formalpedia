-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_compatible_pullback_adicThickening_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/29178af9-d020-5f84-803e-19607332a868

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_hom_app_eq_of_affHom_ofModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_compatible_pullback_adicThickening_iso
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FormalIsoAdic

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~pushforward"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

theorem affHom_ext {F G : OModulePresheaf f} {Φ Ψ : AffHom F G}
    (h : ∀ (U : X.affineOpens) (x : F.obj U.1), Φ.app U x = Ψ.app U x) : Φ = Ψ := by
  obtain ⟨a, b, c⟩ := Φ
  obtain ⟨a', b', c'⟩ := Ψ
  have : a = a' := funext fun U => LinearMap.ext (h U)
  subst this
  rfl

theorem app_map {M N : X.Modules} (α : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (s : Γ(M, V)) :
    α.app U (M.presheaf.map i.op s) = N.presheaf.map i.op (α.app V s) := by
  have h := ConcreteCategory.congr_hom (α.mapPresheaf.naturality i.op) s
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at h
  exact h

noncomputable def ofMap {M N : X.Modules} (α : M ⟶ N) : AffHom (ofModules f M) (ofModules f N) where
  app U :=
    { toFun := fun s => α.app U.1 s
      map_add' := fun x y => map_add (α.app U.1).hom x y
      map_smul' := fun r x => by
        show α.app U.1 ((Scheme.TwoAffineOpenCover.algebraOfHom f U.1).algebraMap r • x)
          = (Scheme.TwoAffineOpenCover.algebraOfHom f U.1).algebraMap r • α.app U.1 x
        exact Scheme.Modules.Hom.app_smul α _ x }
  app_smul U a x := Scheme.Modules.Hom.app_smul α a x
  naturality h := by
    refine LinearMap.ext fun s => ?_
    show α.app _ (_) = _
    exact app_map α (homOfLE h) s

theorem ofMap_app {M N : X.Modules} (α : M ⟶ N) (U : X.affineOpens) (s : Γ(M, U.1)) :
    (ofMap f α).app U s = α.app U.1 s := rfl

theorem ofMap_comp {M N K : X.Modules} (α : M ⟶ N) (β : N ⟶ K) :
    ofMap f (α ≫ β) = (ofMap f β).comp (ofMap f α) :=
  affHom_ext f fun U s => by
    show (α ≫ β).app U.1 s = β.app U.1 (α.app U.1 s)
    rw [Scheme.Modules.Hom.comp_app]; rfl

theorem ofMap_id (M : X.Modules) : ofMap f (𝟙 M) = AffHom.id (ofModules f M) :=
  affHom_ext f fun U s => by
    show (𝟙 M : M ⟶ M).app U.1 s = s
    rw [Scheme.Modules.Hom.id_app]; rfl

theorem comp_assoc {F G H K : OModulePresheaf f} (a : AffHom F G) (b : AffHom G H) (c : AffHom H K) :
    (c.comp b).comp a = c.comp (b.comp a) := affHom_ext f fun _ _ => rfl

theorem comp_id' {F G : OModulePresheaf f} (a : AffHom F G) : a.comp (AffHom.id F) = a := affHom_ext f fun _ _ => rfl
theorem id_comp' {F G : OModulePresheaf f} (a : AffHom F G) : (AffHom.id G).comp a = a := affHom_ext f fun _ _ => rfl

section Transition

variable {Z Z' X : Scheme.{u}} (t : Z ⟶ Z') (ι' : Z' ⟶ X) (ι : Z ⟶ X) (h : t ≫ ι' = ι)

private noncomputable def _root_.FormalIsoAdic.trans (N : X.Modules) :
    (Scheme.Modules.pushforward ι').obj ((Scheme.Modules.pullback ι').obj N) ⟶
      (Scheme.Modules.pushforward ι).obj ((Scheme.Modules.pullback ι).obj N) :=
  (Scheme.Modules.pushforward ι').map
      ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N))
    ≫ (Scheme.Modules.pushforwardComp t ι').hom.app
        ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N))
    ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N)
    ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N)
    ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N)

p2m_export "FormalIsoAdic" "trans"
theorem unit_eq (N : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N =
      (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N ≫ trans t ι' ι h N :=
  AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_unit_app_eq_of_comp_eq t ι' ι h N

theorem trans_nat (N N' : X.Modules)
    (φ' : (Scheme.Modules.pullback ι').obj N ⟶ (Scheme.Modules.pullback ι').obj N')
    (φ : (Scheme.Modules.pullback ι).obj N ⟶ (Scheme.Modules.pullback ι).obj N')
    (hφ : φ =
      ((Scheme.Modules.pullbackComp t ι').app N ≪≫ (Scheme.Modules.pullbackCongr h).app N).inv
        ≫ (Scheme.Modules.pullback t).map φ'
        ≫ ((Scheme.Modules.pullbackComp t ι').app N' ≪≫ (Scheme.Modules.pullbackCongr h).app N').hom) :
    trans t ι' ι h N ≫ (Scheme.Modules.pushforward ι).map φ =
      (Scheme.Modules.pushforward ι').map φ' ≫ trans t ι' ι h N' :=
  AlgebraicGeometry.Scheme.Modules.transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq
    t ι' ι h N N' φ' φ hφ

theorem rho_compat (N : X.Modules) (q : X ⟶ Spec (.of R)) :
    (ofMap q (trans t ι' ι h N)).comp (ofMap q ((Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N)) =
      ofMap q ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N) :=
  (ofMap_comp q _ _).symm.trans (congrArg (ofMap q) (unit_eq t ι' ι h N).symm)

theorem psi_compat (N N' : X.Modules) (q : X ⟶ Spec (.of R))
    (φ' : (Scheme.Modules.pullback ι').obj N ⟶ (Scheme.Modules.pullback ι').obj N')
    (φ : (Scheme.Modules.pullback ι).obj N ⟶ (Scheme.Modules.pullback ι).obj N')
    (hφ : φ =
      ((Scheme.Modules.pullbackComp t ι').app N ≪≫ (Scheme.Modules.pullbackCongr h).app N).inv
        ≫ (Scheme.Modules.pullback t).map φ'
        ≫ ((Scheme.Modules.pullbackComp t ι').app N' ≪≫ (Scheme.Modules.pullbackCongr h).app N').hom) :
    (ofMap q (trans t ι' ι h N')).comp
        (ofMap q ((Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N ≫ (Scheme.Modules.pushforward ι').map φ')) =
      ofMap q ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N ≫ (Scheme.Modules.pushforward ι).map φ) := by
  have h1 := trans_nat t ι' ι h N N' φ' φ hφ
  have h2 := unit_eq t ι' ι h N
  refine (ofMap_comp q _ _).symm.trans (congrArg (ofMap q) ?_)
  calc ((Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N ≫ (Scheme.Modules.pushforward ι').map φ')
          ≫ trans t ι' ι h N'
        = (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N
            ≫ ((Scheme.Modules.pushforward ι').map φ' ≫ trans t ι' ι h N') := Category.assoc _ _ _
    _ = (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N
            ≫ (trans t ι' ι h N ≫ (Scheme.Modules.pushforward ι).map φ) :=
          congrArg (fun x => (Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N ≫ x) h1.symm
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction ι').unit.app N ≫ trans t ι' ι h N)
            ≫ (Scheme.Modules.pushforward ι).map φ := (Category.assoc _ _ _).symm
    _ = (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N ≫ (Scheme.Modules.pushforward ι).map φ :=
          congrArg (fun x => x ≫ (Scheme.Modules.pushforward ι).map φ) h2.symm

end Transition

theorem unit_comp_map_hom_inv {Z X : Scheme.{u}} (ι : Z ⟶ X) {N N' : X.Modules}
    (e : (Scheme.Modules.pullback ι).obj N ≅ (Scheme.Modules.pullback ι).obj N') :
    ((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N ≫ (Scheme.Modules.pushforward ι).map e.hom)
        ≫ (Scheme.Modules.pushforward ι).map e.inv =
      (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N := by
  rw [Category.assoc]
  have hmi : (Scheme.Modules.pushforward ι).map e.hom ≫ (Scheme.Modules.pushforward ι).map e.inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (congrArg (fun x => (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N ≫ x) hmi).trans
    (Category.comp_id _)

end FormalIsoAdic

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~pushforward" in open FormalIsoAdic  in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (𝓜 𝓜' : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (φ : ∀ n : ℕ, (Scheme.Modules.pullback (adicThickeningι p I n)).obj 𝓜 ≅ (Scheme.Modules.pullback (adicThickeningι p I n)).obj 𝓜')
    (hφ : ∀ n, φ n =
        ((Scheme.Modules.pullbackComp (adicThickeningTransition p I n) (adicThickeningι p I (n + 1))).app 𝓜
            ≪≫ (Scheme.Modules.pullbackCongr (adicThickeningTransition_ι p I n)).app 𝓜).symm
          ≪≫ (Scheme.Modules.pullback (adicThickeningTransition p I n)).mapIso (φ (n + 1))
          ≪≫ ((Scheme.Modules.pullbackComp (adicThickeningTransition p I n) (adicThickeningι p I (n + 1))).app 𝓜'
            ≪≫ (Scheme.Modules.pullbackCongr (adicThickeningTransition_ι p I n)).app 𝓜')) :
    Nonempty (𝓜 ≅ 𝓜') := by

  let F : OModulePresheaf p := ofModules p 𝓜
  let G : OModulePresheaf p := ofModules p 𝓜'
  have hFc : F.IsCoherent := AlgebraicGeometry.OModulePresheaf.isCoherent_ofModules_of_locallyTrivial p 𝓜 h𝓜.exists_trivialization
  have hFq : F.IsQuasicoherent := AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial p 𝓜 h𝓜.exists_trivialization
  have hGc : G.IsCoherent := AlgebraicGeometry.OModulePresheaf.isCoherent_ofModules_of_locallyTrivial p 𝓜' h𝓜'.exists_trivialization
  have hGq : G.IsQuasicoherent := AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial p 𝓜' h𝓜'.exists_trivialization

  let Fn : ℕ → OModulePresheaf p := fun n =>
    ofModules p ((Scheme.Modules.pushforward (adicThickeningι p I n)).obj ((Scheme.Modules.pullback (adicThickeningι p I n)).obj 𝓜))
  let Gn : ℕ → OModulePresheaf p := fun n =>
    ofModules p ((Scheme.Modules.pushforward (adicThickeningι p I n)).obj ((Scheme.Modules.pullback (adicThickeningι p I n)).obj 𝓜'))
  let ρ : ∀ n : ℕ, AffHom F (Fn n) := fun n => ofMap p ((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι p I n)).unit.app 𝓜)
  let ρ' : ∀ n : ℕ, AffHom G (Gn n) := fun n => ofMap p ((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι p I n)).unit.app 𝓜')
  let τ : ∀ n : ℕ, AffHom (Fn (n + 1)) (Fn n) := fun n => ofMap p (trans (adicThickeningTransition p I n) (adicThickeningι p I (n + 1)) (adicThickeningι p I n) (adicThickeningTransition_ι p I n) 𝓜)
  let τ' : ∀ n : ℕ, AffHom (Gn (n + 1)) (Gn n) := fun n => ofMap p (trans (adicThickeningTransition p I n) (adicThickeningι p I (n + 1)) (adicThickeningι p I n) (adicThickeningTransition_ι p I n) 𝓜')

  let ψ : ∀ n : ℕ, AffHom F (Gn n) := fun n => ofMap p ((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι p I n)).unit.app 𝓜 ≫ (Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).hom)
  let ψ' : ∀ n : ℕ, AffHom G (Fn n) := fun n => ofMap p ((Scheme.Modules.pullbackPushforwardAdjunction (adicThickeningι p I n)).unit.app 𝓜' ≫ (Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).inv)

  have hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U) := fun n U =>
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
      I p 𝓜 h𝓜 n U).1
  have hρ's : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ' n).app U) := fun n U =>
    (AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
      I p 𝓜' h𝓜' n U).1
  have hρk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)) := fun n U =>
    Submodule.ext fun s => by
      rw [LinearMap.mem_ker]
      exact (AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
        I p 𝓜 h𝓜 n U).2 s
  have hρ'k : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ' n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)) := fun n U =>
    Submodule.ext fun s => by
      rw [LinearMap.mem_ker]
      exact (AlgebraicGeometry.Scheme.Modules.IsInvertible.unit_app_adicThickening_surjective_and_eq_zero_iff_mem_pow_smul_top
        I p 𝓜' h𝓜' n U).2 s

  have hρc : ∀ n : ℕ, (τ n).comp (ρ (n + 1)) = ρ n := fun n =>
    rho_compat (adicThickeningTransition p I n) (adicThickeningι p I (n + 1)) (adicThickeningι p I n)
      (adicThickeningTransition_ι p I n) 𝓜 p
  have hρ'c : ∀ n : ℕ, (τ' n).comp (ρ' (n + 1)) = ρ' n := fun n =>
    rho_compat (adicThickeningTransition p I n) (adicThickeningι p I (n + 1)) (adicThickeningι p I n)
      (adicThickeningTransition_ι p I n) 𝓜' p

  have hφhom : ∀ n : ℕ, (φ n).hom =
      ((Scheme.Modules.pullbackComp (adicThickeningTransition p I n) (adicThickeningι p I (n + 1))).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr (adicThickeningTransition_ι p I n)).app 𝓜).inv
        ≫ (Scheme.Modules.pullback (adicThickeningTransition p I n)).map (φ (n + 1)).hom
        ≫ ((Scheme.Modules.pullbackComp (adicThickeningTransition p I n) (adicThickeningι p I (n + 1))).app 𝓜' ≪≫ (Scheme.Modules.pullbackCongr (adicThickeningTransition_ι p I n)).app 𝓜').hom := by
    intro n
    have e := congrArg Iso.hom (hφ n)
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] at e ⊢
    exact e
  have hφinv : ∀ n : ℕ, (φ n).inv =
      ((Scheme.Modules.pullbackComp (adicThickeningTransition p I n) (adicThickeningι p I (n + 1))).app 𝓜' ≪≫ (Scheme.Modules.pullbackCongr (adicThickeningTransition_ι p I n)).app 𝓜').inv
        ≫ (Scheme.Modules.pullback (adicThickeningTransition p I n)).map (φ (n + 1)).inv
        ≫ ((Scheme.Modules.pullbackComp (adicThickeningTransition p I n) (adicThickeningι p I (n + 1))).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr (adicThickeningTransition_ι p I n)).app 𝓜).hom := by
    intro n
    have e := congrArg Iso.inv (hφ n)
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] at e ⊢
    exact e

  have hψ : ∀ n : ℕ, (τ' n).comp (ψ (n + 1)) = ψ n := fun n =>
    psi_compat (adicThickeningTransition p I n) (adicThickeningι p I (n + 1)) (adicThickeningι p I n)
      (adicThickeningTransition_ι p I n) 𝓜 𝓜' p (φ (n + 1)).hom (φ n).hom (hφhom n)
  have hψ' : ∀ n : ℕ, (τ n).comp (ψ' (n + 1)) = ψ' n := fun n =>
    psi_compat (adicThickeningTransition p I n) (adicThickeningι p I (n + 1)) (adicThickeningι p I n)
      (adicThickeningTransition_ι p I n) 𝓜' 𝓜 p (φ (n + 1)).inv (φ n).inv (hφinv n)

  obtain ⟨Φ, hΦ, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
      I p F G hFc hFq hGc hGq Gn τ' ρ' hρ's hρ'k hρ'c ψ hψ
  obtain ⟨Φ', hΦ', -⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
      I p G F hGc hGq hFc hFq Fn τ ρ hρs hρk hρc ψ' hψ'

  obtain ⟨χ, -, hχu⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
      I p F F hFc hFq hFc hFq Fn τ ρ hρs hρk hρc ρ hρc
  obtain ⟨χ', -, hχ'u⟩ :=
    AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
      I p G G hGc hGq hGc hGq Gn τ' ρ' hρ's hρ'k hρ'c ρ' hρ'c
  have hFF : Φ'.comp Φ = AffHom.id F := by
    have h1 : Φ'.comp Φ = χ := hχu _ fun n => by
      have e1 : (ρ n).comp (Φ'.comp Φ) = ((ρ n).comp Φ').comp Φ := (comp_assoc p _ _ _).symm
      have e2 : ((ρ n).comp Φ').comp Φ = (ψ' n).comp Φ := by rw [hΦ' n]
      have e3 : (ψ' n).comp Φ =
          (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).inv)).comp ((ρ' n).comp Φ) :=
        (congrArg (fun x => AffHom.comp x Φ) (ofMap_comp p _ _)).trans (comp_assoc p _ _ _)
      have e4 : (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).inv)).comp ((ρ' n).comp Φ) =
          (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).inv)).comp (ψ n) := by rw [hΦ n]
      have e5 : (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).inv)).comp (ψ n) = ρ n :=
        (ofMap_comp p _ _).symm.trans (congrArg (ofMap p) (unit_comp_map_hom_inv (adicThickeningι p I n) (φ n)))
      exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
    have h2 : AffHom.id F = χ := hχu _ fun n => comp_id' p _
    rw [h1, h2]
  have hGG : Φ.comp Φ' = AffHom.id G := by
    have h1 : Φ.comp Φ' = χ' := hχ'u _ fun n => by
      have e1 : (ρ' n).comp (Φ.comp Φ') = ((ρ' n).comp Φ).comp Φ' := (comp_assoc p _ _ _).symm
      have e2 : ((ρ' n).comp Φ).comp Φ' = (ψ n).comp Φ' := by rw [hΦ n]
      have e3 : (ψ n).comp Φ' =
          (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).hom)).comp ((ρ n).comp Φ') :=
        (congrArg (fun x => AffHom.comp x Φ') (ofMap_comp p _ _)).trans (comp_assoc p _ _ _)
      have e4 : (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).hom)).comp ((ρ n).comp Φ') =
          (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).hom)).comp (ψ' n) := by rw [hΦ' n]
      have e5 : (ofMap p ((Scheme.Modules.pushforward (adicThickeningι p I n)).map (φ n).hom)).comp (ψ' n) = ρ' n :=
        (ofMap_comp p _ _).symm.trans (congrArg (ofMap p) (unit_comp_map_hom_inv (adicThickeningι p I n) (φ n).symm))
      exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
    have h2 : AffHom.id G = χ' := hχ'u _ fun n => comp_id' p _
    rw [h1, h2]

  obtain ⟨α, hα, -⟩ := AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules p 𝓜 𝓜' Φ
  obtain ⟨β, hβ, -⟩ := AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules p 𝓜' 𝓜 Φ'
  obtain ⟨γ, -, hγu⟩ := AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules p 𝓜 𝓜 (AffHom.id F)
  obtain ⟨γ', -, hγ'u⟩ := AlgebraicGeometry.OModulePresheaf.existsUnique_hom_app_eq_of_affHom_ofModules p 𝓜' 𝓜' (AffHom.id G)
  have hαβ : α ≫ β = 𝟙 𝓜 := by
    have h1 : α ≫ β = γ := hγu _ fun U s => by
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hα, hβ]
      show (Φ'.comp Φ).app U s = _
      rw [hFF]
    have h2 : 𝟙 𝓜 = γ := hγu _ fun U s => by rw [Scheme.Modules.Hom.id_app]; rfl
    rw [h1, h2]
  have hβα : β ≫ α = 𝟙 𝓜' := by
    have h1 : β ≫ α = γ' := hγ'u _ fun U s => by
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hβ, hα]
      show (Φ.comp Φ').app U s = _
      rw [hGG]
    have h2 : 𝟙 𝓜' = γ' := hγ'u _ fun U s => by rw [Scheme.Modules.Hom.id_app]; rfl
    rw [h1, h2]
  exact ⟨⟨α, β, hαβ, hβα⟩⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_compatible_pullback_adicThickening_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_compatible_pullback_adicThickening_iso (solution)
