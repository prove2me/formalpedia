-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3c94d689-81d7-54c8-a8e6-8e4999993c81

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FrameKit19

theorem locallyOfFinitePresentation_of_isNoetherianRing {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFinitePresentation) X.affineCover]
  intro i
  have h : ((X.affineCover.f i ≫ f).appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType) X.affineCover).1 inferInstance i
  haveI : IsNoetherianRing ↑(Γ(Spec R, ⊤)) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  exact RingHom.FinitePresentation.of_finiteType.1 h

section Transition

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A] (T : Subalgebra A₀ A)
  {X : Scheme.{u}} (w : X ⟶ Spec (CommRingCat.of A₀))

theorem specMap_algebraMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 1

theorem exists_transition :
    ∃ q : pullback w (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶ pullback w (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
      q ≫ pullback.fst w _ = pullback.fst w _ ∧
      q ≫ pullback.snd w _ = pullback.snd w _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) :=
  ⟨pullback.lift (pullback.fst w _) (pullback.snd w _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))
      (by rw [Category.assoc, specMap_algebraMap_comp]; exact pullback.condition),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isPullback_comp_transition {Z : Scheme.{u}} {f : Z ⟶ Spec (CommRingCat.of A)} (r : Z ⟶ X)
    (hr : IsPullback r f w (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (q : pullback w (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶ pullback w (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
    (hq_fst : q ≫ pullback.fst w _ = pullback.fst w _)
    (hq_snd : q ≫ pullback.snd w _ = pullback.snd w _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) :
    IsPullback (hr.isoPullback.hom ≫ q) f (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  have h1 : (hr.isoPullback.hom ≫ q) ≫ pullback.fst w _ = r := by rw [Category.assoc, hq_fst, hr.isoPullback_hom_fst]
  have h2 : (hr.isoPullback.hom ≫ q) ≫ pullback.snd w _ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) := by
    rw [Category.assoc, hq_snd, ← Category.assoc, hr.isoPullback_hom_snd]
  refine IsPullback.of_right (h₁₂ := pullback.fst w _) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) (v₁₃ := w)
    ?_ h2 (IsPullback.of_hasPullback w _)
  rw [h1, specMap_algebraMap_comp]; exact hr

end Transition

theorem stage_frame
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {Z₁ : Scheme.{u}} (f₁ : Z₁ ⟶ Spec (CommRingCat.of A₀)) [IsProper f₁]
    (N : ℕ) {Z : Scheme.{u}} {f : Z ⟶ Spec (CommRingCat.of A)} (g₁ : Z ⟶ Z₁)
    (hg₁ : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (hι : ι ≫ ProjSpace.π A N = f)
    (ε : Spec (CommRingCat.of A) ⟶ Z) (hε : ε ≫ f = 𝟙 _) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG)
      (m : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
        pullback (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
      (_ : m ≫ pullback.snd _ _ = pullback.snd _ _)
      (σ : Spec (CommRingCat.of ↥T) ⟶ pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
      (_ : σ ≫ pullback.snd f₁ _ = 𝟙 _)
      (r : Z ⟶ pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
      (_ : IsPullback r f (pullback.snd f₁ _) (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))),
      ι ≫ ProjSpace.map A₀ A N = r ≫ m ≫ pullback.fst _ _ ∧ ε ≫ r = Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) ≫ σ := by
  classical
  haveI : LocallyOfFinitePresentation (ProjSpace.π A₀ N) := locallyOfFinitePresentation_of_isNoetherianRing _
  haveI : LocallyOfFinitePresentation f₁ := locallyOfFinitePresentation_of_isNoetherianRing _
  have hP := ProjSpace.isPullback_map A₀ A N

  let gT : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) :=
    hg₁.isoPullback.inv ≫ ι ≫ hP.isoPullback.hom
  have hgT : gT ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [gT, Category.assoc, IsPullback.isoPullback_hom_snd, hι]
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd]
  have hgS_w : (pullback.snd (𝟙 (Spec (CommRingCat.of A₀))) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ ε ≫ g₁) ≫ f₁ =
      pullback.snd (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
    rw [Category.assoc, Category.assoc, hg₁.w, ← Category.assoc ε, hε, Category.id_comp]
  let gS : pullback (𝟙 (Spec (CommRingCat.of A₀))) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) :=
    pullback.lift (pullback.snd _ _ ≫ ε ≫ g₁) (pullback.snd _ _) hgS_w
  have hgS : gS ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

  let X₁ : Bool → Scheme.{u} := fun b => cond b Z₁ (Spec (CommRingCat.of A₀))
  let X₂ : Bool → Scheme.{u} := fun b => cond b (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A₀)) Z₁
  let F₁ : ∀ b, X₁ b ⟶ Spec (CommRingCat.of A₀) := fun b => match b with | true => f₁ | false => 𝟙 _
  let F₂ : ∀ b, X₂ b ⟶ Spec (CommRingCat.of A₀) := fun b => match b with | true => ProjSpace.π A₀ N | false => f₁
  let G : ∀ b, pullback (F₁ b) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback (F₂ b) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) := fun b => match b with | true => gT | false => gS
  have iqc : QuasiCompact f₁ := inferInstance
  have iqs : QuasiSeparated f₁ := inferInstance
  have iqc1 : QuasiCompact (𝟙 (Spec (CommRingCat.of A₀))) := inferInstance
  have iqs1 : QuasiSeparated (𝟙 (Spec (CommRingCat.of A₀))) := inferInstance
  have ilfpP : LocallyOfFinitePresentation (ProjSpace.π A₀ N) := inferInstance
  have ilfp1 : LocallyOfFinitePresentation f₁ := inferInstance
  haveI : ∀ b, QuasiCompact (F₁ b) := fun b => match b with | true => iqc | false => iqc1
  haveI : ∀ b, QuasiSeparated (F₁ b) := fun b => match b with | true => iqs | false => iqs1
  haveI : ∀ b, LocallyOfFinitePresentation (F₂ b) := fun b => match b with | true => ilfpP | false => ilfp1
  have hG : ∀ b, G b ≫ pullback.snd (F₂ b) _ = pullback.snd (F₁ b) _ := fun b => by
    cases b
    · exact hgS
    · exact hgT
  obtain ⟨T, hTfg, -, g₀, hg₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := A₀) (A := A) F₁ F₂ G hG ∅

  obtain ⟨qZ, hqZ_fst, hqZ_snd⟩ := exists_transition T f₁
  obtain ⟨qP, hqP_fst, hqP_snd⟩ := exists_transition T (ProjSpace.π A₀ N)
  obtain ⟨qS, hqS_fst, hqS_snd⟩ := exists_transition T (𝟙 (Spec (CommRingCat.of A₀)))
  have hr := isPullback_comp_transition T f₁ g₁ hg₁ qZ hqZ_fst hqZ_snd

  let m : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
      pullback (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) := g₀ true
  have hm : m ≫ pullback.snd _ _ = pullback.snd _ _ := hg₀ true
  let n : pullback (𝟙 (Spec (CommRingCat.of A₀))) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
      pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) := g₀ false
  have hn : n ≫ pullback.snd f₁ _ = pullback.snd (𝟙 _) _ := hg₀ false
  have hcT : qZ ≫ m = gT ≫ qP := hcompat true qZ qP hqZ_fst hqZ_snd hqP_fst hqP_snd
  have hcS : qS ≫ n = gS ≫ qZ := hcompat false qS qZ hqS_fst hqS_snd hqZ_fst hqZ_snd
  refine ⟨T, hTfg, m, hm,
    inv (pullback.snd (𝟙 (Spec (CommRingCat.of A₀))) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) ≫ n, ?_,
    hg₁.isoPullback.hom ≫ qZ, hr, ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_comp_eq, Category.comp_id]
    exact hn
  ·
    rw [Category.assoc, ← Category.assoc qZ, hcT]
    simp only [gT, Category.assoc, hqP_fst, IsPullback.isoPullback_hom_fst, Iso.hom_inv_id_assoc]
  ·

    let uA : Spec (CommRingCat.of A) ⟶ pullback (𝟙 (Spec (CommRingCat.of A₀))) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) :=
      pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) (𝟙 _) (by simp)
    have huA : uA ≫ gS = ε ≫ hg₁.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp, Category.assoc,
          IsPullback.isoPullback_hom_fst]
      · rw [Category.assoc, hgS, pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, hε]
    have huS : (uA ≫ qS) ≫ pullback.snd (𝟙 _) _ = Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) := by
      rw [Category.assoc, hqS_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
    rw [← Category.assoc, ← huA, Category.assoc, ← hcS, ← Category.assoc, ← huS]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]

end FrameKit19

namespace FrameKit19

theorem specMap_algebraMap_comp_tower (A₀ B A : Type u) [CommRing A₀] [CommRing B] [CommRing A] [Algebra A₀ B] [Algebra B A]
    [Algebra A₀ A] [IsScalarTower A₀ B A] :
    Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem stage_closed
    {A₀ : Type u} [CommRing A₀] {B : Type u} [CommRing B] [Algebra A₀ B] {A : Type u} [CommRing A] [Algebra B A] [Algebra A₀ A]
    [IsScalarTower A₀ B A] [Algebra.FiniteType A₀ B] (N : ℕ)
    {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of B)) [Smooth w] [IsProper w] [GeometricallyConnected w]
    (m : W ⟶ pullback (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
    (hm : m ≫ pullback.snd _ _ = w)
    (σ : Spec (CommRingCat.of B) ⟶ W) (hσ : σ ≫ w = 𝟙 _)
    {Z : Scheme.{u}} {f : Z ⟶ Spec (CommRingCat.of A)} (r : Z ⟶ W)
    (hr : IsPullback r f w (Spec.map (CommRingCat.ofHom (algebraMap B A))))
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π A N = f)
    (hcompat : ι ≫ ProjSpace.map A₀ A N = r ≫ m ≫ pullback.fst _ _)
    (ε : Spec (CommRingCat.of A) ⟶ Z) (hε : ε ≫ f = 𝟙 _) (hεσ : ε ≫ r = Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ σ) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG) (Z₀ : Scheme.{u}) (f₀ : Z₀ ⟶ Spec (CommRingCat.of ↥T)) (g : Z ⟶ Z₀),
      IsPullback g f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
      Smooth f₀ ∧ IsProper f₀ ∧ GeometricallyConnected f₀ ∧
      (∃ ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ↥T), IsClosedImmersion ι₀ ∧ ι₀ ≫ ProjSpace.π ↥T N = f₀) ∧
      ∃ ε₀ : Spec (CommRingCat.of ↥T) ⟶ Z₀, ε₀ ≫ f₀ = 𝟙 _ ∧ ε ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) ≫ ε₀ := by
  classical
  have hmv : Smooth (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))) := by rw [hm]; infer_instance
  have hmv' : IsProper (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))) := by rw [hm]; infer_instance
  have hmv'' : GeometricallyConnected (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))) := by
    rw [hm]; infer_instance
  haveI : QuasiCompact m := QuasiCompact.of_comp m (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
  haveI : QuasiSeparated m := QuasiSeparated.of_comp m (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
  haveI : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
  have hP := ProjSpace.isPullback_map A₀ A N
  have hjB : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A₀ B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := specMap_algebraMap_comp_tower A₀ B A
  have hr' : IsPullback r f (m ≫ pullback.snd _ _) (Spec.map (CommRingCat.ofHom (algebraMap B A))) := by rw [hm]; exact hr

  have hA : ∀ mA : pullback (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
        (Spec.map (CommRingCat.ofHom (algebraMap B A))) ⟶
        pullback (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
          (Spec.map (CommRingCat.ofHom (algebraMap B A))),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mA ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mA := by
    intro mA h1 h2
    have big := (IsPullback.of_hasPullback (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B A)))).paste_horiz
      (IsPullback.of_hasPullback (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
    rw [hjB] at big
    let eW := hr'.isoPullback
    let eV := hP.isoIsPullback _ _ big
    have heW_fst : eW.hom ≫ pullback.fst _ _ = r := hr'.isoPullback_hom_fst
    have heW_snd : eW.hom ≫ pullback.snd _ _ = f := hr'.isoPullback_hom_snd
    have heV_fst : eV.hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ = ProjSpace.map A₀ A N := hP.isoIsPullback_hom_fst _ _ big
    have heV_snd : eV.hom ≫ pullback.snd _ _ = ProjSpace.π A N := hP.isoIsPullback_hom_snd _ _ big
    have key : eW.hom ≫ mA = ι ≫ eV.hom := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [reassoc_of% h1, reassoc_of% heW_fst, heV_fst, hcompat]
        · simp only [Category.assoc]
          rw [pullback.condition, reassoc_of% h2, reassoc_of% heW_snd, reassoc_of% heV_snd, reassoc_of% hι]
      · simp only [Category.assoc]
        rw [h2, heW_snd, heV_snd, hι]
    have : mA = eW.inv ≫ ι ≫ eV.hom := by rw [← key, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  obtain ⟨T, hTfg, -, hmT⟩ :=
    AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact (A₀ := B) (A := A)
      m (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))) hA ∅

  let mT : pullback (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
        (Spec.map (CommRingCat.ofHom (algebraMap B ↥T))) ⟶
      pullback (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
        (Spec.map (CommRingCat.ofHom (algebraMap B ↥T))) :=
    pullback.lift (pullback.fst _ _ ≫ m) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have hmTci : IsClosedImmersion mT := hmT mT (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have bigT := (IsPullback.of_hasPullback (pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)))).paste_horiz
      (IsPullback.of_hasPullback (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
  rw [specMap_algebraMap_comp_tower A₀ B ↥T] at bigT
  let θ := bigT.isoIsPullback _ _ (ProjSpace.isPullback_map A₀ ↥T N)
  have hθ : θ.hom ≫ ProjSpace.π ↥T N = pullback.snd _ _ := bigT.isoIsPullback_hom_snd _ _ _

  obtain ⟨q, hq_fst, hq_snd⟩ := exists_transition T (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
  have hg := isPullback_comp_transition T _ r hr' q hq_fst hq_snd
  have hε₀w : (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)) ≫ σ) ≫
      (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))) =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B ↥T)) := by
    rw [hm, Category.assoc, hσ, Category.comp_id, Category.id_comp]
  have hfgT : (T.restrictScalars A₀).FG := by
    have i2 : Algebra.FiniteType B ↥T := (Subalgebra.fg_iff_finiteType _).1 hTfg
    have i3 : Algebra.FiniteType A₀ ↥T := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A₀ B) i2
    exact (Subalgebra.fg_iff_finiteType (T.restrictScalars A₀)).2 i3
  have hs₀ : Smooth (pullback.snd (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)))) := inferInstance
  have hp₀ : IsProper (pullback.snd (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)))) := inferInstance
  have hc₀ : GeometricallyConnected (pullback.snd (m ≫ pullback.snd (ProjSpace.π A₀ N) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)))) := inferInstance
  have hι₀ci : IsClosedImmersion (mT ≫ θ.hom) := inferInstance
  have hι₀ : (mT ≫ θ.hom) ≫ ProjSpace.π ↥T N = pullback.snd _ _ := by rw [Category.assoc, hθ, pullback.lift_snd]
  have hε₀ : pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)) ≫ σ) (𝟙 _) hε₀w ≫ pullback.snd _ _ = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hεc : ε ≫ hr'.isoPullback.hom ≫ q =
      Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) ≫ pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)) ≫ σ) (𝟙 _) hε₀w := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hq_fst, pullback.lift_fst]
      rw [hr'.isoPullback_hom_fst, hεσ, ← Category.assoc, specMap_algebraMap_comp_tower B ↥T A]
    · simp only [Category.assoc, hq_snd, pullback.lift_snd, Category.comp_id]
      rw [reassoc_of% hr'.isoPullback_hom_snd, reassoc_of% hε]
  exact ⟨T.restrictScalars A₀, hfgT, pullback (m ≫ pullback.snd _ _) (Spec.map (CommRingCat.ofHom (algebraMap B ↥T))), pullback.snd _ _,
    hr'.isoPullback.hom ≫ q, hg, hs₀, hp₀, hc₀, ⟨mT ≫ θ.hom, hι₀ci, hι₀⟩,
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap B ↥T)) ≫ σ) (𝟙 _) hε₀w, hε₀, hεc⟩

end FrameKit19

open NeronModelInfra GoodReductionJacobian

theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (S₁ : Subalgebra ℤ S) (hS₁ : S₁.FG) (Z₁ : Scheme.{u}) (f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥S₁)) (g₁ : Z ⟶ Z₁)
    (hg₁ : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ S))))
    (hsm₁ : Smooth f₁) (hpr₁ : IsProper f₁) (hgc₁ : GeometricallyConnected f₁) :
    ∃ (S₀ : Subalgebra ℤ S) (_ : S₀.FG) (Z₀ : Scheme.{u}) (f₀ : Z₀ ⟶ Spec (CommRingCat.of ↥S₀)) (g : Z ⟶ Z₀),
      IsPullback g f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S))) ∧
      Smooth f₀ ∧ IsProper f₀ ∧
      (∃ (N₀ : ℕ) (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N₀ + 1)) ↥S₀)),
        IsClosedImmersion ι₀ ∧ ι₀ ≫ ProjSpace.π ↥S₀ N₀ = f₀) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x₀ : ↥S₀ →+* k),
        ConnectedSpace ↥(pullback f₀ (Spec.map (CommRingCat.ofHom x₀)))) ∧
      ∃ ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥S₀))) f₀,
        ε.1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S)) ≫ ε₀.1 := by
  classical
  obtain ⟨N, ι, hιci, hιπ⟩ := hproj
  haveI := hsm₁
  haveI := hpr₁
  haveI := hgc₁
  haveI := hιci
  haveI : Algebra.FiniteType ℤ ↥S₁ := (Subalgebra.fg_iff_finiteType _).1 hS₁
  haveI : IsNoetherianRing ↥S₁ := Algebra.FiniteType.isNoetherianRing ℤ ↥S₁
  obtain ⟨T₁, hT₁fg, m, hm, σ, hσ, r, hr, hcompat, hεσ⟩ :=
    FrameKit19.stage_frame (A₀ := ↥S₁) f₁ N g₁ hg₁ ι hιπ ε.1 ε.2
  haveI : IsScalarTower ↥S₁ ↥T₁ S := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Algebra.FiniteType ↥S₁ ↥T₁ := (Subalgebra.fg_iff_finiteType _).1 hT₁fg
  obtain ⟨T₂, hT₂fg, Z₀, f₀, g, hg, hsm₀, hpr₀, hgc₀, ⟨ι₀, hι₀ci, hι₀π⟩, ε₀, hε₀, hεc⟩ :=
    FrameKit19.stage_closed (A₀ := ↥S₁) (B := ↥T₁) (A := S) N
      (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ ↥T₁)))) m hm σ hσ r hr ι hιπ hcompat ε.1 ε.2 hεσ
  have hfg : (T₂.restrictScalars ℤ).FG := by
    have i3 : Algebra.FiniteType ↥S₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).1 hT₂fg
    have i4 : Algebra.FiniteType ℤ ↥T₂ := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ ↥S₁) i3
    exact (Subalgebra.fg_iff_finiteType (T₂.restrictScalars ℤ)).2 i4
  have hgeo : geometrically (fun X => ConnectedSpace X) f₀ := by
    rw [← GeometricallyConnected.eq_geometrically]; exact hgc₀
  exact ⟨T₂.restrictScalars ℤ, hfg, Z₀, f₀, g, hg, hsm₀, hpr₀, ⟨N, ι₀, hι₀ci, hι₀π⟩,
    fun k _ _ x₀ => pullback_of_geometrically hgeo k (Spec.map (CommRingCat.ofHom x₀)), ⟨ε₀, hε₀⟩, hεc⟩

end
end S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback (solution)
