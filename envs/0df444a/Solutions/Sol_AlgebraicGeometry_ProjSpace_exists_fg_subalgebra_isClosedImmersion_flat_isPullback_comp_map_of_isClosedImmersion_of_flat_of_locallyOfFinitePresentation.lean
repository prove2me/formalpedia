-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/798fed87-36eb-5699-8539-7d0fbc583368

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjFlatDescent25

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

theorem map_comp_map (A₀ B A : Type u) [CommRing A₀] [CommRing B] [CommRing A] [Algebra A₀ B] [Algebra B A]
    [Algebra A₀ A] [IsScalarTower A₀ B A] (n : ℕ) :
    ProjSpace.map B A n ≫ ProjSpace.map A₀ B n = ProjSpace.map A₀ A n := by
  have h : (ProjSpace.mvMapGraded B A n).comp (ProjSpace.mvMapGraded A₀ B n) = ProjSpace.mvMapGraded A₀ A n := by
    apply GradedRingHom.ext
    intro x
    rw [GradedRingHom.coe_comp, Function.comp_apply]
    change MvPolynomial.map (algebraMap B A) (MvPolynomial.map (algebraMap A₀ B) x) = MvPolynomial.map (algebraMap A₀ A) x
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have key : ∀ (f g : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ →+*ᵍ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A),
      f = g → ∀ hf hg, Proj.map f hf = Proj.map g hg := by
    intro f g hfg hf hg; subst hfg; rfl
  rw [ProjSpace.map_eq, ProjSpace.map_eq, ProjSpace.map_eq, ← Proj.map_comp]
  exact key _ _ h _ _

theorem fg_restrictScalars {L : Type u} [CommRing L] (R₁ : Subalgebra ℤ L) (T : Subalgebra ↥R₁ L)
    (h₁ : R₁.FG) (h₂ : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 h₂
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

theorem isNoetherianRing_of_fg {L : Type u} [CommRing L] (R : Subalgebra ℤ L) (hR : R.FG) : IsNoetherianRing ↥R := by
  haveI : Algebra.FiniteType ℤ ↥R := (Subalgebra.fg_iff_finiteType _).1 hR
  exact Algebra.FiniteType.isNoetherianRing ℤ ↥R

variable {S : Type u} [CommRing S]

attribute [local instance] ULift.algebra' in

theorem stage_model {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    ∃ (R : Subalgebra ℤ S) (_ : R.FG) (X : Scheme.{u}) (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X),
      IsPullback c f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))) ∧ IsProper f₁ ∧ Flat f₁ := by
  haveI : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T, hT, -, X, f₁, c, hpr, hfl, hc⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := ULift.{u} ℤ) (A := S) f (∅ : Finset S)
  have i1 : Algebra.FiniteType ℤ (ULift.{u} ℤ) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId ℤ (ULift.{u} ℤ)) (fun x => ⟨x.down, rfl⟩)
  have i2 : Algebra.FiniteType (ULift.{u} ℤ) ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact ⟨T.restrictScalars ℤ, (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3, X, f₁, c, hc, hpr, hfl⟩

theorem stage_frame (R : Subalgebra ℤ S) (hR : R.FG) {Z₁ : Scheme.{u}} (f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥R))
    [IsProper f₁] [Flat f₁] (n : ℕ) {Z : Scheme.{u}} (c₁ : Z ⟶ Z₁)
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S))
    (hc₁ : IsPullback c₁ (ι ≫ ProjSpace.π S n) f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S)))) :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (W : Scheme.{u}) (w : W ⟶ Spec (CommRingCat.of ↥R'))
      (m : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ↥R')) (r : Z ⟶ W),
      IsProper w ∧ Flat w ∧ LocallyOfFinitePresentation w ∧ m ≫ ProjSpace.π ↥R' n = w ∧
      IsPullback r (ι ≫ ProjSpace.π S n) w (Spec.map (CommRingCat.ofHom (algebraMap ↥R' S))) ∧
      ι ≫ ProjSpace.map ↥R' S n = r ≫ m := by
  classical
  haveI : IsNoetherianRing ↥R := isNoetherianRing_of_fg R hR
  haveI : LocallyOfFinitePresentation (ProjSpace.π ↥R n) := locallyOfFinitePresentation_of_isNoetherianRing _
  haveI : LocallyOfFinitePresentation f₁ := locallyOfFinitePresentation_of_isNoetherianRing _
  have hP := ProjSpace.isPullback_map ↥R S n

  let gT : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))) ⟶
      pullback (ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))) :=
    hc₁.isoPullback.inv ≫ ι ≫ hP.isoPullback.hom
  have hgT : gT ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [gT, Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd]
  obtain ⟨T, hTfg, -, m₀, hm₀, hcompat⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (A₀ := ↥R) (A := S) f₁ (ProjSpace.π ↥R n) gT hgT ∅
  haveI : IsScalarTower ↥R ↥T S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  obtain ⟨qZ, hqZ_fst, hqZ_snd⟩ := exists_transition T f₁
  obtain ⟨qP, hqP_fst, hqP_snd⟩ := exists_transition T (ProjSpace.π ↥R n)
  have hr := isPullback_comp_transition T f₁ c₁ hc₁ qZ hqZ_fst hqZ_snd
  have hcT : qZ ≫ m₀ = gT ≫ qP := hcompat qZ qP hqZ_fst hqZ_snd hqP_fst hqP_snd

  have hPT := ProjSpace.isPullback_map ↥R ↥T n
  let θ := (IsPullback.of_hasPullback (ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T)))).isoIsPullback
    _ _ hPT
  have hθ_fst : θ.hom ≫ ProjSpace.map ↥R ↥T n = pullback.fst _ _ := IsPullback.isoIsPullback_hom_fst _ _ _ hPT
  have hθ_snd : θ.hom ≫ ProjSpace.π ↥T n = pullback.snd _ _ := IsPullback.isoIsPullback_hom_snd _ _ _ hPT

  have hpr : IsProper (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T)))) := inferInstance
  have hfl : Flat (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T)))) := inferInstance
  have hlfp : LocallyOfFinitePresentation (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T)))) := inferInstance
  have hm : (m₀ ≫ θ.hom) ≫ ProjSpace.π ↥T n = pullback.snd f₁ _ := by rw [Category.assoc, hθ_snd, hm₀]
  have hc : ι ≫ ProjSpace.map ↥T S n = (hc₁.isoPullback.hom ≫ qZ) ≫ m₀ ≫ θ.hom := by
    apply hPT.hom_ext
    · rw [Category.assoc, map_comp_map ↥R ↥T S n]
      simp only [Category.assoc]
      rw [hθ_fst, ← Category.assoc qZ, hcT]
      simp only [gT, Category.assoc, hqP_fst, IsPullback.isoPullback_hom_fst, Iso.hom_inv_id_assoc]
    · simp only [Category.assoc]
      rw [(ProjSpace.isPullback_map ↥T S n).w, hθ_snd, hm₀, ← Category.assoc, ← Category.assoc, hr.w, Category.assoc]
  exact ⟨T.restrictScalars ℤ, fg_restrictScalars R T hR hTfg,
    pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))), pullback.snd f₁ _, m₀ ≫ θ.hom,
    hc₁.isoPullback.hom ≫ qZ, hpr, hfl, hlfp, hm, hr, hc⟩

theorem exists_projIso (A₀ B : Type u) [CommRing A₀] [CommRing B] [Algebra A₀ B] (n : ℕ) :
    ∃ θ : pullback (ProjSpace.π A₀ n) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B))) ≅
        Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B),
      θ.hom ≫ ProjSpace.map A₀ B n = pullback.fst _ _ ∧ θ.hom ≫ ProjSpace.π B n = pullback.snd _ _ :=
  ⟨(IsPullback.of_hasPullback (ProjSpace.π A₀ n) (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))).isoIsPullback _ _
      (ProjSpace.isPullback_map A₀ B n),
    IsPullback.isoIsPullback_hom_fst _ _ _ _, IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

theorem isClosedImmersion_of_docked (R : Subalgebra ℤ S) (n : ℕ)
    {W : Scheme.{u}} (m : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ↥R))
    {Z : Scheme.{u}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)) [IsClosedImmersion ι]
    (r : Z ⟶ W)
    (hr' : IsPullback r (ι ≫ ProjSpace.π S n) (m ≫ ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))))
    (hcompat : ι ≫ ProjSpace.map ↥R S n = r ≫ m)
    (mA : pullback (m ≫ ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))) ⟶
        pullback (ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))))
    (h1 : mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m) (h2 : mA ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsClosedImmersion mA := by
  have hP := ProjSpace.isPullback_map ↥R S n
  have heW_fst : hr'.isoPullback.hom ≫ pullback.fst _ _ = r := hr'.isoPullback_hom_fst
  have heW_snd : hr'.isoPullback.hom ≫ pullback.snd _ _ = ι ≫ ProjSpace.π S n := hr'.isoPullback_hom_snd
  have heV_fst : hP.isoPullback.hom ≫ pullback.fst _ _ = ProjSpace.map ↥R S n := hP.isoPullback_hom_fst
  have heV_snd : hP.isoPullback.hom ≫ pullback.snd _ _ = ProjSpace.π S n := hP.isoPullback_hom_snd
  have key : hr'.isoPullback.hom ≫ mA = ι ≫ hP.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [h1, reassoc_of% heW_fst, heV_fst, hcompat]
    · simp only [Category.assoc]
      rw [h2, heW_snd, heV_snd]
  have : mA = hr'.isoPullback.inv ≫ ι ≫ hP.isoPullback.hom := by rw [← key, Iso.inv_hom_id_assoc]
  rw [this]; infer_instance

theorem stage_closed (R : Subalgebra ℤ S) (hR : R.FG) (n : ℕ)
    {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of ↥R)) [IsProper w] [Flat w] [LocallyOfFinitePresentation w]
    (m : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ↥R)) (hm : m ≫ ProjSpace.π ↥R n = w)
    {Z : Scheme.{u}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)) [IsClosedImmersion ι]
    (r : Z ⟶ W) (hr : IsPullback r (ι ≫ ProjSpace.π S n) w (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))))
    (hcompat : ι ≫ ProjSpace.map ↥R S n = r ≫ m) :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (Z₀ : Scheme.{u})
      (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ↥R')) (g : Z ⟶ Z₀),
      IsClosedImmersion ι₀ ∧ Flat (ι₀ ≫ ProjSpace.π ↥R' n) ∧ LocallyOfFinitePresentation (ι₀ ≫ ProjSpace.π ↥R' n) ∧
      IsPullback g (ι ≫ ProjSpace.π S n) (ι₀ ≫ ProjSpace.π ↥R' n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R' S))) ∧
      g ≫ ι₀ = ι ≫ ProjSpace.map ↥R' S n := by
  classical
  have hmv : IsProper (m ≫ ProjSpace.π ↥R n) := by rw [hm]; infer_instance
  have hmv' : Flat (m ≫ ProjSpace.π ↥R n) := by rw [hm]; infer_instance
  have hmv'' : LocallyOfFinitePresentation (m ≫ ProjSpace.π ↥R n) := by rw [hm]; infer_instance
  haveI : QuasiCompact m := QuasiCompact.of_comp m (ProjSpace.π ↥R n)
  haveI : QuasiSeparated m := QuasiSeparated.of_comp m (ProjSpace.π ↥R n)
  haveI : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m (ProjSpace.π ↥R n)
  have hr' : IsPullback r (ι ≫ ProjSpace.π S n) (m ≫ ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R S))) := by
    rw [hm]; exact hr
  obtain ⟨T, hTfg, -, hmT⟩ :=
    AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact (A₀ := ↥R) (A := S)
      m (ProjSpace.π ↥R n) (isClosedImmersion_of_docked R n m ι r hr' hcompat) ∅
  haveI : IsScalarTower ↥R ↥T S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let mT : pullback (m ≫ ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) ⟶
      pullback (ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) :=
    pullback.lift (pullback.fst _ _ ≫ m) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have hmT_fst : mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m := pullback.lift_fst _ _ _
  have hmT_snd : mT ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hmTci : IsClosedImmersion mT := hmT mT hmT_fst hmT_snd
  obtain ⟨θ, hθ_fst, hθ_snd⟩ := exists_projIso ↥R ↥T n
  have hPT := ProjSpace.isPullback_map ↥R ↥T n

  obtain ⟨q, hq_fst, hq_snd⟩ := exists_transition T (m ≫ ProjSpace.π ↥R n)
  have hg := isPullback_comp_transition T _ r hr' q hq_fst hq_snd
  have hι₀ : (mT ≫ θ.hom) ≫ ProjSpace.π ↥T n =
      pullback.snd (m ≫ ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) := by
    rw [Category.assoc, hθ_snd, hmT_snd]
  have hci : IsClosedImmersion (mT ≫ θ.hom) := inferInstance
  have hfl : Flat ((mT ≫ θ.hom) ≫ ProjSpace.π ↥T n) := by rw [hι₀]; infer_instance
  have hlfp : LocallyOfFinitePresentation ((mT ≫ θ.hom) ≫ ProjSpace.π ↥T n) := by rw [hι₀]; infer_instance
  have hg' : IsPullback (hr'.isoPullback.hom ≫ q) (ι ≫ ProjSpace.π S n) ((mT ≫ θ.hom) ≫ ProjSpace.π ↥T n)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) := by
    rw [hι₀]; exact hg
  have hgι : (hr'.isoPullback.hom ≫ q) ≫ mT ≫ θ.hom = ι ≫ ProjSpace.map ↥T S n := by
    apply hPT.hom_ext
    · simp only [Category.assoc]
      rw [hθ_fst, hmT_fst, ← Category.assoc q, hq_fst, ← Category.assoc, hr'.isoPullback_hom_fst, ← hcompat,
        map_comp_map ↥R ↥T S n]
    · simp only [Category.assoc]
      rw [hθ_snd, hmT_snd, hq_snd, ← Category.assoc, hr'.isoPullback_hom_snd,
        (ProjSpace.isPullback_map ↥T S n).w, Category.assoc]
  exact ⟨T.restrictScalars ℤ, fg_restrictScalars R T hR hTfg,
    pullback (m ≫ ProjSpace.π ↥R n) (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))), mT ≫ θ.hom,
    hr'.isoPullback.hom ≫ q, hci, hfl, hlfp, hg', hgι⟩

end ProjFlatDescent25

open ProjFlatDescent25 in
theorem solution
    {A : Type u} [CommRing A] (n : ℕ)
    (Z : Scheme.{u}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ ProjSpace.π A n))
    (hfp : LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n)) :
    ∃ (A₀ : Subalgebra ℤ A), A₀.FG ∧
      ∃ (Z₀ : Scheme.{u}) (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ↥A₀)) (g : Z ⟶ Z₀),
        IsClosedImmersion ι₀ ∧ Flat (ι₀ ≫ ProjSpace.π ↥A₀ n) ∧ LocallyOfFinitePresentation (ι₀ ≫ ProjSpace.π ↥A₀ n) ∧
        IsPullback g (ι ≫ ProjSpace.π A n) (ι₀ ≫ ProjSpace.π ↥A₀ n)
          (Spec.map (CommRingCat.ofHom (algebraMap ↥A₀ A))) ∧
        g ≫ ι₀ = ι ≫ ProjSpace.map ↥A₀ A n := by
  classical
  haveI := hι
  haveI := hfl
  haveI := hfp
  haveI : IsProper (ι ≫ ProjSpace.π A n) := inferInstance

  obtain ⟨R₁, hR₁, Z₁, f₁, c₁, hc₁, hpr₁, hfl₁⟩ := stage_model (ι ≫ ProjSpace.π A n)
  haveI := hpr₁
  haveI := hfl₁

  obtain ⟨R₂, hR₂, W, w, m, r, hprw, hflw, hlfpw, hm, hr, hcompat⟩ := stage_frame R₁ hR₁ f₁ n c₁ ι hc₁
  haveI := hprw
  haveI := hflw
  haveI := hlfpw

  obtain ⟨R₃, hR₃, Z₀, ι₀, g, h₁, h₂, h₃, h₄, h₅⟩ := stage_closed R₂ hR₂ n w m hm ι r hr hcompat
  exact ⟨R₃, hR₃, Z₀, ι₀, g, h₁, h₂, h₃, h₄, h₅⟩

end
end S_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation (solution)
