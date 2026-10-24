-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_generic_curve_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T21:29:25.920019+00:00
-- url     : https://prove2.me/submissions/165dd43d-e89c-41f0-83eb-77fe9fa5d5c4

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_projection_with_dense_smooth_open
import Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

universe u
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponAlterationProjection
/-- The canonical map from a local spectrum is flat. -/
lemma flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  dsimp only [IsAffineOpen.fromSpecStalk]
  haveI : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    apply Flat.SpecMap_iff.mpr
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := hU.isLocalization_stalk ⟨x, hx⟩
    change (algebraMap Γ(X, U) (X.presheaf.stalk x)).Flat
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  infer_instance

/-- The generic-point residue-field inclusion into an integral scheme is flat. -/
lemma flat_fromSpecResidueField_genericPoint (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  have hbij : Function.Bijective (Y.residue (genericPoint Y)) :=
    ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩
  letI : IsIso (Y.residue (genericPoint Y)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI := flat_fromSpecStalk Y (genericPoint Y)
  dsimp only [Scheme.fromSpecResidueField]
  infer_instance

/-- A dominant morphism maps the generic point of an integral source to that of its target. -/
lemma genericPoint_eq_of_dominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  have hg : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec Y)

lemma isIntegral_genericFiber
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsIntegral (f.fiber (genericPoint Y)) :=
  AlgebraicGeometry.isIntegral_genericFiber_of_isDominant f
end PhilipponAlterationProjection


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationProjection

/-- A flat preimmersion induces isomorphisms on local rings. -/
lemma isIso_stalkMap_of_flat_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] (x : X) :
    IsIso (f.stalkMap x) := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  have hff : RingHom.FaithfullyFlat (f.stalkMap x).hom := this
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨hff.injective, f.stalkMap_surjective x⟩

/-- The generic-fibre inclusion preserves all local rings. -/
lemma isIso_stalkMap_genericFiber
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (x : f.fiber (genericPoint Y)) : IsIso ((f.fiberι (genericPoint Y)).stalkMap x) := by
  haveI : Flat (f.fiberι (genericPoint Y)) :=
    MorphismProperty.pullback_fst f (Y.fromSpecResidueField (genericPoint Y))
      (flat_fromSpecResidueField_genericPoint Y)
  exact isIso_stalkMap_of_flat_preimmersion (f.fiberι (genericPoint Y)) x

/-- Normal local rings are retained in the generic fibre. -/
lemma integrallyClosed_stalk_genericFiber
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (z : f.fiber (genericPoint Y)) :
    IsIntegrallyClosed ((f.fiber (genericPoint Y)).presheaf.stalk z) := by
  letI := hnormal (f.fiberι (genericPoint Y) z)
  letI : IsIso ((f.fiberι (genericPoint Y)).stalkMap z) := isIso_stalkMap_genericFiber f z
  exact IsIntegrallyClosed.of_equiv
    (asIso ((f.fiberι (genericPoint Y)).stalkMap z)).commRingCatIsoToRingEquiv

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponAlterationProjection

abbrev residueAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma preimage_residue_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  apply ext_of_isAffine
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  have ht : (Spec.map (Scheme.ΓSpecIso (.of K)).inv).appTop =
      (Scheme.ΓSpecIso Γ(Spec (.of K), ⊤)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
    exact (Scheme.ΓSpecIso_inv_naturality (Scheme.ΓSpecIso (.of K)).inv).symm
  simp
  simp only [Scheme.Hom.appTop] at ht ⊢
  rw [ht]

lemma residue_tower {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X) :
    letI := residueAlgebra g (f x)
    letI := residueAlgebra (f ≫ g) x
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  letI := residueAlgebra g (f x)
  letI := residueAlgebra (f ≫ g) x
  letI := (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := congrArg Spec.preimage
    (congrArg (fun a => a ≫ g)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map,
    preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h


lemma dimension_eq_of_open_immersion {K : Type u} [Field K]
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (f : U ⟶ W) [IsOpenImmersion f]
    (d : W ⟶ Spec (.of K)) [LocallyOfFiniteType d] :
    topologicalKrullDim U = topologicalKrullDim W := by
  let u := genericPoint U
  let L := W.residueField (f u)
  let E := U.residueField u
  letI : Algebra K L := residueAlgebra d (f u)
  letI : Algebra K E := residueAlgebra (f ≫ d) u
  letI : Algebra L E := (f.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower f d u
  letI : IsIso (f.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion f u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  have hW := toENat_trdeg_residueField_eq_topologicalKrullDim_closure d (f u)
  have hU := toENat_trdeg_residueField_eq_topologicalKrullDim_closure (f ≫ d) u
  have hgen : f u = genericPoint W := genericPoint_eq_of_isOpenImmersion f
  have hclW : closure ({f u} : Set W) = Set.univ := by rw [hgen]; exact genericPoint_spec W
  have hclU : closure ({u} : Set U) = Set.univ := genericPoint_spec U
  have hdW : topologicalKrullDim W = topologicalKrullDim (closure ({f u} : Set W)) := by
    rw [hclW]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ W)
      (Homeomorph.Set.univ W).isHomeomorph).symm
  have hdU : topologicalKrullDim U = topologicalKrullDim (closure ({u} : Set U)) := by
    rw [hclU]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ U)
      (Homeomorph.Set.univ U).isHomeomorph).symm
  rw [hdU, hdW, ← hU, ← hW]
  change (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞)
  rw [he]

end PhilipponAlterationProjection


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section

namespace PhilipponAlterationProjection

lemma isDominant_genericFiberι
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsDominant (f.fiberι (genericPoint Y)) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)) := by
    refine ⟨(f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant f⟩, ?_⟩
    exact f.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (f.fiberι (genericPoint Y)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma residue_base_tower {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of F)) (x : X) :
    letI := residueAlgebra s x
    letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
    IsScalarTower K F (X.residueField x) := by
  letI := residueAlgebra s x
  letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := Spec.preimage_comp (X.fromSpecResidueField x ≫ s)
    (Spec.map (CommRingCat.ofHom (algebraMap K F)))
  rw [Spec.preimage_map] at h
  simp only [Category.assoc, preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h

lemma dimension_eq_trdeg_of_genericPoint {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (x : X) (hx : x = genericPoint X) :
    letI := residueAlgebra c x
    topologicalKrullDim X = (Cardinal.toENat (Algebra.trdeg K (X.residueField x)) : WithBot ℕ∞) := by
  letI := residueAlgebra c x
  have h := toENat_trdeg_residueField_eq_topologicalKrullDim_closure c x
  have hcl : closure ({x} : Set X) = Set.univ := by rw [hx]; exact genericPoint_spec X
  have hd : topologicalKrullDim X = topologicalKrullDim (closure ({x} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  exact hd.trans h.symm

/-- Dimensions add along the actual generic fibre, with the structure-field maps retained. -/
theorem dimension_eq_add_genericFiber
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : Y ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    topologicalKrullDim X = topologicalKrullDim Y +
      topologicalKrullDim (f.fiber (genericPoint Y)) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ c)
  let η := genericPoint Y
  let F := Y.residueField η
  let C := f.fiber η
  let s : C ⟶ Spec F := f.fiberToSpecResidueField η
  let t : C ⟶ X := f.fiberι η
  letI : IsIntegral C := isIntegral_genericFiber f
  letI : IsDominant t := isDominant_genericFiberι f
  let u := genericPoint C
  let z := t u
  let E := C.residueField u
  let L := X.residueField z
  letI : Algebra K F := residueAlgebra c η
  letI : Algebra F E := residueAlgebra s u
  letI : Algebra K E := residueAlgebra (t ≫ (f ≫ c)) u
  letI : Algebra K L := residueAlgebra (f ≫ c) z
  letI : Algebra L E := (t.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower t (f ≫ c) u
  have hbase : t ≫ (f ≫ c) = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    change f.fiberι η ≫ (f ≫ c) =
      f.fiberToSpecResidueField η ≫ Spec.map
        ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop ≫
          Y.presheaf.germ ⊤ η trivial ≫ Y.residue η)
    rw [← preimage_residue_comp, Spec.map_preimage, ← Category.assoc, f.fiber_fac]
    exact Category.assoc _ _ _
  letI : IsScalarTower K F E := by
    apply IsScalarTower.of_algebraMap_eq'
    have hmap : (algebraMap F E).comp (algebraMap K F) =
        (residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u).algebraMap := by
      letI : Algebra K E := residueAlgebra
        (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u
      letI : IsScalarTower K F E := residue_base_tower (K := K) (F := F) s u
      exact (IsScalarTower.algebraMap_eq K F E).symm
    exact (hmap.trans (congrArg (fun a => (residueAlgebra a u).algebraMap) hbase.symm)).symm
  letI : IsIso (t.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion t u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (t.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  letI : LocallyOfFiniteType s := MorphismProperty.pullback_snd f
    (Y.fromSpecResidueField η) (inferInstance : LocallyOfFiniteType f)
  have hX := dimension_eq_trdeg_of_genericPoint (f ≫ c) z (genericPoint_eq_of_dominant t)
  have hY := dimension_eq_trdeg_of_genericPoint c η rfl
  have hC := dimension_eq_trdeg_of_genericPoint (K := F) s u rfl
  rw [hX, hY, hC]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K F) : WithBot ℕ∞) +
      (Cardinal.toENat (Algebra.trdeg F E) : WithBot ℕ∞)
  rw [he, ← trdeg_add_eq K F (A := E)]
  simp only [map_add, WithBot.coe_add]

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma projective_space_irreducible (K : Type u) [Field K] (n : ℕ) :
    IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K
  have hprime : (⊥ : HomogeneousIdeal 𝒜).toIdeal.IsPrime := by
    change (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)).IsPrime
    infer_instance
  have hrel : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ := by
    intro h
    have hX : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ K) ∈
        HomogeneousIdeal.irrelevant 𝒜 :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
        (ProjSpace.X_mem_one K n 0)
    have hz : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ K) = 0 := by
      change MvPolynomial.X 0 ∈ (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K))
      exact h hX
    exact MvPolynomial.X_ne_zero _ hz
  let η : ProjectiveSpectrum 𝒜 := ⟨⊥, hprime, hrel⟩
  have hη : IsGenericPoint η (Set.univ : Set (ProjectiveSpectrum 𝒜)) := by
    apply Set.eq_univ_of_forall
    intro y
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η y).mp (show
      η.asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  exact (irreducibleSpace_def _).mpr hη.isIrreducible

end PhilipponAlterationProjection


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma projective_space_integral (K : Type u) [Field K] (r : ℕ) :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)
  letI : IrreducibleSpace P := projective_space_irreducible K r
  haveI (x : P) : _root_.IsReduced (P.presheaf.stalk x) := by
    let L := HomogeneousLocalization.AtPrime
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) x.asHomogeneousIdeal.toIdeal
    letI : _root_.IsReduced L := isReduced_of_injective
      (algebraMap L (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective x.asHomogeneousIdeal.toIdeal.primeCompl)
    let e := (Proj.stalkIso (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) x).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e e.injective
  letI : IsReduced P := isReduced_of_isReduced_stalk P
  exact isIntegral_of_irreducibleSpace_of_isReduced P

/-- A dominant projective-space projection has an actual integral fibre over its generic point. -/
lemma exists_integral_genericFiber_of_projective_projection
    (K : Type u) [Field K] (r : ℕ) {G : Scheme.{u}} [IsIntegral G] [IsLocallyNoetherian G]
    (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsDominant q] :
    ∃ η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K),
      IsGenericPoint η Set.univ ∧ IsIntegral (q.fiber η) := by
  letI := projective_space_integral K r
  exact ⟨genericPoint _, genericPoint_spec _, isIntegral_genericFiber q⟩

/-- The generic fibre of a normal proper dominant projective-space projection is an actual
integral normal proper scheme over the generic-point residue field. -/
lemma exists_normal_proper_genericFiber_of_projective_projection
    (K : Type u) [Field K] (r : ℕ) {G : Scheme.{u}} [IsIntegral G] [IsLocallyNoetherian G]
    (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsDominant q] [IsProper q]
    (hnormal : ∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) :
    ∃ η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K),
      IsGenericPoint η Set.univ ∧ IsIntegral (q.fiber η) ∧
      (∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z)) ∧
      IsProper (q.fiberToSpecResidueField η) ∧
      ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)
  letI : IsIntegral P := projective_space_integral K r
  let η := genericPoint P
  have hp : IsProper (q.fiberToSpecResidueField η) :=
    MorphismProperty.pullback_snd q (P.fromSpecResidueField η) (inferInstance : IsProper q)
  exact ⟨η, genericPoint_spec P, isIntegral_genericFiber q,
    integrallyClosed_stalk_genericFiber q hnormal, hp, isIso_stalkMap_genericFiber q⟩

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection.ProjectiveAffineChart
variable (R : Type u) [CommRing R] (n : ℕ)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
abbrev chartRing := Away (grading R n) (MvPolynomial.X (0 : Fin (n + 1)))

noncomputable def specialize :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

lemma specialize_X_zero : specialize R n (MvPolynomial.X (0 : Fin (n + 1))) = 1 := by
  simp [specialize]

lemma specialize_unit : IsUnit (specialize R n (MvPolynomial.X (0 : Fin (n + 1)))) :=
  isUnit_iff_exists_inv.mpr ⟨1, by rw [specialize_X_zero]; simp⟩

noncomputable def fromAway : chartRing R n →+* MvPolynomial (Fin n) R :=
  (Localization.awayLift (specialize R n) (MvPolynomial.X (0 : Fin (n + 1)))
    (specialize_unit R n)).comp
    (algebraMap (chartRing R n) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) :
      MvPolynomial (Fin (n + 1)) R)))

lemma fromAway_coeff (r : R) :
    fromAway R n (algebraMap R (chartRing R n) r) = MvPolynomial.C r := by
  change Localization.awayLift (specialize R n) _ (specialize_unit R n)
    ((algebraMap R (chartRing R n) r).val) = _
  rw [ProjSpace.val_algebraMap]
  simp only [Localization.awayLift, IsLocalization.Away.lift_eq]
  simp [specialize]

lemma fromAway_ratio (j : Fin (n + 1)) :
    fromAway R n (ProjSpace.ratio R n 0 j) = specialize R n (MvPolynomial.X j) := by
  change Localization.awayLift (specialize R n) _ (specialize_unit R n) (ProjSpace.ratio R n 0 j).val = _
  rw [ProjSpace.ratio, Away.val_mk]
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (specialize R n) (MvPolynomial.X (0 : Fin (n + 1)))
      (MvPolynomial.X j) 1 (by rw [specialize_X_zero]; simp) 1

noncomputable def fromAwayAlg : chartRing R n →ₐ[R] MvPolynomial (Fin n) R where
  __ := fromAway R n
  commutes' := fromAway_coeff R n

lemma fromAwayAlg_apply (x : chartRing R n) : fromAwayAlg R n x = fromAway R n x := rfl

noncomputable def toAwayAlg : MvPolynomial (Fin n) R →ₐ[R] chartRing R n :=
  MvPolynomial.aeval (fun j : Fin n => ProjSpace.ratio R n 0 j.succ)

lemma toAwayAlg_X (j : Fin n) : toAwayAlg R n (MvPolynomial.X j) = ProjSpace.ratio R n 0 j.succ :=
  MvPolynomial.aeval_X _ _

lemma from_to : (fromAwayAlg R n).comp (toAwayAlg R n) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, toAwayAlg_X, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  simp [specialize]

lemma to_from : (toAwayAlg R n).comp (fromAwayAlg R n) = AlgHom.id R _ := by
  apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R n 0)
  rintro _ ⟨j, rfl⟩
  simp only [AlgHom.comp_apply, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [specialize, ProjSpace.ratio_self]
  · simp [specialize, toAwayAlg]

noncomputable def equiv : chartRing R n ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (fromAwayAlg R n) (toAwayAlg R n) (from_to R n) (to_from R n)

/-- The standard affine-space chart in projective space. -/
noncomputable def embedding : Spec (.of (MvPolynomial (Fin n) R)) ⟶ Proj (grading R n) :=
  Spec.map (CommRingCat.ofHom (equiv R n).toRingEquiv.toRingHom) ≫
    Proj.awayι (grading R n) (MvPolynomial.X (0 : Fin (n + 1)))
      (ProjSpace.X_mem_one R n 0) one_pos

instance embedding_isOpenImmersion : IsOpenImmersion (embedding R n) := by
  haveI : IsIso (CommRingCat.ofHom (equiv R n).toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (equiv R n).bijective
  unfold embedding
  infer_instance

lemma embedding_over : embedding R n ≫ ProjSpace.π R n =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) := by
  rw [embedding, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (equiv R n).commutes r

end PhilipponAlterationProjection.ProjectiveAffineChart



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma affine_space_dimension (K : Type u) [Field K] (r : ℕ) :
    topologicalKrullDim (Spec (.of (MvPolynomial (Fin r) K))) = (r : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin r) K)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

lemma projective_space_dimension (K : Type u) [Field K] (r : ℕ) :
    topologicalKrullDim (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) =
      (r : WithBot ℕ∞) := by
  letI := projective_space_integral K r
  have h := dimension_eq_of_open_immersion (ProjectiveAffineChart.embedding K r) (ProjSpace.π K r)
  exact h.symm.trans (affine_space_dimension K r)

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma eq_one_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : ((r + 1 : ℕ) : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 1 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 1 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [Nat.cast_add, Nat.cast_one,
        WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_one] using h)
    have hd : d = 1 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

/-- A normal proper dominant projection with dimension drop one has a normal proper
integral generic curve, and its fibre inclusion preserves every local ring. -/
theorem exists_normal_proper_genericCurve_of_projective_projection
    (K : Type u) [Field K] (r : ℕ) {G : Scheme.{u}} [IsIntegral G]
    (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsDominant q] [IsProper q]
    (hnormal : ∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g))
    (hdim : topologicalKrullDim G = ((r + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K),
      IsGenericPoint η Set.univ ∧ IsIntegral (q.fiber η) ∧
      (∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z)) ∧
      IsProper (q.fiberToSpecResidueField η) ∧
      topologicalKrullDim (q.fiber η) = 1 ∧
      ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)
  letI : IsIntegral P := projective_space_integral K r
  letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (ProjSpace.π K r)
  letI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian q
  let η := genericPoint P
  have hadd := dimension_eq_add_genericFiber K (ProjSpace.π K r) q
  rw [hdim, projective_space_dimension K r] at hadd
  have hCdim : topologicalKrullDim (q.fiber η) = 1 := eq_one_of_nat_add_eq r _ hadd
  have hp : IsProper (q.fiberToSpecResidueField η) :=
    MorphismProperty.pullback_snd q (P.fromSpecResidueField η) (inferInstance : IsProper q)
  exact ⟨η, genericPoint_spec P, isIntegral_genericFiber q,
    integrallyClosed_stalk_genericFiber q hnormal, hp, hCdim, isIso_stalkMap_genericFiber q⟩

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

/-- The separating projection model has an actual normal proper integral generic curve. -/
theorem exists_normal_projective_generic_curve_model
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (r : ℕ) (G : Scheme.{u}) (p : G ⟶ X)
      (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)),
      0 < r ∧ IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
      topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞) ∧
      IsProper p ∧ Surjective p ∧ IsProper q ∧ Surjective q ∧
      p ≫ π = q ≫ ProjSpace.π K r ∧
      (∃ W : G.Opens, IsAffineOpen W ∧ Nonempty W ∧ Dense (W : Set G) ∧
        Smooth (W.ι ≫ q) ∧ (∀ w : W, IsIso (p.stalkMap w.val))) ∧
      (∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π) ∧
      ∃ η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K),
        IsGenericPoint η Set.univ ∧ IsIntegral (q.fiber η) ∧
        (∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z)) ∧
        IsProper (q.fiberToSpecResidueField η) ∧
        topologicalKrullDim (q.fiber η) = 1 ∧
        ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z) := by
  obtain ⟨r, G, p, q, hr, hG, hn, hdG, hdX, hp, hsp, hq, hsq, hbase, hW, hemb⟩ :=
    exists_normal_projective_projection_with_dense_smooth_open K π n i hi hnormalX hdim
  letI := hG
  letI := hq
  letI := hsq
  have hcurve := exists_normal_proper_genericCurve_of_projective_projection K r q hn
    (hdG.trans hdX)
  exact ⟨r, G, p, q, hr, hG, hn, hdG, hdX, hp, hsp, hq, hsq, hbase, hW, hemb, hcurve⟩

end PhilipponAlterationProjection


theorem solution
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (r : ℕ) (G : Scheme.{u}) (p : G ⟶ X)
      (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)),
      0 < r ∧ IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
      topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞) ∧
      IsProper p ∧ Surjective p ∧ IsProper q ∧ Surjective q ∧
      p ≫ π = q ≫ ProjSpace.π K r ∧
      (∃ W : G.Opens, IsAffineOpen W ∧ Nonempty W ∧ Dense (W : Set G) ∧
        Smooth (W.ι ≫ q) ∧ (∀ w : W, IsIso (p.stalkMap w.val))) ∧
      (∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π) ∧
      ∃ η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K),
        IsGenericPoint η Set.univ ∧ IsIntegral (q.fiber η) ∧
        (∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z)) ∧
        IsProper (q.fiberToSpecResidueField η) ∧
        topologicalKrullDim (q.fiber η) = 1 ∧
        ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z) := by
  exact PhilipponAlterationProjection.exists_normal_projective_generic_curve_model K π n i hi hnormalX hdim
