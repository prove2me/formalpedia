-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_fibration_with_smooth_integral_generic_fiber
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T15:07:55.594744+00:00
-- url     : https://prove2.me/submissions/00524e96-46ec-4e07-ad98-bbab8d101dbe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_exists_finite_extension_integral_smooth_projective_cover_of_integral_proper_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_model_of_finite_genericResidueField_extension
import Theorems.Thm_AlgebraicGeometry_exists_principal_localization_hom_of_fractionField
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_compactified_geometricallyIntegral_smooth_proper_curve_family
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_pullback_snd
import Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily

universe u
noncomputable section
set_option linter.style.haveILetI false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponGenericDominance

lemma genericPoint_eq_of_dominant
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] : q (genericPoint X) = genericPoint S := by
  have h := (genericPoint_spec X).image q.continuous
  have hg : IsGenericPoint (q (genericPoint X)) (Set.univ : Set S) := by
    simpa only [Set.image_univ, q.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec S)

lemma genericFiber_inclusion
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] (η : S) (hη : IsGenericPoint η Set.univ) :
    IsDominant (q.fiberι η) := by
  have hηeq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (q.fiberι (genericPoint S)) := by
    refine ⟨(q.fiberHomeo (genericPoint S)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant q⟩, ?_⟩
    exact q.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (q.fiberι (genericPoint S)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma of_recovered_generic_cover
    {C F Y X : Scheme.{u}} (e : C ⟶ Y) (f : Y ⟶ X) (a : C ⟶ F) (i : F ⟶ X)
    [Surjective a] [IsDominant i] (h : e ≫ f = a ≫ i) : IsDominant f := by
  haveI : IsDominant (e ≫ f) := by rw [h]; infer_instance
  exact IsDominant.of_comp e f

end PhilipponGenericDominance


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFieldModelProperties

lemma fpqc_fieldMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := by
    constructor
    intro x
    exact ⟨(⊥ : PrimeSpectrum K), Subsingleton.elim _ _⟩
  haveI : Flat b := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

lemma smooth_of_isPullback_field
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K))
    (g : X' ⟶ X)
    (h : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hs : Smooth f') : Smooth f := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K) hs

end PhilipponFieldModelProperties


set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory

namespace PhilipponFieldModelIntegral

lemma isReduced_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced Y := by
  have hstalk (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj y
    algebraize [(f.stalkMap x).hom]
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    have hf : RingHom.FaithfullyFlat (f.stalkMap x).hom := by
      change Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      infer_instance
    exact isReduced_of_injective (f.stalkMap x).hom hf.injective
  letI := hstalk
  exact isReduced_of_isReduced_stalk Y

lemma isIntegral_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsIntegral X] : IsIntegral Y := by
  letI : AlgebraicGeometry.IsReduced Y := isReduced_of_flat_surjective f
  letI : IrreducibleSpace Y := (inferInstance : Surjective f).surj.irreducibleSpace f.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

lemma geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f := by
  constructor
  intro K _ y Z fst snd hpb
  letI : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral (f := f) y fst snd hpb
  infer_instance

end PhilipponFieldModelIntegral



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponGenericDimensionFormula

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


end PhilipponGenericDimensionFormula


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section

namespace PhilipponGenericDimensionFormula

lemma isDominant_genericFiberι
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsDominant (f.fiberι (genericPoint Y)) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)) := by
    refine ⟨(f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, PhilipponGenericDominance.genericPoint_eq_of_dominant f⟩, ?_⟩
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
  letI : IsIntegral C := AlgebraicGeometry.isIntegral_genericFiber_of_isDominant f
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
  have hX := dimension_eq_trdeg_of_genericPoint (f ≫ c) z (PhilipponGenericDominance.genericPoint_eq_of_dominant t)
  have hY := dimension_eq_trdeg_of_genericPoint c η rfl
  have hC := dimension_eq_trdeg_of_genericPoint (K := F) s u rfl
  rw [hX, hY, hC]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K F) : WithBot ℕ∞) +
      (Cardinal.toENat (Algebra.trdeg F E) : WithBot ℕ∞)
  rw [he, ← trdeg_add_eq K F (A := E)]
  simp only [map_add, WithBot.coe_add]

end PhilipponGenericDimensionFormula



set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationDimensionControl

lemma finite_of_dimension_le_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hd : topologicalKrullDim X ≤ 0) : IsFinite π := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hd
  letI : Subsingleton X := Set.subsingleton_univ_iff.mp
    ((isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology X)).subsingleton_of_isPreirreducible
      PreirreducibleSpace.isPreirreducible_univ)
  exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := π)).mpr inferInstance

lemma dimension_nonneg (X : Scheme.{u}) [IsIntegral X] :
    0 ≤ topologicalKrullDim X := by
  change 0 ≤ Order.krullDim (IrreducibleCloseds X)
  letI : Nonempty (IrreducibleCloseds X) := ⟨{
    carrier := Set.univ
    isIrreducible' := IrreducibleSpace.isIrreducible_univ X
    isClosed' := isClosed_univ }⟩
  exact Order.krullDim_nonneg

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

lemma eq_zero_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : (r : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 0 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 0 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [add_zero,
        WithBot.coe_add, WithBot.coe_natCast] using h)
    have hd : d = 0 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

/-- The controlled generic curve forces the covering model to preserve
dimension. Its map to the original variety has zero-dimensional generic fibre. -/
theorem dimension_eq_and_genericFiber_dimensions
    (K : Type u) [Field K] {G X N : Scheme.{u}}
    [IsIntegral G] [IsIntegral X] [IsIntegral N]
    (πX : X ⟶ Spec (.of K)) [LocallyOfFiniteType πX]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (a : G ⟶ X) [LocallyOfFiniteType a] [IsDominant a]
    (f : G ⟶ N) [LocallyOfFiniteType f] [IsDominant f]
    (r : ℕ) (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞))
    (hdN : topologicalKrullDim N = (r : WithBot ℕ∞))
    (hdF : topologicalKrullDim (f.fiber (genericPoint N)) ≤ 1) :
    topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim (f.fiber (genericPoint N)) = 1 ∧
      topologicalKrullDim (a.fiber (genericPoint X)) = 0 := by
  have ha := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πX a
  have hf := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πN f
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (a ≫ πX)
  haveI : IsIntegral (a.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant a
  have hza := dimension_nonneg (a.fiber (genericPoint X))
  have hlow : topologicalKrullDim X ≤ topologicalKrullDim G := by
    calc
      topologicalKrullDim X = topologicalKrullDim X + 0 := (add_zero _).symm
      _ ≤ topologicalKrullDim X + topologicalKrullDim (a.fiber (genericPoint X)) :=
        add_le_add (le_refl _) hza
      _ = topologicalKrullDim G := ha.symm
  have hhigh : topologicalKrullDim G ≤ topologicalKrullDim X := by
    calc
      topologicalKrullDim G = (r : WithBot ℕ∞) +
          topologicalKrullDim (f.fiber (genericPoint N)) := hf.trans (by rw [hdN])
      _ ≤ (r : WithBot ℕ∞) + 1 := add_le_add (le_refl _) hdF
      _ = topologicalKrullDim X := by rw [hdX]; simp
  have heq := le_antisymm hhigh hlow
  refine ⟨heq, eq_one_of_nat_add_eq r _ ?_, eq_zero_of_nat_add_eq (r + 1) _ ?_⟩
  · simpa only [heq, hdX, hdN] using hf
  · simpa only [heq, hdX] using ha

end PhilipponAlterationDimensionControl



set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponGenericFieldPointIso

/-- A field-valued preimmersion uses exactly the residue field of its image,
via the canonical field map obtained from the actual local stalk map. -/
lemma isIso_residue_factor_of_isPreimmersion
    (E : Type u) [Field E] {U : Scheme.{u}}
    (b : Spec (.of E) ⟶ U) [IsPreimmersion b] :
    IsIso (Spec.map (U.descResidueField (Scheme.stalkClosedPointTo b))) := by
  let η := b (IsLocalRing.closedPoint E)
  let γ : U.residueField η ⟶ CommRingCat.of E :=
    U.descResidueField (Scheme.stalkClosedPointTo b)
  have hγ : Spec.map γ ≫ U.fromSpecResidueField η = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E U b
  letI : IsPreimmersion (Spec.map γ ≫ U.fromSpecResidueField η) := by rw [hγ]; infer_instance
  letI : IsPreimmersion (Spec.map γ) :=
    IsPreimmersion.of_comp (Spec.map γ) (U.fromSpecResidueField η)
  letI : Algebra (U.residueField η) E := γ.hom.toAlgebra
  have hf := PhilipponFieldModelProperties.fpqc_fieldMap (U.residueField η) E
  letI : Surjective (Spec.map γ) := hf.1.1
  letI : Flat (Spec.map γ) := hf.1.2
  letI : QuasiCompact (Spec.map γ) := hf.2
  change IsIso (Spec.map γ)
  exact Flat.isIso_of_surjective_of_mono (Spec.map γ)

/-- Fraction-field points of an affine chart are preimmersions, including
after their given open embedding into a larger integral base. -/
lemma isPreimmersion_of_fractionField_chart
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] [IsFractionRing B E]
    {N U : Scheme.{u}} (t : Spec (.of B) ⟶ N) [IsOpenImmersion t]
    (u : U ⟶ N) [IsOpenImmersion u] (b : Spec (.of E) ⟶ U)
    (hb : b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t) :
    IsPreimmersion b := by
  letI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap B E))) :=
    IsPreimmersion.of_isLocalization (R := B) (S := E) (nonZeroDivisors B)
  letI : IsPreimmersion (b ≫ u) := by rw [hb]; infer_instance
  exact IsPreimmersion.of_comp b u

/-- The actual prescribed generic source has the same geometric integrality
as the canonical fibre when its field point is a preimmersion. -/
lemma geometricallyIntegral_fiber_of_isPullback
    (E : Type u) [Field E] {C Y U : Scheme.{u}}
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsPreimmersion b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) [GeometricallyIntegral p₀]
    (h : IsPullback e p₀ p b) :
    GeometricallyIntegral (p.fiberToSpecResidueField (b (IsLocalRing.closedPoint E))) := by
  let η := b (IsLocalRing.closedPoint E)
  let γ : U.residueField η ⟶ CommRingCat.of E :=
    U.descResidueField (Scheme.stalkClosedPointTo b)
  have hγ : Spec.map γ ≫ U.fromSpecResidueField η = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E U b
  letI : IsIso (Spec.map γ) := isIso_residue_factor_of_isPreimmersion E b
  let hp := IsPullback.of_hasPullback p (U.fromSpecResidueField η)
  have hw : e ≫ p = (p₀ ≫ Spec.map γ) ≫ U.fromSpecResidueField η := by
    rw [Category.assoc, hγ]
    exact h.w
  let a := hp.lift e (p₀ ≫ Spec.map γ) hw
  have hr : IsPullback a p₀ (p.fiberToSpecResidueField η) (Spec.map γ) := by
    refine IsPullback.of_right ?_ (hp.lift_snd _ _ _) hp
    rw [hp.lift_fst, hγ]
    exact h
  letI : IsIso a := hr.isIso_fst_of_isIso
  have hc : GeometricallyIntegral (p₀ ≫ Spec.map γ) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral p₀ (Spec.map γ)).mpr inferInstance
  rw [← hr.w] at hc
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral a
    (p.fiberToSpecResidueField η)).mp hc

lemma geometricallyIntegral_genericFiber_of_isPullback
    (E : Type u) [Field E] {C Y U : Scheme.{u}} [IsIntegral U]
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsPreimmersion b] [IsDominant b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) [GeometricallyIntegral p₀]
    (h : IsPullback e p₀ p b) :
    GeometricallyIntegral (p.fiberToSpecResidueField (genericPoint U)) := by
  have hη : b (IsLocalRing.closedPoint E) = genericPoint U := by
    have hz : IsLocalRing.closedPoint E = genericPoint (Spec (.of E)) := Subsingleton.elim _ _
    rw [hz]
    exact PhilipponGenericDominance.genericPoint_eq_of_dominant b
  exact (congrArg (fun x : U => GeometricallyIntegral (p.fiberToSpecResidueField x)) hη).mp
    (geometricallyIntegral_fiber_of_isPullback E p b e p₀ h)

/-- A surjective open source subfamily of a geometrically integral family
has geometrically integral fibres. No finiteness hypothesis is needed. -/
lemma geometricallyIntegral_of_surjective_open_subfamily
    {W Y S : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (p : Y ⟶ S) [GeometricallyIntegral p] [Surjective (i ≫ p)] :
    GeometricallyIntegral (i ≫ p) := by
  constructor
  intro K _ s J a b hJ
  let hp := IsPullback.of_hasPullback p s
  let r : J ⟶ pullback p s := hp.lift (a ≫ i) b hJ.w
  have hr : IsPullback r a (pullback.fst p s) i := by
    refine IsPullback.of_right ?_ (hp.lift_fst _ _ _) hp.flip
    rw [hp.lift_snd]
    exact hJ.flip
  haveI : IsOpenImmersion r := MorphismProperty.of_isPullback hr.flip inferInstance
  haveI : IsIntegral (pullback p s) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) s _ _ hp
  haveI : Surjective b := MorphismProperty.of_isPullback hJ inferInstance
  haveI : Nonempty J := by
    obtain ⟨j, _hj⟩ := (inferInstance : Surjective b).surj (IsLocalRing.closedPoint K)
    exact ⟨j⟩
  exact isIntegral_of_isOpenImmersion r

end PhilipponGenericFieldPointIso

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGenericOpenFactor

/-- A dominant field point factors through every dense base open, retaining
the actual map and its dominance. -/
lemma exists_factor
    (E : Type u) [Field E] {U : Scheme.{u}} [IsIntegral U]
    (b : Spec (.of E) ⟶ U) [IsDominant b] (V : U.Opens) (hdV : Dense (V : Set U)) :
    ∃ b' : Spec (.of E) ⟶ (V : Scheme.{u}), b' ≫ V.ι = b ∧ IsDominant b' := by
  have hηV : genericPoint U ∈ V := by
    apply ((genericPoint_spec U).mem_open_set_iff V.isOpen).mpr
    simpa only [Set.univ_inter] using hdV.nonempty
  have hrange : Set.range b ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    have hz : z = genericPoint (Spec (.of E)) := Subsingleton.elim _ _
    rw [hz, PhilipponGenericDominance.genericPoint_eq_of_dominant b]
    exact hηV
  let b' := IsOpenImmersion.lift V.ι b hrange
  have hb' : b' ≫ V.ι = b := IsOpenImmersion.lift_fac V.ι b hrange
  haveI : IsDominant (b' ≫ V.ι) := by rw [hb']; infer_instance
  exact ⟨b', hb', IsDominant.of_comp_of_isOpenImmersion b' V.ι⟩

/-- The retained fraction-field chart makes the prescribed field point
factor through the dense absolute smooth base open. -/
lemma exists_factor_of_fractionField_chart
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {U N : Scheme.{u}} [IsIntegral U]
    (t : Spec (.of B) ⟶ N) [IsDominant t]
    (u : U ⟶ N) [IsOpenImmersion u]
    (b : Spec (.of E) ⟶ U)
    (hb : b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t)
    (V : U.Opens) (hdV : Dense (V : Set U)) :
    ∃ b' : Spec (.of E) ⟶ (V : Scheme.{u}), b' ≫ V.ι = b ∧ IsDominant b' := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap B E))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap B E)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective B E)]
    exact bot_le
  haveI : IsDominant (b ≫ u) := by rw [hb]; infer_instance
  haveI : IsDominant b := IsDominant.of_comp_of_isOpenImmersion b u
  exact exists_factor E b V hdV

/-- Restrict the family along a base open while retaining the same actual
generic source and its original map to the family. -/
lemma exists_cartesian_comparison_on_open
    {C Y U T : Scheme.{u}} (p : Y ⟶ U)
    (e : C ⟶ Y) (p₀ : C ⟶ T) (b : T ⟶ U)
    (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) (b' : T ⟶ (V : Scheme.{u})) (hb : b' ≫ V.ι = b) :
    ∃ e' : C ⟶ (p ⁻¹ᵁ V : Scheme.{u}),
      e' ≫ (p ⁻¹ᵁ V).ι = e ∧ IsPullback e' p₀ (p ∣_ V) b' := by
  let hr := (isPullback_morphismRestrict p V).flip
  have hcomm : e ≫ p = (p₀ ≫ b') ≫ V.ι := by
    rw [Category.assoc, hb, hp₀.w]
  let e' := hr.lift e (p₀ ≫ b') hcomm
  have he : e' ≫ (p ⁻¹ᵁ V).ι = e := hr.lift_fst _ _ _
  have hep : e' ≫ (p ∣_ V) = p₀ ≫ b' := hr.lift_snd _ _ _
  have hwhole : IsPullback (e' ≫ (p ⁻¹ᵁ V).ι) p₀ p (b' ≫ V.ι) := by
    rw [he, hb]
    exact hp₀
  exact ⟨e', he, hwhole.of_right hep hr⟩

/-- Base changing an open source subfamily gives an open subscheme of the
original actual generic source, hence cannot increase its dimension. -/
lemma dimension_le_of_open_subfamily_baseChange
    {W Y C U T : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (p : Y ⟶ U) (e : C ⟶ Y) (p₀ : C ⟶ T) (b : T ⟶ U)
    (hp₀ : IsPullback e p₀ p b) :
    topologicalKrullDim (pullback (i ≫ p) b : Scheme.{u}) ≤ topologicalKrullDim C := by
  have hr : IsPullback (pullback.fst i e) (pullback.snd i e ≫ p₀) (i ≫ p) b :=
    ((IsPullback.of_hasPullback i e).flip.paste_horiz hp₀.flip).flip
  let α := hr.isoPullback.inv ≫ pullback.snd i e
  haveI : IsOpenImmersion α := inferInstance
  exact α.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

end PhilipponGenericOpenFactor





set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGeometricGenericTransport

lemma geometricallyIntegral_fiber_of_surjective_open_subfamily
    {W Y U : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (p : Y ⟶ U) [Surjective (i ≫ p)] (x : U)
    [hgeo : GeometricallyIntegral (p.fiberToSpecResidueField x)] :
    GeometricallyIntegral ((i ≫ p).fiberToSpecResidueField x) := by
  let s := U.fromSpecResidueField x
  let hp := IsPullback.of_hasPullback p s
  let hw := IsPullback.of_hasPullback (i ≫ p) s
  let j := hp.lift (pullback.fst (i ≫ p) s ≫ i) (pullback.snd (i ≫ p) s)
    (by simpa only [Category.assoc] using hw.w)
  have hj : IsPullback j (pullback.fst (i ≫ p) s) (pullback.fst p s) i := by
    refine IsPullback.of_right ?_ (hp.lift_fst _ _ _) hp.flip
    rw [hp.lift_snd]
    exact hw.flip
  haveI : IsOpenImmersion j := MorphismProperty.of_isPullback hj.flip inferInstance
  have hjp : j ≫ p.fiberToSpecResidueField x = (i ≫ p).fiberToSpecResidueField x :=
    hp.lift_snd _ _ _
  have hsur : Surjective ((i ≫ p).fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd (i ≫ p) s inferInstance
  letI hsurJ : Surjective (j ≫ p.fiberToSpecResidueField x) :=
    (congrArg (fun a => Surjective a) hjp).mpr hsur
  letI hgeoY : GeometricallyIntegral (p.fiberToSpecResidueField x) := hgeo
  have hg := @PhilipponGenericFieldPointIso.geometricallyIntegral_of_surjective_open_subfamily
    ((i ≫ p).fiber x) (p.fiber x) (Spec (U.residueField x)) j
    (inferInstance : IsOpenImmersion j) (p.fiberToSpecResidueField x) hgeo hsurJ
  exact (congrArg (fun m : ((i ≫ p).fiber x) ⟶ Spec (U.residueField x) =>
    GeometricallyIntegral m) hjp).mp hg

lemma geometricallyIntegral_fiber_of_cartesian_preimmersion
    {W G U N : Scheme.{u}} (t : W ⟶ G) (p : W ⟶ U)
    (f : G ⟶ N) (u : U ⟶ N) [IsPreimmersion u]
    (h : IsPullback t p f u) (x : U)
    [GeometricallyIntegral (p.fiberToSpecResidueField x)] :
    GeometricallyIntegral (f.fiberToSpecResidueField (u x)) := by
  let γ := Spec.map (u.residueFieldMap x)
  letI : IsIso (u.residueFieldMap x) :=
    PhilipponGenericDimensionFormula.isIso_residueFieldMap_of_isPreimmersion u x
  letI : IsIso γ := inferInstance
  let hF := isPullback_fiberToSpecResidueField_of_isPullback h x
  let a := pullback.map p (U.fromSpecResidueField x) f (N.fromSpecResidueField (u x))
    t γ u h.w.symm (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField u x).symm
  have ha : IsIso a := hF.isIso_fst_of_isIso
  letI := ha
  have hg : GeometricallyIntegral (p.fiberToSpecResidueField x ≫ γ) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral _ γ).mpr inferInstance
  have he : a ≫ f.fiberToSpecResidueField (u x) = p.fiberToSpecResidueField x ≫ γ := hF.w
  have hg' : GeometricallyIntegral (a ≫ f.fiberToSpecResidueField (u x)) :=
    (congrArg (fun m : p.fiber x ⟶ Spec (N.residueField (u x)) => GeometricallyIntegral m) he).mpr hg
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral a _).mp hg'

/-- A retained geometrically integral actual generic source supplies
geometric integrality of the completed canonical generic curve. -/
theorem geometricallyIntegral_genericFiber_of_cartesian_open_subfamily
    (E : Type u) [Field E] {Y C U W G N : Scheme.{u}} [IsIntegral U] [IsIntegral N]
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsPreimmersion b] [IsDominant b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) [GeometricallyIntegral p₀]
    (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) [IsIntegral (V : Scheme.{u})] (hdV : Dense (V : Set U))
    (i : W ⟶ (p ⁻¹ᵁ V : Scheme.{u})) [IsOpenImmersion i]
    [Surjective (i ≫ (p ∣_ V))]
    (t : W ⟶ G) (f : G ⟶ N) (u : (V : Scheme.{u}) ⟶ N)
    [IsOpenImmersion u] [IsDominant u]
    (hG : IsPullback t (i ≫ (p ∣_ V)) f u) (η : N) (hη : IsGenericPoint η Set.univ) :
    GeometricallyIntegral (f.fiberToSpecResidueField η) := by
  obtain ⟨b', hb', hdb'⟩ := PhilipponGenericOpenFactor.exists_factor E b V hdV
  haveI : IsDominant b' := hdb'
  haveI : IsPreimmersion (b' ≫ V.ι) := by rw [hb']; infer_instance
  haveI : IsPreimmersion b' := IsPreimmersion.of_comp b' V.ι
  obtain ⟨e', _he', hp'⟩ :=
    PhilipponGenericOpenFactor.exists_cartesian_comparison_on_open p e p₀ b hp₀ V b' hb'
  haveI : GeometricallyIntegral ((p ∣_ V).fiberToSpecResidueField (genericPoint (V : Scheme.{u}))) :=
    PhilipponGenericFieldPointIso.geometricallyIntegral_genericFiber_of_isPullback
      E (p ∣_ V) b' e' p₀ hp'
  haveI : GeometricallyIntegral ((i ≫ (p ∣_ V)).fiberToSpecResidueField (genericPoint (V : Scheme.{u}))) :=
    geometricallyIntegral_fiber_of_surjective_open_subfamily i (p ∣_ V) _
  have hg := geometricallyIntegral_fiber_of_cartesian_preimmersion t (i ≫ (p ∣_ V)) f u hG
    (genericPoint (V : Scheme.{u}))
  have he : u (genericPoint (V : Scheme.{u})) = η :=
    (PhilipponGenericDominance.genericPoint_eq_of_dominant u).trans
      (hη.eq (genericPoint_spec N)).symm
  exact (congrArg (fun x : N => GeometricallyIntegral (f.fiberToSpecResidueField x)) he).mp hg

end PhilipponGeometricGenericTransport


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponFractionFieldCoefficients

/-- A finitely generated prime subalgebra of a fraction field is defined on
one principal open of any given affine model. The factorization uses the
actual field, not an abstractly isomorphic field. -/
lemma factor_fg_prime_subalgebra
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (A : Subalgebra ℤ E) (hA : A.FG) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (φ : A →+* Localization.Away s),
          γ.toRingHom.comp φ = A.val.toRingHom := by
  classical
  obtain ⟨T, hT⟩ := hA
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors B) T
  have hs0 : (s : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  let γ : Localization.Away (s : B) →ₐ[B] E :=
    IsLocalization.Away.liftAlgHom (s : B)
      (f := Algebra.ofId B E)
      (isUnit_iff_ne_zero.mpr (by
        change algebraMap B E (s : B) ≠ 0
        simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0))
  have hγbase (b : B) : γ (algebraMap B (Localization.Away (s : B)) b) =
      algebraMap B E b := γ.commutes b
  have hM : Submonoid.powers (s : B) ≤ nonZeroDivisors B := by
    intro b hb
    obtain ⟨n, rfl⟩ := by simpa only [Algebra.smul_def] using hb
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs0)
  have hγ : Function.Injective γ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers (s : B)) γ.toRingHom).mpr
    intro x y
    change algebraMap B (Localization.Away (s : B)) x = _ ↔
      γ (algebraMap B (Localization.Away (s : B)) x) =
        γ (algebraMap B (Localization.Away (s : B)) y)
    rw [hγbase, hγbase]
    exact (IsLocalization.injective _ hM).eq_iff.trans
      (IsFractionRing.injective B E).eq_iff.symm
  let γz : Localization.Away (s : B) →ₐ[ℤ] E := { __ := γ.toRingHom, commutes' := by intro r; simp }
  have hTA : A ≤ γz.range := by
    rw [← hT]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨b, hb⟩ := hs x hx
    have hb' : algebraMap B E b = algebraMap B E s * x := by simpa only [Algebra.smul_def] using hb
    refine ⟨algebraMap B (Localization.Away (s : B)) b *
      IsLocalization.Away.invSelf (s : B), ?_⟩
    change γ (_ * _) = x
    apply mul_left_cancel₀ (show algebraMap B E s ≠ 0 by
      simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0)
    rw [map_mul, hγbase, hb']
    calc
      algebraMap B E s * (algebraMap B E s * x * γ (IsLocalization.Away.invSelf (s : B))) =
          (algebraMap B E s * x) * γ (algebraMap B (Localization.Away (s : B)) s *
            IsLocalization.Away.invSelf (s : B)) := by rw [map_mul, hγbase]; ring
      _ = algebraMap B E s * x := by
        rw [IsLocalization.Away.mul_invSelf, map_one]
        simp
  let e := AlgEquiv.ofInjective γz hγ
  let φ : A →+* Localization.Away (s : B) :=
    (e.symm.toAlgHom.comp (Subalgebra.inclusion hTA)).toRingHom
  refine ⟨s, hs0, γ, hγ, φ, ?_⟩
  ext x
  change γz (e.symm (Subalgebra.inclusion hTA x)) = (x : E)
  have he := congrArg (fun z : γz.range => (z : E))
    (e.apply_symm_apply (Subalgebra.inclusion hTA x))
  exact (AlgEquiv.ofInjective_apply γz hγ _).symm.trans he

end PhilipponFractionFieldCoefficients

namespace PhilipponFractionFieldCoefficients

lemma fractionRing_of_injective_tower
    {B A E : Type u} [CommRing B] [CommRing A] [Field E]
    [Algebra B A] [Algebra B E] [Algebra A E] [IsScalarTower B A E]
    [IsFractionRing B E] (h : Function.Injective (algebraMap A E)) :
    IsFractionRing A E := by
  haveI : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr h
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _hb, hx⟩ := IsFractionRing.div_surjective B x
  refine ⟨algebraMap B A a, algebraMap B A b, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply B A E] using hx.symm

end PhilipponFractionFieldCoefficients

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponFractionFieldLocalization

/-- A prescribed nonzero principal localization embeds into the same actual
fraction field, with its specified base-algebra structure. -/
lemma exists_embedding
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E] (s : B) (hs : s ≠ 0) :
    ∃ γ : Localization.Away s →ₐ[B] E, Function.Injective γ := by
  let γ : Localization.Away s →ₐ[B] E := IsLocalization.Away.liftAlgHom s
    (f := Algebra.ofId B E) (isUnit_iff_ne_zero.mpr (by
      change algebraMap B E s ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective B E).ne hs))
  refine ⟨γ, ?_⟩
  have hM : Submonoid.powers s ≤ nonZeroDivisors B := by
    intro b hb
    obtain ⟨n, rfl⟩ := hb
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs)
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s) γ.toRingHom).mpr
  intro x y
  change algebraMap B (Localization.Away s) x = _ ↔
    γ (algebraMap B (Localization.Away s) x) = γ (algebraMap B (Localization.Away s) y)
  rw [γ.commutes, γ.commutes]
  exact (IsLocalization.injective _ hM).eq_iff.trans
    (IsFractionRing.injective B E).eq_iff.symm

end PhilipponFractionFieldLocalization


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericMorphismSpread

/-- Canonical comparison of two pullbacks with compatible base maps. -/
def changeBase {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    pullback f a ⟶ pullback f b :=
  pullback.lift (pullback.fst f a) (pullback.snd f a ≫ c)
    (by rw [Category.assoc, hc]; exact pullback.condition)

@[reassoc (attr := simp)] lemma changeBase_fst {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.fst f b = pullback.fst f a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma changeBase_snd {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.snd f b = pullback.snd f a ≫ c :=
  pullback.lift_snd _ _ _

end PhilipponGenericMorphismSpread

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponProperCoverSpread

lemma changeBase_isPullback {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    IsPullback (changeBase f a b c hc) (pullback.snd f a) (pullback.snd f b) c := by
  refine IsPullback.of_right ?_ (changeBase_snd _ _ _ _ _) (IsPullback.of_hasPullback f b)
  rw [changeBase_fst, hc]
  exact IsPullback.of_hasPullback f a

end PhilipponProperCoverSpread


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponSmoothFamilyOpen

lemma smooth_of_comp_openImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] [LocallyOfFinitePresentation f] [Smooth (f ≫ j)] :
    Smooth f := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  have hx : x ∈ (f ≫ j).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (j.stalkMap (f x)) (f.stalkMap x)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact hx

/-- Smoothness of a flatly covered fibre of a proper finitely presented
morphism extends over a neighbourhood of that fibre's base point. -/
lemma exists_open_of_smooth_pullback
    {Y S C T : Scheme.{u}} (f : Y ⟶ S) (p : C ⟶ T)
    (b : T ⟶ S) (g : C ⟶ Y) (hpb : IsPullback g p f b)
    [IsProper f] [LocallyOfFinitePresentation f] [Smooth p] [Flat b]
    (η : S) (hη : η ∈ Set.range b) :
    ∃ U : S.Opens, η ∈ U ∧ Smooth (f ∣_ U) := by
  let bad : Set Y := (f.smoothLocus : Set Y)ᶜ
  have hbad : IsClosed bad := f.smoothLocus.isOpen.isClosed_compl
  let U : S.Opens := ⟨(f '' bad)ᶜ, (f.isClosedMap bad hbad).isOpen_compl⟩
  have hηU : η ∈ U := by
    rintro ⟨y, hy, hyη⟩
    obtain ⟨t, ht⟩ := hη
    obtain ⟨z, hzy, _⟩ := Scheme.Pullback.exists_preimage_pullback y t (hyη.trans ht.symm)
    let c := hpb.isoPullback.inv z
    have hc : g c = y := by
      change (hpb.isoPullback.inv ≫ g) z = y
      rw [hpb.isoPullback_inv_fst]
      exact hzy
    have hs := Scheme.Hom.smoothLocus_le_preimage_of_isPullback hpb
    have hcS : c ∈ p.smoothLocus := by rw [p.smoothLocus_eq_top]; trivial
    have hyS : y ∈ f.smoothLocus := by simpa only [Scheme.Hom.mem_preimage, hc] using hs hcS
    exact hy hyS
  have hle : f ⁻¹ᵁ U ≤ f.smoothLocus := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hc : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact hle x.property
  have hcomp : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    (isPullback_morphismRestrict f U).w
  haveI : Smooth ((f ∣_ U) ≫ U.ι) := by rw [hcomp]; exact hc
  exact ⟨U, hηU, smooth_of_comp_openImmersion (f ∣_ U) U.ι⟩

end PhilipponSmoothFamilyOpen


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponMorphismFamilySpread

/-- A generic morphism from a smooth proper source spreads over a dense
base open. Its image need not cover every component of the scalar target. -/
theorem exists_smooth_proper_source_on_dense_open
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of B)),
      IsOpenImmersion j ∧ DenseRange j ∧
      ∃ (Y₁ Y₂ : Scheme.{u}) (p₁ : Y₁ ⟶ S) (p₂ : Y₂ ⟶ S)
        (t₁ : Y₁ ⟶ X₁) (t₂ : Y₂ ⟶ X₂),
        IsPullback t₁ p₁ f₁ j ∧ IsPullback t₂ p₂ f₂ j ∧
        ∃ (h : Y₁ ⟶ Y₂), h ≫ p₂ = p₁ ∧ Smooth p₁ ∧ IsProper p₁ ∧
          ∃ (b : Spec (.of E) ⟶ S)
            (e₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₁)
            (e₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₂),
            b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B E)) ∧
            IsPullback e₁ (pullback.snd f₁ _) p₁ b ∧
            IsPullback e₂ (pullback.snd f₂ _) p₂ b ∧
            e₁ ≫ t₁ = pullback.fst f₁ _ ∧ e₂ ≫ t₂ = pullback.fst f₂ _ ∧
            e₁ ≫ h = g ≫ e₂ := by
  obtain ⟨s, hs, γ, hγ, g₀, hg₀, hrec⟩ :=
    AlgebraicGeometry.exists_principal_localization_hom_of_fractionField B E f₁ f₂ g hg
  let A := Localization.Away s
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B A E := IsScalarTower.of_algebraMap_eq fun x => (γ.commutes x).symm
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγ
  haveI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let d := Spec.map (CommRingCat.ofHom γ.toRingHom)
  have hd : d ≫ bA = bE := by
    dsimp only [d, bA, bE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  let q₁ := changeBase f₁ bE bA d hd
  let q₂ := changeBase f₂ bE bA d hd
  have hp₁ := PhilipponProperCoverSpread.changeBase_isPullback f₁ bE bA d hd
  have hp₂ := PhilipponProperCoverSpread.changeBase_isPullback f₂ bE bA d hd
  have hrec' : q₁ ≫ g₀ = g ≫ q₂ :=
    hrec q₁ q₂ (changeBase_fst _ _ _ _ _) (changeBase_snd _ _ _ _ _)
      (changeBase_fst _ _ _ _ _) (changeBase_snd _ _ _ _ _)
  letI : Module.Flat A E := IsLocalization.flat E (nonZeroDivisors A)
  letI : Flat d := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let e : Spec (.of E) := default
  obtain ⟨U, hU, hsm⟩ := PhilipponSmoothFamilyOpen.exists_open_of_smooth_pullback
    (pullback.snd f₁ bA) (pullback.snd f₁ bE) d q₁ hp₁ (d e) ⟨e, rfl⟩
  have hrange : Set.range d ⊆ U := by
    rintro x ⟨e', rfl⟩
    change d e' ∈ U
    rw [Subsingleton.elim e' e]
    exact hU
  let b := IsOpenImmersion.lift U.ι d (by simpa only [Scheme.Opens.range_ι] using hrange)
  have hb : b ≫ U.ι = d := IsOpenImmersion.lift_fac _ _ _
  let j := U.ι ≫ bA
  haveI : IsOpenImmersion bA := IsOpenImmersion.of_isLocalization s
  haveI : IsOpenImmersion j := by dsimp only [j]; infer_instance
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨d e, hU⟩⟩
  have hdense : DenseRange j := j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
  let p₁ := pullback.snd f₁ bA
  let p₂ := pullback.snd f₂ bA
  let Y₁ := p₁ ⁻¹ᵁ U
  let Y₂ := p₂ ⁻¹ᵁ U
  let f₁U := p₁ ∣_ U
  let f₂U := p₂ ∣_ U
  let t₁ := Y₁.ι ≫ pullback.fst f₁ bA
  let t₂ := Y₂.ι ≫ pullback.fst f₂ bA
  let hu₁ := (isPullback_morphismRestrict p₁ U).flip
  let hu₂ := (isPullback_morphismRestrict p₂ U).flip
  have ht₁ : IsPullback t₁ f₁U f₁ j := hu₁.paste_horiz (IsPullback.of_hasPullback f₁ bA)
  have ht₂ : IsPullback t₂ f₂U f₂ j := hu₂.paste_horiz (IsPullback.of_hasPullback f₂ bA)
  have hPQ : p₁ ⁻¹ᵁ U = g₀ ⁻¹ᵁ (p₂ ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hg₀]
  let h := g₀.resLE (p₂ ⁻¹ᵁ U) (p₁ ⁻¹ᵁ U) hPQ.le
  have hι : h ≫ Y₂.ι = Y₁.ι ≫ g₀ := Scheme.Hom.resLE_comp_ι _ _
  have hover : h ≫ f₂U = f₁U := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, ← hu₂.w, ← Category.assoc, hι, Category.assoc, hg₀]
    exact hu₁.w
  have hw₁ : q₁ ≫ p₁ = (pullback.snd f₁ bE ≫ b) ≫ U.ι := by
    rw [Category.assoc, hb]; exact changeBase_snd _ _ _ _ _
  have hw₂ : q₂ ≫ p₂ = (pullback.snd f₂ bE ≫ b) ≫ U.ι := by
    rw [Category.assoc, hb]; exact changeBase_snd _ _ _ _ _
  let e₁ := hu₁.lift q₁ (pullback.snd f₁ bE ≫ b) hw₁
  let e₂ := hu₂.lift q₂ (pullback.snd f₂ bE ≫ b) hw₂
  have he₁ : IsPullback e₁ (pullback.snd f₁ bE) f₁U b := by
    refine IsPullback.of_right ?_ (hu₁.lift_snd _ _ _) hu₁
    rw [hu₁.lift_fst, hb]; exact hp₁
  have he₂ : IsPullback e₂ (pullback.snd f₂ bE) f₂U b := by
    refine IsPullback.of_right ?_ (hu₂.lift_snd _ _ _) hu₂
    rw [hu₂.lift_fst, hb]; exact hp₂
  have hbj : b ≫ j = bE := by dsimp only [j]; rw [← Category.assoc, hb, hd]
  have het₁ : e₁ ≫ t₁ = pullback.fst f₁ bE := by
    dsimp only [t₁]
    rw [← Category.assoc, hu₁.lift_fst]
    exact changeBase_fst _ _ _ _ _
  have het₂ : e₂ ≫ t₂ = pullback.fst f₂ bE := by
    dsimp only [t₂]
    rw [← Category.assoc, hu₂.lift_fst]
    exact changeBase_fst _ _ _ _ _
  have hrecover : e₁ ≫ h = g ≫ e₂ := by
    apply (cancel_mono Y₂.ι).mp
    rw [Category.assoc, hι, ← Category.assoc, hu₁.lift_fst,
      hrec', Category.assoc, hu₂.lift_fst]
  exact ⟨U, j, inferInstance, hdense, Y₁, Y₂, f₁U, f₂U, t₁, t₂, ht₁, ht₂,
    h, hover, hsm, inferInstance, b, e₁, e₂, hbj, he₁, he₂, het₁, het₂, hrecover⟩

end PhilipponMorphismFamilySpread


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveFamily

/-- A smooth projective scheme over the actual fraction field spreads to a
flat finitely presented projective scheme over a principal localization. -/
lemma exists_flat_projective_model
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (Y : Scheme.{u})
          (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (Localization.Away s))) (g : C ⟶ Y),
          IsClosedImmersion j ∧ Flat (j ≫ ProjSpace.π (Localization.Away s) n) ∧
          LocallyOfFinitePresentation (j ≫ ProjSpace.π (Localization.Away s) n) ∧
          IsPullback g (ι ≫ ProjSpace.π E n)
            (j ≫ ProjSpace.π (Localization.Away s) n)
            (Spec.map (CommRingCat.ofHom γ.toRingHom)) := by
  obtain ⟨A₀, hA₀, C₀, ι₀, g₀, hι₀, hflat₀, hfp₀, hpb₀, _⟩ :=
    ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
      n C ι inferInstance inferInstance inferInstance
  obtain ⟨s, hs, γ, hγ, φ, hφ⟩ :=
    PhilipponFractionFieldCoefficients.factor_fg_prime_subalgebra B E A₀ hA₀
  let A := Localization.Away s
  letI : Algebra A₀ A := φ.toAlgebra
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower A₀ A E := IsScalarTower.of_algebraMap_eq fun x =>
    DFunLike.congr_fun hφ x |>.symm
  letI : IsClosedImmersion ι₀ := hι₀
  letI : Flat (ι₀ ≫ ProjSpace.π A₀ n) := hflat₀
  letI : LocallyOfFinitePresentation (ι₀ ≫ ProjSpace.π A₀ n) := hfp₀
  obtain ⟨Y, j, hj, e, hpbe, _⟩ :=
    ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map ι₀ A
  have hbase : Spec.map (CommRingCat.ofHom γ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ E)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (γ.toRingHom.comp φ)) = _
    rw [hφ]
    rfl
  have hw : g₀ ≫ (ι₀ ≫ ProjSpace.π A₀ n) =
      ((ι ≫ ProjSpace.π E n) ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
    rw [Category.assoc, hbase]
    exact hpb₀.w
  let g := hpbe.lift g₀
    ((ι ≫ ProjSpace.π E n) ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) hw
  have hpg : IsPullback g (ι ≫ ProjSpace.π E n)
      (j ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom γ.toRingHom)) := by
    refine IsPullback.of_right ?_ (hpbe.lift_snd _ _ _) hpbe
    rw [hpbe.lift_fst, hbase]
    exact hpb₀
  have hflat : Flat (j ≫ ProjSpace.π A n) :=
    MorphismProperty.of_isPullback hpbe hflat₀
  have hfp : LocallyOfFinitePresentation (j ≫ ProjSpace.π A n) :=
    MorphismProperty.of_isPullback hpbe hfp₀
  exact ⟨s, hs, γ, hγ, Y, j, g, hj, hflat, hfp, hpg⟩

end PhilipponProjectiveFamily

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveMorphismFamilySpread

/-- A given smooth projective generic cover acquires a projective model and
spreads to a smooth proper covering family, retaining its original maps. -/
theorem exists_projective_morphism_family
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f] [LocallyOfFinitePresentation f]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)]
    (g : C ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f _ = ι ≫ ProjSpace.π E n) :
    ∃ a : B, a ≠ 0 ∧
      ∃ γ : Localization.Away a →ₐ[B] E, Function.Injective γ ∧
        ∃ (M : Scheme.{u})
          (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (Localization.Away a)))
          (gM : C ⟶ M), IsClosedImmersion iM ∧
          IsPullback gM (ι ≫ ProjSpace.π E n) (iM ≫ ProjSpace.π (Localization.Away a) n)
            (Spec.map (CommRingCat.ofHom γ.toRingHom)) ∧
          ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of (Localization.Away a))),
            IsOpenImmersion j ∧ DenseRange j ∧
            ∃ (Y Z : Scheme.{u}) (pY : Y ⟶ S) (pZ : Z ⟶ S) (tY : Y ⟶ M) (tZ : Z ⟶ X),
              IsPullback tY pY (iM ≫ ProjSpace.π (Localization.Away a) n) j ∧
              IsPullback tZ pZ f (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ∧
              Smooth pY ∧ IsProper pY ∧ IsProper pZ ∧
              ∃ h : Y ⟶ Z, h ≫ pZ = pY ∧
                ∃ (b : Spec (.of E) ⟶ S) (eC : C ⟶ Y)
                  (eX : pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Z),
                  b ≫ j = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
                  IsPullback eC (ι ≫ ProjSpace.π E n) pY b ∧
                  IsPullback eX (pullback.snd f _) pZ b ∧
                  eC ≫ tY = gM ∧ eX ≫ tZ = pullback.fst f _ ∧ eC ≫ h = g ≫ eX := by
  obtain ⟨a, ha, γ, hγ, M, iM, gM, hiM, _hflatM, hfpM, hpM⟩ :=
    PhilipponProjectiveFamily.exists_flat_projective_model B E C n ι
  let A := Localization.Away a
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B A E := IsScalarTower.of_algebraMap_eq fun x => (γ.commutes x).symm
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγ
  haveI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let dE := Spec.map (CommRingCat.ofHom γ.toRingHom)
  have hdE : dE ≫ bA = bE := by
    dsimp only [dE, bA, bE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  let fM := iM ≫ ProjSpace.π A n
  haveI : IsClosedImmersion iM := hiM
  haveI : IsProper fM := inferInstance
  haveI : LocallyOfFinitePresentation fM := hfpM
  let fA := pullback.snd f bA
  let q := changeBase f bE bA dE hdE
  have hpX := PhilipponProperCoverSpread.changeBase_isPullback f bE bA dE hdE
  let e₁ := hpM.isoPullback
  let e₂ := hpX.isoPullback
  let gA := e₁.inv ≫ g ≫ e₂.hom
  have hgA : gA ≫ pullback.snd fA dE = pullback.snd fM dE := by
    dsimp only [gA, e₂]
    rw [Category.assoc, Category.assoc, hpX.isoPullback_hom_snd, hg]
    exact hpM.isoPullback_inv_snd
  have hscomp : Smooth (e₁.hom ≫ pullback.snd fM dE) := by
    rw [hpM.isoPullback_hom_snd]
    infer_instance
  have hsmA : Smooth (pullback.snd fM dE) :=
    (MorphismProperty.cancel_left_of_respectsIso @Smooth e₁.hom _).mp hscomp
  have hrecA : hpM.isoPullback.hom ≫ gA = g ≫ hpX.isoPullback.hom := by
    dsimp only [gA, e₁, e₂]
    simp
  haveI : Smooth (pullback.snd fM dE) := hsmA
  obtain ⟨S, j, hj, hdj, Y, Z, pY, pZ, tY, tA, hpY, hpZ,
    h, hover, hsmY, hprY, b, cY, cZ, hb, heY, heZ, hcY, hcZ, hrec⟩ :=
    PhilipponMorphismFamilySpread.exists_smooth_proper_source_on_dense_open A E fM fA gA hgA
  let tZ := tA ≫ pullback.fst f bA
  have hptZ : IsPullback tZ pZ f (j ≫ bA) :=
    hpZ.paste_horiz (IsPullback.of_hasPullback f bA)
  have hprZ : IsProper pZ := MorphismProperty.of_isPullback hptZ inferInstance
  let eC := hpM.isoPullback.hom ≫ cY
  let eX := hpX.isoPullback.hom ≫ cZ
  have heCt : eC ≫ tY = gM := by
    dsimp only [eC]
    rw [Category.assoc, hcY, hpM.isoPullback_hom_fst]
  have heCp : eC ≫ pY = (ι ≫ ProjSpace.π E n) ≫ b := by
    dsimp only [eC]
    rw [Category.assoc, heY.w, ← Category.assoc, hpM.isoPullback_hom_snd]
  have heXp : eX ≫ pZ = pullback.snd f bE ≫ b := by
    dsimp only [eX]
    rw [Category.assoc, heZ.w, ← Category.assoc, hpX.isoPullback_hom_snd]
  have heXt : eX ≫ tA = q := by
    dsimp only [eX]
    rw [Category.assoc, hcZ, hpX.isoPullback_hom_fst]
  have heC : IsPullback eC (ι ≫ ProjSpace.π E n) pY b := by
    refine IsPullback.of_right ?_ heCp hpY
    rw [heCt, hb]
    exact hpM
  have heX : IsPullback eX (pullback.snd f bE) pZ b := by
    refine IsPullback.of_right ?_ heXp hpZ
    rw [heXt, hb]
    exact hpX
  have heXorig : eX ≫ tZ = pullback.fst f bE := by
    dsimp only [tZ]
    rw [← Category.assoc, heXt]
    exact changeBase_fst _ _ _ _ _
  have hrecover : eC ≫ h = g ≫ eX := by
    dsimp only [eC, eX]
    rw [Category.assoc, hrec, ← Category.assoc, hrecA, Category.assoc]
  exact ⟨a, ha, γ, hγ, M, iM, gM, hiM, hpM, S, j, hj, hdj, Y, Z, pY, pZ, tY, tZ,
    hpY, hptZ, hsmY, hprY, hprZ, h, hover,
    b, eC, eX, hb, heC, heX, heCt, heXorig, hrecover⟩

end PhilipponProjectiveMorphismFamilySpread


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericFieldBaseChange

/-- Two base-change paths with the same composite retain canonically
isomorphic actual fibres, with both original projections fixed. -/
lemma exists_comparison_iso
    {X S T U V : Scheme.{u}} (q : X ⟶ S) (a : T ⟶ S) (b : U ⟶ S)
    (c : V ⟶ T) (d : V ⟶ U) (h : c ≫ a = d ≫ b) :
    ∃ e : pullback (pullback.snd q a) c ≅ pullback (pullback.snd q b) d,
      e.hom ≫ pullback.snd (pullback.snd q b) d = pullback.snd (pullback.snd q a) c ∧
      e.hom ≫ pullback.fst (pullback.snd q b) d ≫ pullback.fst q b =
        pullback.fst (pullback.snd q a) c ≫ pullback.fst q a := by
  let hp₁ := (IsPullback.of_hasPullback (pullback.snd q a) c).paste_horiz
    (IsPullback.of_hasPullback q a)
  have hp₂ : IsPullback
      (pullback.fst (pullback.snd q b) d ≫ pullback.fst q b)
      (pullback.snd (pullback.snd q b) d) q (c ≫ a) := by
    rw [h]
    exact (IsPullback.of_hasPullback (pullback.snd q b) d).paste_horiz
      (IsPullback.of_hasPullback q b)
  let e := hp₁.isoPullback ≪≫ hp₂.isoPullback.symm
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, hp₂.isoPullback_inv_snd, hp₁.isoPullback_hom_snd]
  · dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, hp₂.isoPullback_inv_fst, hp₁.isoPullback_hom_fst]

end PhilipponGenericFieldBaseChange

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PhilipponNoetherianPresentation

lemma locallyOfFinitePresentation_of_locallyOfFiniteType
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV hVU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact RingHom.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hVU)

end PhilipponNoetherianPresentation


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponGeometricBaseFamily

/-- Spread a geometrically integral generic covering source and its actual
map, retaining dominance over the original variety. -/
theorem exists_dominating_geometric_source_family
    (k : Type u) [Field k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (q : X ⟶ S) [IsProper q] [IsDominant q]
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∃ E : IntermediateField (S.residueField η) (AlgebraicClosure (S.residueField η)),
      FiniteDimensional (S.residueField η) E ∧
      letI : Algebra k E := ((algebraMap (S.residueField η) E).comp (algebraMap k (S.residueField η))).toAlgebra
      ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧ IsFractionRing B E ∧
        ∃ (N : Scheme.{u}) (qN : N ⟶ S) (t : Spec (.of B) ⟶ N),
          IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
          IsProper qN ∧ Surjective qN ∧ IsOpenImmersion t ∧ IsDominant t ∧
          topologicalKrullDim N = topologicalKrullDim S ∧
          t ≫ (qN ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
          (∃ (nN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nN + 1)) k)),
            IsClosedImmersion iN ∧ iN ≫ ProjSpace.π k nN = qN ≫ π) ∧
          ∃ (a : B) (nM : ℕ) (M : Scheme.{u})
            (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) (Localization.Away a))),
            a ≠ 0 ∧ IsClosedImmersion iM ∧
            ∃ (U : Scheme.{u}) (j : U ⟶ Spec (.of (Localization.Away a))),
              IsOpenImmersion j ∧ DenseRange j ∧
              let u : U ⟶ N := (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ≫ t
              IsOpenImmersion u ∧ IsDominant u ∧
              ∃ (Y : Scheme.{u}) (pY : Y ⟶ U) (tY : Y ⟶ M) (aY : Y ⟶ X),
                IsOpenImmersion tY ∧ Smooth pY ∧ IsProper pY ∧ IsDominant aY ∧
                tY ≫ iM ≫ ProjSpace.π (Localization.Away a) nM = pY ≫ j ∧
                aY ≫ q = pY ≫ u ≫ qN ∧
                ∃ (C₀ : Scheme.{u}) (p₀ : C₀ ⟶ Spec (.of E)) (a₀ : C₀ ⟶ q.fiber η),
                  IsIntegral C₀ ∧ Smooth p₀ ∧ IsProper p₀ ∧ GeometricallyIntegral p₀ ∧
                  topologicalKrullDim C₀ ≤ 1 ∧ IsProper a₀ ∧ Surjective a₀ ∧
                  a₀ ≫ q.fiberToSpecResidueField η = p₀ ≫
                    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ∧
                  ∃ (b : Spec (.of E) ⟶ U) (eC : C₀ ⟶ Y),
                    b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ∧
                    IsPullback eC p₀ pY b ∧ eC ≫ aY = a₀ ≫ q.fiberι η := by
  let κ := S.residueField η
  letI : Algebra k κ :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
  let πC := q.fiberToSpecResidueField η
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (q ≫ π)
  have hIG : IsIntegral (q.fiber (genericPoint S)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant q
  haveI : IsIntegral (q.fiber η) :=
    (congrArg (fun x : S => IsIntegral (q.fiber x)) (hη.eq (genericPoint_spec S))).mpr hIG
  haveI : IsProper πC := MorphismProperty.pullback_snd q (S.fromSpecResidueField η) inferInstance
  obtain ⟨E, hE, C₀, a₀, p₀, hC₀, hpa₀, hsa₀, hsm₀, hpp₀, hgeo₀, _hconn₀,
    hdC₀, hbase₀, n₀, i₀, hi₀, hpi₀⟩ :=
    AlgebraicGeometry.exists_finite_extension_integral_smooth_projective_cover_of_integral_proper_dimension_le_one
      κ (AlgebraicClosure κ) πC hdim
  let α := pullback.lift a₀ p₀ hbase₀
  have hαf : α ≫ pullback.fst πC _ = a₀ := pullback.lift_fst _ _ _
  have hαp : α ≫ pullback.snd πC _ = p₀ := pullback.lift_snd _ _ _
  haveI : FiniteDimensional κ E := hE
  letI : Algebra k E := ((algebraMap κ E).comp (algebraMap k κ)).toAlgebra
  letI : IsScalarTower k κ E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B, hBft, hBn, hBE, N, qN, t, hN, hnN, hqN, hsqN, ht, htd, hdN,
    htbase, hgeneric, nN, iN, hiN, hbaseN⟩ :=
    AlgebraicGeometry.exists_normal_projective_model_of_finite_genericResidueField_extension
      k π m i hi η hη E
  haveI : Algebra.FiniteType k B := hBft
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsFractionRing B E := hBE
  haveI : IsIntegral N := hN
  haveI : IsOpenImmersion t := ht
  let β := t ≫ qN
  let bBE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bκE := Spec.map (CommRingCat.ofHom (algebraMap κ E))
  have hβ : bBE ≫ β = bκE ≫ S.fromSpecResidueField η := hgeneric
  let fB := pullback.snd q β
  haveI : LocallyOfFinitePresentation fB :=
    PhilipponNoetherianPresentation.locallyOfFinitePresentation_of_locallyOfFiniteType fB
  obtain ⟨e, heS, heX⟩ := PhilipponGenericFieldBaseChange.exists_comparison_iso
    q (S.fromSpecResidueField η) β bκE bBE hβ.symm
  let e' : pullback πC bκE ≅ pullback fB bBE := e
  have heS' : e'.hom ≫ pullback.snd fB bBE = pullback.snd πC bκE := heS
  have heX' : e'.hom ≫ pullback.fst fB bBE ≫ pullback.fst q β =
      pullback.fst πC bκE ≫ q.fiberι η := heX
  let g := α ≫ e'.hom
  haveI : IsClosedImmersion i₀ := hi₀
  haveI : Smooth (i₀ ≫ ProjSpace.π E n₀) := by rw [hpi₀]; exact hsm₀
  have hg : g ≫ pullback.snd fB bBE = i₀ ≫ ProjSpace.π E n₀ := by
    dsimp only [g]
    rw [Category.assoc, heS', hαp, hpi₀]
  obtain ⟨a, ha, γ, _hγ, M, iM, _gM, hiM, _hpM,
    U, j, hj, hdj, Y, Z, pY, pZ, tY, tB, hpY, hpZ, hsmY, hprY, _hprZ,
    h, hover, b, eC, eX, hb, heC, _heX, _heCt, heXt, hrec⟩ :=
    PhilipponProjectiveMorphismFamilySpread.exists_projective_morphism_family
      B E fB C₀ n₀ i₀ g hg
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))
  let u := (j ≫ bA) ≫ t
  let tZ := tB ≫ pullback.fst q β
  let aY := h ≫ tZ
  haveI : IsOpenImmersion j := hj
  haveI : IsOpenImmersion bA := IsOpenImmersion.of_isLocalization a
  haveI : IsOpenImmersion u := by dsimp only [u]; infer_instance
  haveI : Nonempty U := ⟨b default⟩
  have hu : IsDominant u := ⟨u.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : IsOpenImmersion tY := MorphismProperty.of_isPullback hpY.flip inferInstance
  have hpZ' : IsPullback tZ pZ q (u ≫ qN) := by
    simpa only [tZ, u, β, Category.assoc] using
      hpZ.paste_horiz (IsPullback.of_hasPullback q β)
  have hγbase : Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ bA = bBE := by
    dsimp only [bA, bBE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  have hbu : b ≫ u = bBE ≫ t := by
    dsimp only [u]
    rw [← Category.assoc, ← Category.assoc, hb, hγbase]
  have hrecover : eC ≫ aY = a₀ ≫ q.fiberι η := by
    calc
      eC ≫ aY = g ≫ eX ≫ tZ := by
        dsimp only [aY]; rw [← Category.assoc, hrec, Category.assoc]
      _ = g ≫ pullback.fst fB bBE ≫ pullback.fst q β := by
        dsimp only [tZ]; rw [← Category.assoc eX, heXt]
      _ = α ≫ (e'.hom ≫ pullback.fst fB bBE ≫ pullback.fst q β) := by
        dsimp only [g]; simp only [Category.assoc]
      _ = α ≫ (pullback.fst πC bκE ≫ q.fiberι η) := by rw [heX']
      _ = a₀ ≫ q.fiberι η := by rw [← Category.assoc, hαf]
  haveI : Surjective a₀ := hsa₀
  haveI : IsDominant (q.fiberι η) := PhilipponGenericDominance.genericFiber_inclusion q η hη
  have hdom : IsDominant aY :=
    PhilipponGenericDominance.of_recovered_generic_cover eC aY a₀ (q.fiberι η) hrecover
  have heC' : IsPullback eC p₀ pY b := by simpa only [hpi₀] using heC
  have hqa : aY ≫ q = pY ≫ u ≫ qN := by
    dsimp only [aY]
    rw [Category.assoc, hpZ'.w, ← Category.assoc, hover]
  exact ⟨E, hE, B, hBft, hBn, hBE, N, qN, t, hN, hnN, hqN, hsqN, ht, htd, hdN,
    htbase, ⟨nN, iN, hiN, hbaseN⟩, a, n₀, M, iM, ha, hiM,
    U, j, hj, hdj, inferInstance, hu, Y, pY, tY, aY, inferInstance, hsmY, hprY, hdom,
    hpY.w, hqa, C₀, p₀, a₀, hC₀, hsm₀, hpp₀, hgeo₀, hdC₀, hpa₀, hsa₀, hbase₀,
    b, eC, hbu, heC', hrecover⟩

end PhilipponGeometricBaseFamily


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



set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAffineProjectiveCompactification

lemma exists_affine_immersion
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (j : Spec (.of A) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)),
      IsImmersion j ∧ j ≫ ProjSpace.π k n =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  haveI : IsClosedImmersion f := IsClosedImmersion.spec_of_surjective _ hφ
  let j := f ≫ PhilipponAlterationProjection.ProjectiveAffineChart.embedding k n
  refine ⟨n, j, inferInstance, ?_⟩
  dsimp only [j]
  rw [Category.assoc, PhilipponAlterationProjection.ProjectiveAffineChart.embedding_over]
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact φ.commutes r

end PhilipponAffineProjectiveCompactification

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponAbsoluteSmoothOpen

/-- A smooth proper family over a reduced finite-type base over a perfect
field has dense base and source opens smooth over that field. -/
lemma exists_dense_absolute_smooth_open
    (k : Type u) [Field k] [PerfectField k]
    {S Y : Scheme.{u}} [IsReduced S]
    (c : S ⟶ Spec (.of k)) [LocallyOfFinitePresentation c]
    (p : Y ⟶ S) [Smooth p] [IsProper p] :
    ∃ V : S.Opens, Dense (V : Set S) ∧ Dense ((p ⁻¹ᵁ V) : Set Y) ∧
      Smooth (V.ι ≫ c) ∧ Smooth ((p ⁻¹ᵁ V).ι ≫ p ≫ c) ∧
      Smooth (p ∣_ V) ∧ IsProper (p ∣_ V) := by
  let V := c.smoothLocus
  have hV : Dense (V : Set S) := c.dense_smoothLocus_of_perfectField
  have hpre : Dense ((p ⁻¹ᵁ V) : Set Y) := hV.preimage p.isOpenMap
  have hsmV : Smooth (V.ι ≫ c) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact x.property
  haveI : Smooth (V.ι ≫ c) := hsmV
  have H : Smooth ((p ∣_ V) ≫ (V.ι ≫ c)) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at H
  exact ⟨V, hV, hpre, hsmV, H, inferInstance, inferInstance⟩

end PhilipponAbsoluteSmoothOpen

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponRelativeProjectiveImmersion

/-- An immersion into relative projective space over an affine finite-type
algebra has an absolute projective immersion with the same structure map. -/
lemma exists_absolute_projective_immersion
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    [IsImmersion j] :
    ∃ (d : ℕ) (ι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
      IsImmersion ι ∧ ι ≫ ProjSpace.π k d =
        j ≫ ProjSpace.π A n ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨m, a, ha, hbase⟩ := PhilipponAffineProjectiveCompactification.exists_affine_immersion k A
  haveI : IsImmersion a := ha
  let pb := ProjSpace.isPullback_map k A n
  have hw : ProjSpace.map k A n ≫ ProjSpace.π k n =
      (ProjSpace.π A n ≫ a) ≫ ProjSpace.π k m := by
    rw [Category.assoc, hbase]
    exact pb.w
  let v := pullback.lift (ProjSpace.map k A n) (ProjSpace.π A n ≫ a) hw
  have hpv : IsPullback v (ProjSpace.π A n)
      (pullback.snd (ProjSpace.π k n) (ProjSpace.π k m)) a := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, hbase]
    exact pb
  haveI : IsImmersion v := MorphismProperty.of_isPullback hpv.flip ha
  obtain ⟨d, l, _hd, hl, hlbase⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      (ProjSpace.π k n) (ProjSpace.π k m)
      n (𝟙 _) inferInstance (Category.id_comp _)
      m (𝟙 _) inferInstance (Category.id_comp _)
  haveI : IsClosedImmersion l := hl
  refine ⟨d, j ≫ v ≫ l, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, hlbase,
    ← Category.assoc v, pullback.lift_fst, pb.w]

end PhilipponRelativeProjectiveImmersion

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGenericFiberSmoothTransport

/-- Smoothness of the scalar-extended fibre descends along its actual
residue-field extension. -/
lemma smooth_fiber_of_isPullback
    {W G U N : Scheme.{u}} (t : W ⟶ G) (p : W ⟶ U) [Smooth p]
    (f : G ⟶ N) (u : U ⟶ N) (h : IsPullback t p f u) (x : U) :
    Smooth (f.fiberToSpecResidueField (u x)) := by
  let γ := u.residueFieldMap x
  letI : Algebra (N.residueField (u x)) (U.residueField x) := γ.hom.toAlgebra
  have hsm : Smooth (p.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd p (U.fromSpecResidueField x) inferInstance
  exact PhilipponFieldModelProperties.smooth_of_isPullback_field
    (N.residueField (u x)) (U.residueField x)
    (f.fiberToSpecResidueField (u x)) (p.fiberToSpecResidueField x) _
    (isPullback_fiberToSpecResidueField_of_isPullback h x) hsm

lemma smooth_genericFiber_of_isPullback
    {W G U N : Scheme.{u}} [IsIntegral U] [IsIntegral N]
    (t : W ⟶ G) (p : W ⟶ U) [Smooth p]
    (f : G ⟶ N) (u : U ⟶ N) [IsDominant u]
    (h : IsPullback t p f u) (η : N) (hη : IsGenericPoint η Set.univ) :
    Smooth (f.fiberToSpecResidueField η) := by
  have he : η = u (genericPoint U) :=
    (hη.eq (genericPoint_spec N)).trans (PhilipponGenericDominance.genericPoint_eq_of_dominant u).symm
  exact (congrArg (fun x : N => Smooth (f.fiberToSpecResidueField x)) he).mpr
    (smooth_fiber_of_isPullback t p f u h (genericPoint U))

end PhilipponGenericFiberSmoothTransport

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponNormalComponents

/-- A domain stalk forces all components through the point to be the
closure of the same irreducible local spectrum. -/
lemma component_eq_closure_stalk_range
    {X : Scheme.{u}} (x : X) [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure (Set.range (X.fromSpecStalk x)) := by
  have hR : IsIrreducible (closure (Set.range (X.fromSpecStalk x))) := by
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        (X.fromSpecStalk x) (X.fromSpecStalk x).continuous.continuousOn).closure
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hm : hZ.1.genericPoint ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hg.specializes hx
  have hsub : Z ⊆ closure (Set.range (X.fromSpecStalk x)) := by
    rw [← hg.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hm)
  exact hsub.antisymm (hZ.2 hR hsub)

lemma component_eq_of_mem
    {X : Scheme.{u}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (x : X) (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  haveI := hX x
  exact (component_eq_closure_stalk_range x hZ hxZ).trans
    (component_eq_closure_stalk_range x hW hxW).symm

lemma isClopen_component
    {X : Scheme.{u}} [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsClopen Z := by
  classical
  have heq : Z = (⋃₀ (irreducibleComponents X \ {Z}))ᶜ := by
    ext x
    constructor
    · intro hx hother
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp hother
      have he := component_eq_of_mem hX hZ hW.1 x hx hxW
      exact hW.2 (Set.mem_singleton_iff.mpr he.symm)
    · intro hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp
        (show x ∈ ⋃₀ irreducibleComponents X by rw [sUnion_irreducibleComponents]; trivial)
      have he : W = Z := by
        by_contra hn
        exact hx (Set.mem_sUnion.mpr ⟨W, ⟨hW, by simpa using hn⟩, hxW⟩)
      simpa only [he] using hxW
  refine ⟨isClosed_of_mem_irreducibleComponents Z hZ, ?_⟩
  rw [heq, isOpen_compl_iff, Set.sUnion_eq_biUnion]
  exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
    (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)

end PhilipponNormalComponents


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponSmoothConnectedIntegralFamily

lemma isIntegral_of_connected_of_domain_stalk
    (X : Scheme.{u}) [NoetherianSpace X] [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  letI (x : X) : IsDomain (X.presheaf.stalk x) := hX x
  letI : IsReduced X := isReduced_of_isReduced_stalk X
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨Z, hZ, _hxZ⟩ := Set.mem_sUnion.mp
    (show x ∈ ⋃₀ irreducibleComponents X by rw [sUnion_irreducibleComponents]; trivial)
  have hcl := PhilipponNormalComponents.isClopen_component hX hZ
  have he : Z = Set.univ := hcl.eq_univ hZ.1.nonempty
  letI : IrreducibleSpace X := (irreducibleSpace_def X).mpr
    ((congrArg (fun S : Set X => IsIrreducible S) he).mp hZ.1)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- Smooth proper geometrically connected families have geometrically
integral fibres, since their geometric fibres are connected and locally domains. -/
theorem geometricallyIntegral_of_smooth_proper_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  constructor
  intro K _ y Z fst snd hp
  letI : Smooth snd := MorphismProperty.of_isPullback hp inferInstance
  letI : IsProper snd := MorphismProperty.of_isPullback hp inferInstance
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace snd
  letI : IsNoetherian Z := ⟨⟩
  letI : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace
    (f := f) y fst snd hp
  letI : Field Γ(Spec (.of K), ⊤) :=
    (isField_of_isIntegral_of_subsingleton (Spec (.of K))).toField
  exact isIntegral_of_connected_of_domain_stalk Z fun z =>
    (Smooth.isDomain_and_isIntegrallyClosed_stalk snd z).1

/-- The whole proper smooth family over a normal affine base is
geometrically integral if its actual fraction-field source is so. -/
theorem geometricallyIntegral_of_smooth_proper_generic_source
    (R E : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field E] [Algebra R E] [IsFractionRing R E]
    {X C : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [IsProper f]
    (p : C ⟶ Spec (.of E)) [GeometricallyIntegral p] (e : C ⟶ X)
    (h : IsPullback e p f (Spec.map (CommRingCat.ofHom (algebraMap R E)))) :
    GeometricallyIntegral f := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R E))
  have hc : GeometricallyIntegral (h.isoPullback.hom ≫ pullback.snd f b) := by
    rw [h.isoPullback_hom_snd]
    infer_instance
  letI : GeometricallyIntegral (pullback.snd f b) :=
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral h.isoPullback.hom _).mp hc
  letI : GeometricallyConnected (pullback.snd f b) :=
    PhilipponFieldModelIntegral.geometricallyConnected_of_geometricallyIntegral _
  letI : GeometricallyConnected f :=
    AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_pullback_snd
      E f
  exact geometricallyIntegral_of_smooth_proper_geometricallyConnected f

end PhilipponSmoothConnectedIntegralFamily


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponPrincipalBaseRestriction

/-- A prescribed fraction-field point inside an open affine chart factors
through a nonzero principal localization contained in that same chart. -/
lemma exists_principal_lift
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ Spec (.of B)) [IsOpenImmersion j]
    (b : Spec (.of E) ⟶ U)
    (hb : b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B E))) :
    ∃ s : B, s ≠ 0 ∧ ∃ γ : Localization.Away s →ₐ[B] E, Function.Injective γ ∧
      ∃ i : Spec (.of (Localization.Away s)) ⟶ U,
        IsOpenImmersion i ∧ IsDominant i ∧
        i ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))) ∧
        Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ i = b := by
  let z := b (IsLocalRing.closedPoint E)
  obtain ⟨_, ⟨s, rfl⟩, hzs, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show j z ∈ Set.range j from ⟨z, rfl⟩) j.isOpenEmbedding.isOpen_range
  have hs : s ≠ 0 := by
    intro hzero
    subst hzero
    simpa using hzs
  obtain ⟨γ, hγ⟩ := PhilipponFractionFieldLocalization.exists_embedding B E s hs
  let R := Localization.Away s
  let β := Spec.map (CommRingCat.ofHom (algebraMap B R))
  have hrange : Set.range β ⊆ Set.range j := by
    change Set.range (PrimeSpectrum.comap (algebraMap B R)) ⊆ Set.range j
    rw [PrimeSpectrum.localization_away_comap_range R s]
    exact hsub
  let i := IsOpenImmersion.lift j β hrange
  have hij : i ≫ j = β := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion β := IsOpenImmersion.of_isLocalization s
  haveI : IsOpenImmersion (i ≫ j) := by rw [hij]; infer_instance
  haveI : IsOpenImmersion i := IsOpenImmersion.of_comp i j
  haveI : IsDomain R := Function.Injective.isDomain γ.toRingHom hγ
  have hi : IsDominant i := ⟨i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hβ : Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ β =
      Spec.map (CommRingCat.ofHom (algebraMap B E)) := by
    dsimp only [β]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) γ.comp_algebraMap
  have hbi : Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ i = b := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hij, hβ, hb]
  exact ⟨s, hs, γ, hγ, i, inferInstance, hi, hij, hbi⟩

end PhilipponPrincipalBaseRestriction


set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGeometricPrincipalFamily

/-- A smooth proper family on an open of a normal affine fraction-field
model has a principal affine restriction with geometrically integral fibres. -/
theorem exists_geometricallyIntegral_principal_family
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Field E] [Algebra B E] [IsFractionRing B E]
    {U Y C : Scheme.{u}} [IsIntegral U]
    (j : U ⟶ Spec (.of B)) [IsOpenImmersion j]
    (b : Spec (.of E) ⟶ U)
    (hb : b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B E)))
    (p : Y ⟶ U) [Smooth p] [IsProper p]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) [GeometricallyIntegral p₀]
    (hp₀ : IsPullback e p₀ p b) :
    ∃ s : B, s ≠ 0 ∧ ∃ γ : Localization.Away s →ₐ[B] E, Function.Injective γ ∧
      ∃ i : Spec (.of (Localization.Away s)) ⟶ U,
        IsOpenImmersion i ∧ IsDominant i ∧
        i ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))) ∧
        Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ i = b ∧
        IsDominant (pullback.fst p i) ∧ GeometricallyIntegral (pullback.snd p i) ∧
        ∃ e' : C ⟶ pullback p i,
          IsPullback e' p₀ (pullback.snd p i) (Spec.map (CommRingCat.ofHom γ.toRingHom)) ∧
          e' ≫ pullback.fst p i = e := by
  obtain ⟨s, hs, γ, hγ, i, hi, hdi, hij, hbi⟩ :=
    PhilipponPrincipalBaseRestriction.exists_principal_lift B E j b hb
  let R := Localization.Away s
  letI : Algebra R E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B R E := IsScalarTower.of_algebraMap_eq fun x => (γ.commutes x).symm
  letI : IsFractionRing R E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := R) hγ
  letI : IsDomain R := Function.Injective.isDomain γ.toRingHom hγ
  have hM : Submonoid.powers s ≤ nonZeroDivisors B := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs)
  letI : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R _ hM
  letI : IsOpenImmersion i := hi
  letI : IsDominant i := hdi
  let hR := IsPullback.of_hasPullback p i
  have hw : e ≫ p = (p₀ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) ≫ i := by
    rw [Category.assoc, hbi]
    exact hp₀.w
  let e' := hR.lift e (p₀ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) hw
  have he' : IsPullback e' p₀ (pullback.snd p i) (Spec.map (CommRingCat.ofHom γ.toRingHom)) := by
    refine IsPullback.of_right ?_ (hR.lift_snd _ _ _) hR
    rw [hR.lift_fst, hbi]
    exact hp₀
  have hdom : IsDominant (pullback.fst p i) := by
    constructor
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact i.denseRange.preimage p.isOpenMap
  have hgeo : GeometricallyIntegral (pullback.snd p i) :=
    PhilipponSmoothConnectedIntegralFamily.geometricallyIntegral_of_smooth_proper_generic_source
      R E (pullback.snd p i) p₀ e' he'
  exact ⟨s, hs, γ, hγ, i, hi, hdi, hij, hbi, hdom, hgeo, e', he', hR.lift_fst _ _ _⟩

end PhilipponGeometricPrincipalFamily

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponIntegralCurveFamilyModel

/-- Complete a relative projective family without carrying the generic-field
presentation through the geometric construction. -/
lemma exists_geometric_model_of_relative_projective_family
    (k A : Type u) [Field k] [PerfectField k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {S X N U Y M : Scheme.{u}} [IsIntegral S] [IsIntegral X] [IsIntegral N] [IsIntegral U]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) (hqπ : q ≫ πS = πX)
    (qN : N ⟶ S) [IsProper qN] [Surjective qN]
    (hnN : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x))
    (hdN : topologicalKrullDim N = topologicalKrullDim S)
    (nN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nN + 1)) k))
    [IsClosedImmersion iN] (hbaseN : iN ≫ ProjSpace.π k nN = qN ≫ πS)
    (u : U ⟶ N) [IsOpenImmersion u] [IsDominant u]
    (pY : Y ⟶ U) [Smooth pY] [IsProper pY] [GeometricallyIntegral pY]
    (nM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) A))
    [IsClosedImmersion iM] (tY : Y ⟶ M) [IsOpenImmersion tY]
    (j : U ⟶ Spec (.of A))
    (hpYeq : tY ≫ iM ≫ ProjSpace.π A nM = pY ≫ j)
    (hjbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = u ≫ qN ≫ πS)
    (aY : Y ⟶ X) [IsDominant aY] (hqa : aY ≫ q = pY ≫ u ≫ qN)
    (E : Type u) [Field E] (b : Spec (.of E) ⟶ U) [IsDominant b] [IsPreimmersion b]
    (C₀ : Scheme.{u}) (eC₀ : C₀ ⟶ Y) (p₀ : C₀ ⟶ Spec (.of E)) [GeometricallyIntegral p₀]
    (hpC₀ : IsPullback eC₀ p₀ pY b) (hdC₀ : topologicalKrullDim C₀ ≤ 1) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      GeometricallyIntegral pW ∧ GeometricallyConnected pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyIntegral (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyConnected (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  let πN := qN ≫ πS
  have hN : IsIntegral N := inferInstance
  have hqN : IsProper qN := inferInstance
  have hsqN : Surjective qN := inferInstance
  have hiN : IsClosedImmersion iN := inferInstance
  haveI : IsProper πN := inferInstance
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian πN
  haveI : CompactSpace N := (quasiCompact_iff_compactSpace πN).mp inferInstance
  haveI : IsNoetherian N := ⟨⟩
  haveI : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion u
  haveI : NoetherianSpace U := u.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  haveI : CompactSpace Y := (quasiCompact_iff_compactSpace pY).mp inferInstance
  haveI : IsNoetherian Y := ⟨⟩
  let cU := u ≫ πN
  obtain ⟨V, hdV, hdYV, hsmV, hsmYV, _hsp, _hpp⟩ :=
    PhilipponAbsoluteSmoothOpen.exists_dense_absolute_smooth_open k cU pY
  let Y₁ : Y.Opens := pY ⁻¹ᵁ V
  let p₁ : (Y₁ : Scheme.{u}) ⟶ (V : Scheme.{u}) := pY ∣_ V
  let u₁ : (V : Scheme.{u}) ⟶ N := V.ι ≫ u
  let a₁ : (Y₁ : Scheme.{u}) ⟶ X := Y₁.ι ≫ aY
  haveI : IsDominant V.ι := ⟨by simpa only [DenseRange, Scheme.Opens.range_ι] using hdV⟩
  haveI : Nonempty (V : Scheme.{u}) := by
    obtain ⟨v, hv⟩ := hdV.nonempty
    exact ⟨⟨v, hv⟩⟩
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion V.ι
  haveI : IsDominant Y₁.ι := ⟨by simpa only [DenseRange, Scheme.Opens.range_ι] using hdYV⟩
  haveI : NoetherianSpace (Y₁ : Scheme.{u}) :=
    Y₁.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : Smooth p₁ := inferInstance
  haveI : IsProper p₁ := inferInstance
  have hrestr : p₁ ≫ V.ι = Y₁.ι ≫ pY := morphismRestrict_ι pY V
  have hπ₁ : p₁ ≫ u₁ ≫ πN = Y₁.ι ≫ pY ≫ cU := by
    simpa only [p₁, u₁, cU, Category.assoc] using
      congrArg (fun f => f ≫ u ≫ πN) hrestr
  haveI : Smooth (p₁ ≫ u₁ ≫ πN) := by rw [hπ₁]; exact hsmYV
  haveI : Smooth (u₁ ≫ πN) := by simpa only [u₁, cU, Category.assoc] using hsmV
  have hbaseY : aY ≫ πX = pY ≫ u ≫ πN := by
    calc
      aY ≫ πX = (aY ≫ q) ≫ πS := by simp only [Category.assoc, hqπ]
      _ = (pY ≫ u ≫ qN) ≫ πS := congrArg (fun f => f ≫ πS) hqa
      _ = pY ≫ u ≫ πN := by simp only [πN, Category.assoc]
  have hqa₁ : a₁ ≫ q = p₁ ≫ u₁ ≫ qN := by
    calc
      a₁ ≫ q = Y₁.ι ≫ pY ≫ u ≫ qN := by
        simpa only [a₁, Category.assoc] using congrArg (fun f => Y₁.ι ≫ f) hqa
      _ = p₁ ≫ u₁ ≫ qN := by
        symm
        simpa only [u₁, Category.assoc] using congrArg (fun f => f ≫ u ≫ qN) hrestr
  have ha₁ : a₁ ≫ πX = p₁ ≫ u₁ ≫ πN := by
    rw [hπ₁]
    simpa only [a₁, cU, Category.assoc] using congrArg (fun f => Y₁.ι ≫ f) hbaseY
  obtain ⟨n₁, j₁, hj₁, hbasej₁⟩ :=
    PhilipponRelativeProjectiveImmersion.exists_absolute_projective_immersion k A nM (Y₁.ι ≫ tY ≫ iM)
  haveI : IsImmersion j₁ := hj₁
  have hrelk : tY ≫ iM ≫ ProjSpace.π A nM ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      pY ≫ u ≫ πN := by
    simpa only [Category.assoc, hjbase] using
      congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))) hpYeq
  have hj₁base : j₁ ≫ ProjSpace.π k n₁ = p₁ ≫ u₁ ≫ πN := by
    calc
      j₁ ≫ ProjSpace.π k n₁ = Y₁.ι ≫ (tY ≫ iM ≫ ProjSpace.π A nM ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
        simpa only [Category.assoc] using hbasej₁
      _ = Y₁.ι ≫ pY ≫ cU := by
        simpa only [cU, Category.assoc] using congrArg (fun f => Y₁.ι ≫ f) hrelk
      _ = p₁ ≫ u₁ ≫ πN := hπ₁.symm
  obtain ⟨W, G, fX, fN, tW, hW, _hcW, hsmW, hprW, hsurW, habsW, _hdomW,
    hG, hnG, hfX, hsfX, hfN, hsfN, htW, hdtW, htX, hpull, hcomp, hdG,
    dG, jG, hjG, hjGbase⟩ :=
    AlgebraicGeometry.exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
      k u₁ p₁ πX mX iX hiX πN nN iN hbaseN n₁ j₁ hj₁base a₁ ha₁
  have hgenericDim (ηN : N) (hηN : IsGenericPoint ηN Set.univ) :
      topologicalKrullDim (fN.fiber ηN) ≤ 1 :=
    (AlgebraicGeometry.topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily
      E pY b eC₀ p₀ hpC₀ V hdV W.ι tW fN u₁ hpull ηN hηN).trans hdC₀
  haveI : IsIntegral G := hG
  haveI : IsDominant tW := hdtW
  haveI : IsProper fX := hfX
  haveI : IsProper fN := hfN
  haveI : Surjective fN := hsfN
  haveI : Smooth (W.ι ≫ p₁) := hsmW
  haveI : Surjective (W.ι ≫ p₁) := hsurW
  haveI : GeometricallyIntegral p₁ := inferInstance
  have hgeoW : GeometricallyIntegral (W.ι ≫ p₁) :=
    PhilipponGenericFieldPointIso.geometricallyIntegral_of_surjective_open_subfamily W.ι p₁
  haveI : GeometricallyIntegral (W.ι ≫ p₁) := hgeoW
  have hconnW := PhilipponFieldModelIntegral.geometricallyConnected_of_geometricallyIntegral (W.ι ≫ p₁)
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (fX ≫ πX)
  have hIGeneric : IsIntegral (fN.fiber (genericPoint N)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant fN
  have hgeneric (ηN : N) (hηN : IsGenericPoint ηN Set.univ) :
      IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
      IsProper (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyIntegral (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyConnected (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1 := by
    have he : ηN = genericPoint N := hηN.eq (genericPoint_spec N)
    have hi : IsIntegral (fN.fiber ηN) :=
      (congrArg (fun x : N => IsIntegral (fN.fiber x)) he).mpr hIGeneric
    have hs := PhilipponGenericFiberSmoothTransport.smooth_genericFiber_of_isPullback
      tW (W.ι ≫ p₁) fN u₁ hpull ηN hηN
    have hp : IsProper (fN.fiberToSpecResidueField ηN) :=
      MorphismProperty.pullback_snd fN (N.fromSpecResidueField ηN) inferInstance
    have hgeo := PhilipponGeometricGenericTransport.geometricallyIntegral_genericFiber_of_cartesian_open_subfamily
      E pY b eC₀ p₀ hpC₀ V hdV W.ι tW fN u₁ hpull ηN hηN
    letI : GeometricallyIntegral (fN.fiberToSpecResidueField ηN) := hgeo
    have hconn := PhilipponFieldModelIntegral.geometricallyConnected_of_geometricallyIntegral
      (fN.fiberToSpecResidueField ηN)
    exact ⟨hi, hs, hp, hgeo, hconn, hgenericDim ηN hηN⟩

  have hcomm : fX ≫ q = fN ≫ qN := by
    apply ext_of_isDominant_of_isSeparated πS ?_ tW ?_
    · simpa only [πN, Category.assoc, hqπ] using hcomp
    · calc
        tW ≫ (fX ≫ q) = (W.ι ≫ a₁) ≫ q := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ q) htX
        _ = W.ι ≫ p₁ ≫ u₁ ≫ qN := by simp only [Category.assoc, hqa₁]
        _ = tW ≫ (fN ≫ qN) := by
          simpa only [Category.assoc] using (congrArg (fun f => f ≫ qN) hpull.w).symm
  exact ⟨N, qN, V, u₁, W, W.ι ≫ p₁, G, fX, fN, tW,
    hN, hnN, hqN, hsqN, hdN, inferInstance, inferInstance, inferInstance,
    inferInstance, hW, hsmW, hprW, hsurW, hgeoW, hconnW, habsW, hG, hnG, hfX, hsfX, hfN, hsfN,
    htW, hdtW, hpull, hgeneric, hcomm, hcomp, hdG, ⟨nN, iN, hiN, hbaseN⟩,
    dG, jG, hjG, hjGbase⟩


end PhilipponIntegralCurveFamilyModel


set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponIntegralCurveFamilyApplication

/-- Apply the accepted finite-generic-field covering data and its global
normal projective completion to the original projective fibration. -/
theorem exists_geometric_curve_family_model
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      GeometricallyIntegral pW ∧ GeometricallyConnected pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyIntegral (fN.fiberToSpecResidueField ηN) ∧
        GeometricallyConnected (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  letI : Algebra k (S.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
  obtain ⟨E, hE, hrest⟩ :=
    PhilipponGeometricBaseFamily.exists_dominating_geometric_source_family k πS mS iS hiS q η hη hdim
  letI : Algebra k E := ((algebraMap (S.residueField η) E).comp (algebraMap k (S.residueField η))).toAlgebra
  obtain ⟨B, hBft, hBn, hBE, N, qN, tN, hN, hnN, hqN, hsqN, htN, hdtN, hdN,
    htbase, ⟨nN, iN, hiN, hbaseN⟩, a, nM, M, iM, ha, hiM,
    U, j, hj, _hdj, hu, hdu, Y, pY, tY, aY, htY, hsmY, hprY, hdomY,
    hpYeq, hYq, C₀, p₀, a₀, _hC₀, _hsm₀, _hpr₀, hgeo₀, hdC₀,
    _hpra₀, _hsura₀, _hbase₀, b, eC₀, hbu, hpC₀, _hrec⟩ := hrest
  let A := Localization.Away a
  let u : U ⟶ N := (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B A))) ≫ tN
  let πN := qN ≫ πS
  haveI : Algebra.FiniteType k B := hBft
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (R := k) (S := B) (A := A) inferInstance inferInstance
  haveI : IsIntegral N := hN
  haveI : IsProper qN := hqN
  haveI : Surjective qN := hsqN
  haveI : IsClosedImmersion iN := hiN
  haveI : IsClosedImmersion iM := hiM
  haveI : IsOpenImmersion tN := htN
  haveI : IsOpenImmersion j := hj
  haveI : IsOpenImmersion u := hu
  haveI : IsDominant u := hdu
  haveI : Nonempty U := ⟨b (genericPoint (Spec (.of E)))⟩
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion u
  haveI : Smooth pY := hsmY
  haveI : IsProper pY := hprY
  haveI : IsDominant aY := hdomY
  haveI : IsOpenImmersion tY := htY
  have hmaps : Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Spec.map_comp]
    congr 1
  have hjbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = u ≫ πN := by
    simp only [u, πN, Category.assoc, htbase, hmaps]
  haveI : IsFractionRing B E := hBE
  haveI : IsDominant tN := hdtN
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap B E))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap B E)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective B E)]
    exact bot_le
  have hb_chart : b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ tN := hbu
  haveI : IsDominant (b ≫ u) := by rw [hb_chart]; infer_instance
  haveI : IsDominant b := IsDominant.of_comp_of_isOpenImmersion b u
  haveI : IsPreimmersion b :=
    PhilipponGenericFieldPointIso.isPreimmersion_of_fractionField_chart B E tN u b hb_chart
  haveI : GeometricallyIntegral p₀ := hgeo₀
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsIntegrallyClosed B := hBn
  have hMa : Submonoid.powers a ≤ nonZeroDivisors B := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ ha)
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A _ hMa
  letI : Algebra (↥B) A := inferInstance
  letI : Algebra (↥B) (↥E) := inferInstance
  obtain ⟨γA, hγA⟩ := PhilipponFractionFieldLocalization.exists_embedding B E a ha
  letI : Algebra A E := γA.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom γA
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγA
  letI : IsDomain A := Function.Injective.isDomain γA.toRingHom hγA
  let βA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  haveI : IsOpenImmersion βA := IsOpenImmersion.of_isLocalization a
  have hγbase : Spec.map (CommRingCat.ofHom γA.toRingHom) ≫ βA =
      Spec.map (CommRingCat.ofHom (algebraMap B E)) := by
    dsimp only [βA]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γA.comp_algebraMap
  have hbj : b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
    apply (cancel_mono βA).mp
    apply (cancel_mono tN).mp
    simpa only [Category.assoc, ← hγbase, u, βA] using hb_chart
  obtain ⟨s, hs, γR, hγR, v, hv, hdv, _hvj, hbR, hdomR, hgeoR, eR, heR, heRf⟩ :=
    PhilipponGeometricPrincipalFamily.exists_geometricallyIntegral_principal_family
      A E j b hbj pY eC₀ p₀ hpC₀
  let R := Localization.Away s
  let pR := pullback.snd pY v
  let tR := pullback.fst pY v
  let bR := Spec.map (CommRingCat.ofHom γR.toRingHom)
  haveI : IsOpenImmersion v := hv
  haveI : IsDominant v := hdv
  haveI : IsDominant tR := hdomR
  haveI : GeometricallyIntegral pR := hgeoR
  haveI : IsIntegral (Spec (.of R)) := by
    haveI : Nonempty (Spec (.of R)) := ⟨bR default⟩
    exact isIntegral_of_isOpenImmersion v
  haveI : IsDominant (bR ≫ v) := by rw [hbR]; infer_instance
  haveI : IsDominant bR := IsDominant.of_comp_of_isOpenImmersion bR v
  haveI : IsPreimmersion (bR ≫ v) := by
    change IsPreimmersion (Spec.map (CommRingCat.ofHom γR.toRingHom) ≫ v)
    rw [hbR]
    infer_instance
  haveI : IsPreimmersion bR := IsPreimmersion.of_comp bR v
  have hRcond : tR ≫ pY = pR ≫ v := pullback.condition
  have hrel : (tR ≫ tY) ≫ iM ≫ ProjSpace.π A nM = pR ≫ (v ≫ j) := by
    calc
      _ = tR ≫ (tY ≫ iM ≫ ProjSpace.π A nM) := by simp only [Category.assoc]
      _ = tR ≫ (pY ≫ j) := congrArg (fun h => tR ≫ h) hpYeq
      _ = (tR ≫ pY) ≫ j := (Category.assoc _ _ _).symm
      _ = (pR ≫ v) ≫ j := congrArg (fun h => h ≫ j) hRcond
      _ = _ := Category.assoc _ _ _
  have hbase : (v ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      (v ≫ u) ≫ qN ≫ πS := by
    simpa only [πN, Category.assoc] using congrArg (fun h => v ≫ h) hjbase
  have hmap : (tR ≫ aY) ≫ q = pR ≫ (v ≫ u) ≫ qN := by
    have hYq' : aY ≫ q = pY ≫ u ≫ qN := hYq
    calc
      _ = tR ≫ (aY ≫ q) := Category.assoc _ _ _
      _ = tR ≫ (pY ≫ u ≫ qN) := congrArg (fun h => tR ≫ h) hYq'
      _ = (tR ≫ pY) ≫ u ≫ qN := by simp only [Category.assoc]
      _ = (pR ≫ v) ≫ u ≫ qN := congrArg (fun h => h ≫ u ≫ qN) hRcond
      _ = _ := by simp only [Category.assoc]
  exact PhilipponIntegralCurveFamilyModel.exists_geometric_model_of_relative_projective_family
    k A πS πX mX iX hiX q hqπ qN hnN hdN nN iN hbaseN (v ≫ u) pR nM iM
      (tR ≫ tY) (v ≫ j) hrel hbase (tR ≫ aY) hmap E bR C₀ eR p₀ heR hdC₀


end PhilipponIntegralCurveFamilyApplication

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {N G : Scheme.{u}}
    [IsIntegral N] [IsIntegral G]
    (πN : N ⟶ Spec (.of K)) [IsProper πN]
    (dN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) K))
    [IsClosedImmersion iN] (hiN : iN ≫ ProjSpace.π K dN = πN)
    (πG : G ⟶ Spec (.of K)) [IsProper πG]
    (dG : ℕ) (iG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) K))
    [IsClosedImmersion iG] (hiG : iG ≫ ProjSpace.π K dG = πG)
    (f : G ⟶ N) [IsProper f] [Surjective f] (hf : f ≫ πN = πG)
    (hnN : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x))
    (hnG : ∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x))
    (hgeneric : ∀ η : N, IsGenericPoint η Set.univ →
      IsIntegral (f.fiber η) ∧ Smooth (f.fiberToSpecResidueField η) ∧
      IsProper (f.fiberToSpecResidueField η) ∧ topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ G),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧ Smooth (a ≫ πG) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ πG := by
  obtain ⟨T, qT, U, u₀, W, p, H, aH, fT, t,
    hT, hnT, hqT, hsqT, _hdT, hU, hu, hdu, hsmU,
    hW, hsmP, hprP, hsurP, hgeoP, hconnP, _hsmW,
    hH, hnH, haH, hsaH, hfT, hsfT, ht, hdt, hcart,
    hgen, _hcomm, hcomp, _hdH, ⟨mT, iT, hiT, heT⟩, ⟨mH, iH, hiH, heH⟩⟩ :=
    PhilipponIntegralCurveFamilyApplication.exists_geometric_curve_family_model
      K πN dN iN hiN πG dG iG hiG f hf (genericPoint N) (genericPoint_spec N)
        (hgeneric (genericPoint N) (genericPoint_spec N)).2.2.2
  let πT := qT ≫ πN
  let πH := aH ≫ πG
  haveI : IsIntegral T := hT
  haveI : IsIntegral H := hH
  haveI : IsIntegral U := hU
  haveI : IsIntegral W := hW
  haveI : IsProper qT := hqT
  haveI : Surjective qT := hsqT
  haveI : IsProper aH := haH
  haveI : Surjective aH := hsaH
  haveI : IsProper fT := hfT
  haveI : Surjective fT := hsfT
  haveI : IsClosedImmersion iT := hiT
  haveI : IsClosedImmersion iH := hiH
  haveI : IsOpenImmersion u₀ := hu
  haveI : IsDominant u₀ := hdu
  haveI : Smooth (u₀ ≫ πT) := hsmU
  haveI : Smooth p := hsmP
  haveI : IsProper p := hprP
  haveI : Surjective p := hsurP
  haveI : GeometricallyIntegral p := hgeoP
  haveI : GeometricallyConnected p := hconnP
  haveI : IsOpenImmersion t := ht
  haveI : IsDominant t := hdt
  have hfh : fT ≫ πT = πH := hcomp.symm
  obtain ⟨Y, a, hY, ha, hsa, hsm, mY, iY, hiY, heY⟩ :=
    AlgebraicGeometry.exists_smooth_projective_cover_of_compactified_geometricallyIntegral_smooth_proper_curve_family
      K πT mT iT heT πH mH iH heH fT hfh hnT hnH u₀ p t hcart
        (fun η hη => (hgen η hη).2.2.2.2.2)
  haveI : IsProper a := ha
  haveI : Surjective a := hsa
  refine ⟨Y, a ≫ aH, hY, inferInstance, inferInstance, ?_, mY, iY, hiY, ?_⟩
  · simpa only [πH, Category.assoc] using hsm
  · simpa only [πH, Category.assoc] using heY
