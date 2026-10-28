-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_model_of_finite_genericResidueField_extension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T14:20:19.224123+00:00
-- url     : https://prove2.me/submissions/02d61a28-fbda-4111-9b42-01b6ae0b6a8f

/- The finite projective normalization portion below reuses the accepted
source of 7d122c2e-85fc-4c12-80b1-6a0ba09d0dca. Its retained affine chart is
used here to preserve a prescribed field extension and generic map. -/
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem
import Theorems.Thm_IsIntegralClosure_finite_of_finiteType

universe u v
set_option linter.style.haveILetI false


set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PhilipponFiniteFieldBaseModel

/-- A finitely generated field extension has an actual finite-type integral affine model
inside the given field, with that field as its fraction field. -/
lemma exists_affine_field_model
    (k E : Type u) [Field k] [Field E] [Algebra k E] [Algebra.EssFiniteType k E] :
    ∃ A : Subalgebra k E, Algebra.FiniteType k A ∧ IsFractionRing A E := by
  let A := Algebra.EssFiniteType.subalgebra k E
  have hM : Algebra.EssFiniteType.submonoid k E = nonZeroDivisors A := by
    ext x
    change IsUnit (x : E) ↔ x ∈ nonZeroDivisors A
    rw [isUnit_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
    simp
  have hfrac : IsFractionRing A E := by
    change IsLocalization (nonZeroDivisors A) E
    rw [← hM]
    infer_instance
  exact ⟨A, inferInstance, hfrac⟩

/-- The finite extension used by the generic-curve cover still has a finite-type affine
ground-field model, without choosing a different abstract field. -/
lemma exists_affine_model_of_finite_field_extension
    (k F E : Type u) [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Algebra.EssFiniteType k F] [FiniteDimensional F E] :
    ∃ A : Subalgebra k E, Algebra.FiniteType k A ∧ IsFractionRing A E := by
  letI : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k F E
  exact exists_affine_field_model k E

end PhilipponFiniteFieldBaseModel



set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PhilipponNormalAffineFieldModel

lemma fractionRing_of_le
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    {A B : Subalgebra k E} (h : A ≤ B) [IsFractionRing A E] : IsFractionRing B E := by
  haveI : FaithfulSMul B E :=
    (faithfulSMul_iff_algebraMap_injective B E).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _hb, hx⟩ := IsFractionRing.div_surjective A x
  exact ⟨⟨a.val, h a.property⟩, ⟨b.val, h b.property⟩, hx.symm⟩

/-- A normal finite-type affine model of the given field can retain any prescribed
finite collection of field elements as regular functions. -/
theorem exists_normal_affine_field_model_containing
    (k E : Type u) [Field k] [Field E] [Algebra k E] [Algebra.EssFiniteType k E]
    (T : Finset E) :
    ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧
      IsFractionRing B E ∧ (T : Set E) ⊆ B := by
  classical
  obtain ⟨A, hA, hAE⟩ := PhilipponFiniteFieldBaseModel.exists_affine_field_model k E
  letI := hA
  letI := hAE
  let C := A ⊔ Algebra.adjoin k (T : Set E)
  have hC : C.FG := ((Subalgebra.fg_iff_finiteType A).mpr hA).sup (Subalgebra.fg_adjoin_finset T)
  letI : Algebra.FiniteType k C := (Subalgebra.fg_iff_finiteType C).mp hC
  letI : IsFractionRing C E := fractionRing_of_le (show A ≤ C from le_sup_left)
  let D := integralClosure C E
  haveI : Module.Finite C D := IsIntegralClosure.finite_of_finiteType k C E E D
  haveI : Algebra.FiniteType k D := Algebra.FiniteType.trans (S := C) inferInstance inferInstance
  have hnormal : IsIntegrallyClosed D := integralClosure.isIntegrallyClosedOfFiniteExtension
    (R := C) E
  have hfrac : IsFractionRing D E := integralClosure.isFractionRing_of_finite_extension E E
  let B := D.restrictScalars k
  let φ : D →ₐ[k] B :=
    { __ := RingHom.id D
      commutes' := by intro r; rfl }
  have hftB : Algebra.FiniteType k B := Algebra.FiniteType.of_surjective φ Function.surjective_id
  refine ⟨B, hftB, hnormal, hfrac, ?_⟩
  intro x hx
  have hxC : x ∈ C :=
    (show Algebra.adjoin k (T : Set E) ≤ C from le_sup_right) (Algebra.subset_adjoin hx)
  change IsIntegral C x
  exact isIntegral_algebraMap (x := (⟨x, hxC⟩ : C))

end PhilipponNormalAffineFieldModel



open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

noncomputable abbrev functionFieldAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra

noncomputable abbrev chartAlgebra {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom.toAlgebra

lemma chart_functionField_tower {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    letI := functionFieldAlgebra π
    letI := chartAlgebra π U
    IsScalarTower K Γ(X, U) X.functionField := by
  letI := functionFieldAlgebra π
  letI := chartAlgebra π U
  apply IsScalarTower.of_algebraMap_eq'
  symm
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp) ≫
    X.germToFunctionField U).hom =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom
  have h : π.appLE ⊤ U (by simp) ≫ X.germToFunctionField U =
      π.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    simp only [Scheme.Hom.appLE, Scheme.germToFunctionField, Category.assoc,
      X.presheaf.germ_res]
    rfl
  exact congrArg CommRingCat.Hom.hom
    (congrArg (fun q => (Scheme.ΓSpecIso (.of K)).inv ≫ q) h)

lemma chart_finiteType {K : Type u} [Field K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := chartAlgebra π U
    Algebra.FiniteType K Γ(X, U) := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)

lemma functionField_essFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    Algebra.EssFiniteType K X.functionField := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hx⟩⟩
  letI := chartAlgebra π U
  letI := chart_functionField_tower π U
  letI := chart_finiteType π U hU
  letI := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp K Γ(X, U) X.functionField

/-- A finite separating transcendence basis of the actual function field. -/
theorem exists_separating_function_field_parameters
    (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    ∃ s : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
  letI := functionFieldAlgebra π
  letI := functionField_essFiniteType π
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K X.functionField
  have hr : Set.range ((↑) : s → X.functionField) = (s : Set X.functionField) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField := by
    have h := hs.isAlgebraic_field
    rw [hr] at h
    exact h
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin K (s : Set X.functionField)) X.functionField :=
    Algebra.EssFiniteType.of_comp K _ _
  exact ⟨s, hs, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩

end PhilipponAlterationProjection



open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace PhilipponAlterationProjection

lemma fromSpec_comp_structure {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U) :
    hU.fromSpec ≫ π = Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)) := by
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec π (isAffineOpen_top _) hU (by simp)).symm


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

lemma dimension_eq_card_of_function_field_basis {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] (S : Finset X.functionField)
    (hS : letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
      IsTranscendenceBasis K ((↑) : S → X.functionField)) :
    topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) := by
  letI : Algebra K X.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let L := X.residueField (genericPoint X)
  letI : Algebra K L := residueAlgebra π (genericPoint X)
  letI : Algebra X.functionField L := (X.residue (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower K X.functionField L := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  have hbij : Function.Bijective (X.residue (genericPoint X)) :=
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩
  let e : X.functionField ≃ₐ[K] L :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom K X.functionField L) hbij
  have he : Algebra.trdeg K X.functionField = Algebra.trdeg K L := e.trdeg_eq
  have hd := toENat_trdeg_residueField_eq_topologicalKrullDim_closure π (genericPoint X)
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hdim : topologicalKrullDim X = topologicalKrullDim (closure ({genericPoint X} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  rw [hdim, ← hd]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) = _
  rw [← he, ← hS.cardinalMk_eq_trdeg]
  simp

end PhilipponAlterationProjection



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

/-- A dominant affine map to a projective scheme has a projective graph compactification,
retaining its original affine chart and dimension. -/
theorem exists_integral_projective_compactification_with_map
    (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (S : Scheme.{u}) (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (a : Spec (.of A) ⟶ S) [IsDominant a]
    (ha : a ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (G : Scheme.{u}) (q : G ⟶ S) (t : Spec (.of A) ⟶ G),
      IsIntegral G ∧ IsProper q ∧ Surjective q ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ q = a ∧
      topologicalKrullDim G = topologicalKrullDim (Spec (.of A)) ∧
      ∃ (d : ℕ) (j : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π k d = q ≫ π := by
  obtain ⟨n, j, hj, hjbase⟩ := exists_affine_immersion k A
  letI := hj
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
  let b : Spec (.of A) ⟶ pullback (ProjSpace.π k n) π :=
    pullback.lift j a (hjbase.trans ha.symm)
  haveI : IsImmersion (b ≫ pullback.fst (ProjSpace.π k n) π) := by
    rw [pullback.lift_fst]
    infer_instance
  haveI : IsImmersion b := IsImmersion.of_comp b (pullback.fst (ProjSpace.π k n) π)
  haveI : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated π
  haveI : QuasiSeparatedSpace (pullback (ProjSpace.π k n) π : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (ProjSpace.π k n) π)
  haveI : QuasiCompact b := inferInstance
  obtain ⟨hG, _, _⟩ := b.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
  letI := hG
  let G := b.image
  let q : G ⟶ S := b.imageι ≫ pullback.snd (ProjSpace.π k n) π
  let t : Spec (.of A) ⟶ G := b.toImage
  have htq : t ≫ q = a := by
    simp only [t, q, ← Category.assoc, Scheme.Hom.toImage_imageι, b, pullback.lift_snd]
  have hsurj : Surjective q := by
    constructor
    have hclosed : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
    have hsub : Set.range a ⊆ Set.range q := by
      rintro x ⟨z, rfl⟩
      refine ⟨t z, ?_⟩
      change (t ≫ q) z = a z
      rw [htq]
    have hall : Set.univ ⊆ Set.range q := by
      rw [← a.denseRange.closure_range]
      exact closure_minimal hsub hclosed
    exact fun x => hall (Set.mem_univ x)
  obtain ⟨d, l, _hd, hl, hlbase⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      (ProjSpace.π k n) π n (𝟙 P) inferInstance (Category.id_comp _) m i inferInstance hi
  letI := hl
  have hdim : topologicalKrullDim G = topologicalKrullDim (Spec (.of A)) :=
    (PhilipponAlterationProjection.dimension_eq_of_open_immersion t (q ≫ π)).symm
  refine ⟨G, q, t, hG, inferInstance, hsurj, inferInstance, inferInstance, htq,
    hdim, d, b.imageι ≫ l, inferInstance, ?_⟩
  simp only [q, Category.assoc, hlbase, pullback.condition]

end PhilipponAffineProjectiveCompactification


/- Finite projective normalization with a retained normal affine chart.
Reuses the accepted source for 7d122c2e-85fc-4c12-80b1-6a0ba09d0dca.
The unrelated separating-parameter theorem is omitted. -/



open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace PhilipponFiniteCocycle
variable {X : Scheme.{u}} {r : ℕ}

/-- A finite chart cocycle, without equating the index and scheme universes. -/
structure UnitCocycle (V : Fin r → X.Opens) where
  u : ∀ i j, Γ(X, V i ⊓ V j)
  refl : ∀ i, u i i = 1
  cocycle : ∀ i j k,
    rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V j) (u i j) *
    rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V j ⊓ V k) (u j k) =
    rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V k) (u i k)

variable {V : Fin r → X.Opens}

def UnitCocycle.lift (c : UnitCocycle V) :
    Scheme.Modules.UnitCocycle (fun i : ULift.{u} (Fin r) => V i.down) where
  u i j := c.u i.down j.down
  refl i := c.refl i.down
  cocycle i j k := c.cocycle i.down j.down k.down

noncomputable abbrev glueOfCocycle (c : UnitCocycle V) : X.Modules :=
  Scheme.Modules.glueOfCocycle c.lift

noncomputable abbrev glueComponent (c : UnitCocycle V) (T : X.Opens) (i : Fin r) :=
  Scheme.Modules.glueComponent c.lift T (ULift.up i)

lemma leij (T : X.Opens) (i j : Fin r) : T ⊓ (V i ⊓ V j) ≤ V i ⊓ V j := inf_le_right

noncomputable abbrev glueMk (c : UnitCocycle V) (T : X.Opens)
    (x : ∀ i, Γ(X, T ⊓ V i))
    (hx : ∀ i j,
      rO (inf_le_inf_left T inf_le_left : T ⊓ (V i ⊓ V j) ≤ T ⊓ V i) (x i) =
      rO (leij T i j) (c.u i j) *
      rO (inf_le_inf_left T inf_le_right : T ⊓ (V i ⊓ V j) ≤ T ⊓ V j) (x j)) :
    Γ(glueOfCocycle c, T) :=
  Scheme.Modules.glueMk c.lift T (fun i => x i.down) (fun i j => hx i.down j.down)

noncomputable abbrev glueFrame (c : UnitCocycle V) (i : Fin r) :=
  Scheme.Modules.glueFrame c.lift (ULift.up i)

lemma glue_ext (c : UnitCocycle V) {T : X.Opens} {p q : Γ(glueOfCocycle c, T)}
    (h : ∀ i, glueComponent c T i p = glueComponent c T i q) : p = q :=
  Scheme.Modules.glue_ext c.lift (fun i => h i.down)

lemma glueComponent_map (c : UnitCocycle V) {T T' : X.Opens} (h : T' ≤ T)
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T' i ((glueOfCocycle c).presheaf.map (homOfLE h).op p) =
      rO (inf_le_inf_right (V i) h) (glueComponent c T i p) := rfl

lemma glueComponent_smul (c : UnitCocycle V) {T : X.Opens} (g : Γ(X, T))
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i (g • p) = rO inf_le_left g * glueComponent c T i p := rfl

lemma glueComponent_glueFrame (c : UnitCocycle V) (i k : Fin r) :
    glueComponent c (V i) k (glueFrame c i) =
      rO (le_of_eq (inf_comm (V i) (V k))) (c.u k i) := rfl

lemma isFrameOn_glueFrame (c : UnitCocycle V) (i : Fin r) :
    Scheme.Modules.IsFrameOn (glueFrame c i) (V i) :=
  Scheme.Modules.isFrameOn_glueFrame c.lift (ULift.up i)

end PhilipponFiniteCocycle


-- Generalizes the accepted FLT chart constructions to arbitrary universes.
-- Original accepted sources and their hashes are archived in the work directory.
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj

set_option autoImplicit false


open CategoryTheory

namespace AlgebraicGeometry

namespace A1ChartFin

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem Proj.exists_basicOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ Proj.basicOpen 𝒜 f ≤ U ∧ ∀ x ∈ S, x ∈ Proj.basicOpen 𝒜 f := by
  classical
  set Z : Set (Proj 𝒜) := (U : Set (Proj 𝒜))ᶜ with hZdef
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  set J : HomogeneousIdeal 𝒜 := ProjectiveSpectrum.vanishingIdeal Z with hJdef
  have hZJ : ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) = Z := by
    rw [hJdef, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hZ.closure_eq
  have havoid : ∀ p ∈ S.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal),
      ¬ (J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ p) := by
    intro p hp hle
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    change (J ⊓ HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal at hle
    rw [HomogeneousIdeal.toIdeal_inf, x.isPrime.inf_le] at hle
    rcases hle with hle | hle
    · have hxZ : x ∈ Z := by
        rw [← hZJ]
        exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x _).mpr hle
      exact hxZ (hS x hxS)
    · exact x.not_irrelevant_le hle
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ :=
    (J ⊓ HomogeneousIdeal.irrelevant 𝒜).exists_homogeneous_pos_mem_forall_notMem inf_le_right
      (S.image fun x : Proj 𝒜 => x.asHomogeneousIdeal)
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
        exact x.isPrime)
      havoid
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := hyU
    rw [← hZJ] at hyZ
    have hfJ : f ∈ J := (inf_le_left : J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ J) hfI
    exact (Proj.mem_basicOpen 𝒜 f y).mp hy ((ProjectiveSpectrum.mem_zeroLocus 𝒜 y _).mp hyZ hfJ)
  · intro x hx
    rw [Proj.mem_basicOpen]
    exact hf _ (Finset.mem_image_of_mem _ hx)

end A1ChartFin

theorem A1ChartFin.isAffineOpen_ι_preimage_of_le {Y : Scheme.{u}} {U V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ U) :
    IsAffineOpen (U.ι ⁻¹ᵁ V) := by
  have himg : IsAffineOpen (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
    exact hV
  haveI : IsAffine (U.ι ''ᵁ U.ι ⁻¹ᵁ V) := himg
  exact IsAffine.of_isIso (U.ι.isoImage (U.ι ⁻¹ᵁ V)).hom

theorem A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsImmersion ι]
    (W : Y.Opens) (hW : W ≤ ι.coborderRange) : IsClosedImmersion (ι ∣_ W) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hsub : (Subtype.val : ↥W → ↥Y) ⁻¹' coborder (Set.range ι) = Set.univ :=
    Set.eq_univ_of_forall fun w => hW w.2
  have hcl : (Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι =
      (Subtype.val : ↥W → ↥Y) ⁻¹' closure (Set.range ι) := by
    conv_lhs => rw [← coborder_inter_closure (s := Set.range ι)]
    rw [Set.preimage_inter, hsub, Set.univ_inter]
  have key : IsClosed ((Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι) := by
    rw [hcl]; exact isClosed_closure.preimage continuous_subtype_val
  rw [morphismRestrict_base]
  erw [Set.range_restrictPreimage]
  exact key

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry in
theorem solution
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsImmersion ι] (S : Finset X) :
    ∃ (d : ℕ) (F : A) (_ : F ∈ 𝒜 d), 0 < d ∧ (∀ x ∈ S, x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧
      IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧ IsClosedImmersion (ι ∣_ Proj.basicOpen 𝒜 F) := by
  classical
  set U := ι.coborderRange with hU
  set g := ι.liftCoborder with hgdef
  have hg : g ≫ U.ι = ι := ι.liftCoborder_ι
  obtain ⟨n, F, hn, hFn, hle, hmem⟩ := A1ChartFin.Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 U (S.image ι.base) (by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hg]
    exact (g.base x).2)
  refine ⟨n, F, hFn, hn, ?_, ?_, ?_⟩
  · intro x hx
    exact hmem _ (Finset.mem_image_of_mem _ hx)
  · have H : IsAffineOpen ((g ≫ U.ι) ⁻¹ᵁ Proj.basicOpen 𝒜 F) :=
      (A1ChartFin.isAffineOpen_ι_preimage_of_le (Proj.isAffineOpen_basicOpen 𝒜 F hFn hn) hle).preimage g
    rwa [hg] at H
  · exact A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange ι _ hle

end S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
end P2MW


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization

theorem solution
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {d : ℕ} (hd : 0 < d) {r : ℕ} (F : Fin r → A) (hF : ∀ i : Fin r, F i ∈ 𝒜 d) :
    ∃ w : ∀ i j : Fin r, Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F i)),
      (∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i))) ∧
      (∀ i : Fin r, w i i = 1) ∧
      (∀ i j k : Fin r,
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i k) =
          (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i j) *
            (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F j))).op (w j k)) ∧
      (∀ i j : Fin r, (Proj 𝒜).basicOpen (w i j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j)) := by
  classical

  have res_res : ∀ {P : Scheme.{u}} {U₁ U₂ U₃ : P.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (x : Γ(P, U₃)),
      P.presheaf.map (homOfLE h₁).op (P.presheaf.map (homOfLE h₂).op x) =
        P.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro P U₁ U₂ U₃ h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have res_inj : ∀ {P : Scheme.{u}} {U₁ U₂ : P.Opens} (e : U₁ = U₂) (x y : Γ(P, U₂)),
      P.presheaf.map (homOfLE e.le).op x = P.presheaf.map (homOfLE e.le).op y → x = y := by
    intro P U₁ U₂ e x y h
    subst e
    have : (homOfLE (le_refl U₁)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [this] using h

  let q : ∀ i j : Fin r, Away 𝒜 (F i) := fun i j =>
    Away.mk 𝒜 (hF i) 1 (F j) (by simpa only [one_smul] using hF j)
  have hV : ∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i)) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (F i) (hF i) hd
  refine ⟨fun i j => Proj.awayToSection 𝒜 (F i) (q i j), hV, ?_, ?_, ?_⟩
  ·
    intro i
    have : q i i = 1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one]
      simp only [q, Away.val_mk]
      rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩
    show Proj.awayToSection 𝒜 (F i) (q i i) = 1
    rw [this, map_one]
  ·
    intro i j k
    have e : Proj.basicOpen 𝒜 (F i * F j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) :=
      Proj.basicOpen_mul 𝒜 (F i) (F j)
    apply res_inj e
    simp only [map_mul, res_res]

    have h1 := congrArg (fun φ => φ.hom (q i k))
      (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h2 := congrArg (fun φ => φ.hom (q i j))
      (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h3 := congrArg (fun φ => φ.hom (q j k))
      (Proj.awayMap_awayToSection 𝒜 (f := F j) (hF i) (x := F i * F j) (mul_comm _ _))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2 h3

    rw [show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_left)).op (Proj.awayToSection 𝒜 (F i) (q i k)) = _ from h1.symm,
      show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_left)).op (Proj.awayToSection 𝒜 (F i) (q i j)) = _ from h2.symm,
      show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_right)).op (Proj.awayToSection 𝒜 (F j) (q j k)) = _ from h3.symm,
      ← map_mul]
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [q, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
    ring
  ·
    intro i j

    have hfrom : (hV i).fromSpec = Spec.map (Proj.awayToSection 𝒜 (F i)) ≫ Proj.awayι 𝒜 (F i) (hF i) hd := by
      rw [← Proj.basicOpenIsoSpec_inv_ι, ← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc]
      congr 1
      rw [← cancel_epi (hV i).isoSpec.hom, Iso.hom_inv_id, IsAffineOpen.isoSpec_hom, ← Category.assoc]
      show 𝟙 _ = Proj.basicOpenToSpec 𝒜 (F i) ≫ _
      rw [← Proj.basicOpenIsoSpec_hom 𝒜 (F i) (hF i) hd, Iso.hom_inv_id]

    have hpre : (hV i).fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 (F j) =
        PrimeSpectrum.basicOpen (Proj.awayToSection 𝒜 (F i) (q i j)) := by
      rw [hfrom, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 (hF i) hd (hF j) hd]
      have hq : Away.isLocalizationElem (hF i) (hF j) = q i j ^ d := by
        apply HomogeneousLocalization.val_injective
        simp only [q, Away.isLocalizationElem, Away.val_mk, HomogeneousLocalization.val_pow, Localization.mk_pow]
        congr 1
        exact Subtype.ext (by simp [← pow_mul, pow_one])
      rw [hq]
      conv_rhs => rw [← PrimeSpectrum.basicOpen_pow _ d hd, ← map_pow]
      ext1
      rfl
    rw [← (hV i).fromSpec_image_basicOpen, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
      IsAffineOpen.opensRange_fromSpec]

end S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
end P2MW


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {X Z : Scheme.{u}} (f : X ⟶ Z) {r : ℕ} (V : Fin r → Z.Opens) (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j) :
    (∀ i : Fin r, f.app (V i) (w i i) = 1) ∧
    (∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i k)) =
        X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i j)) *
          X.presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V j)).op (f.app (V j) (w j k))) ∧
    (∀ i j : Fin r, X.basicOpen (f.app (V i) (w i j)) = f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j) := by

  have nat : ∀ {U U' : Z.Opens} {W : X.Opens} (h : U ≤ U') (h' : W ≤ f ⁻¹ᵁ U') (h'' : W ≤ f ⁻¹ᵁ U)
      (x : Γ(Z, U')),
      X.presheaf.map (homOfLE h').op (f.app U' x) =
        X.presheaf.map (homOfLE h'').op (f.app U (Z.presheaf.map (homOfLE h).op x)) := by
    intro U U' W h h' h'' x
    have e := congrArg (fun φ => (X.presheaf.map (homOfLE h'').op).hom (φ.hom x)) (f.naturality (homOfLE h).op)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e
    have hh : (homOfLE h').op = ((Opens.map f.base).map (homOfLE h).op.unop).op ≫ (homOfLE h'').op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [e]
    change _ = (X.presheaf.map ((Opens.map f.base).map (homOfLE h).op.unop).op ≫
      X.presheaf.map (homOfLE h'').op).hom (f.app U' x)
    rw [← Functor.map_comp, ← hh]
  have hpre : ∀ i j : Fin r, f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ (V i ⊓ V j) := fun i j x hx => hx
  refine ⟨fun i => by rw [hW1, map_one], fun i j k => ?_, fun i j => ?_⟩
  · rw [nat (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (hpre i j) (w i k),
      nat (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (hpre i j) (w i j),
      nat (inf_le_right : V i ⊓ V j ≤ V j) inf_le_right (hpre i j) (w j k), hW2, map_mul, map_mul]
  · rw [← Scheme.preimage_basicOpen, hW3]
    rfl

end S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {Z : Scheme.{u}} {r : ℕ} (V : Fin r → Z.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j)
    (i₀ : Fin r) (g : Γ(Z, V i₀)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : ∀ j : Fin r, Γ(Z, V j), t i₀ = g ∧
      ∀ j m : Fin r,
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (t j) =
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (t m) := by
  classical

  have res_res : ∀ {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : Γ(Z, C)),
      Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op x) =
        Z.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro A B C h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have stepA : ∀ j : Fin r, ∃ (a : Γ(Z, V j)) (n : ℕ),
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op a =
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n *
          Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    letI : Algebra Γ(Z, V j) Γ(Z, V j ⊓ V i₀) :=
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op).hom.toAlgebra
    haveI : IsLocalization.Away (w j i₀) Γ(Z, V j ⊓ V i₀) :=
      (hV j).isLocalization_of_eq_basicOpen (w j i₀) (homOfLE inf_le_left) (hW3 j i₀).symm
    obtain ⟨⟨a, ⟨s, ⟨n, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (w j i₀))
      (Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g)
    refine ⟨a, n, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    rw [← h, mul_comm]
  choose a₀ n₀ ha₀ using stepA

  let a : ∀ j : Fin r, Γ(Z, V j) := Function.update a₀ i₀ g
  let n : Fin r → ℕ := Function.update n₀ i₀ 0
  have ha : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (a j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n j *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simp only [a, n, Function.update_self, pow_zero, one_mul]
    · simp only [a, n, Function.update_of_ne hj]
      exact ha₀ j

  let k₁ : ℕ := Finset.univ.sup n
  have hn : ∀ j, n j ≤ k₁ := fun j => Finset.le_sup (f := n) (Finset.mem_univ j)
  let b : ∀ j : Fin r, Γ(Z, V j) := fun j => a j * w j i₀ ^ (k₁ - n j)
  have hb : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (b j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ k₁ *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    simp only [b, map_mul, map_pow, ha]
    rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (hn j)]
  have hbi₀ : b i₀ = g := by
    simp only [b, a, n, Function.update_self, hW1, one_pow, mul_one]

  have stepB : ∀ j m : Fin r, ∃ e : ℕ,
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀) ^ e *
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
    intro j m
    have hjm : IsAffineOpen (V j ⊓ V m) := by rw [← hW3 j m]; exact (hV j).basicOpen (w j m)

    have hT : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) =
        Z.basicOpen (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)) := by
      rw [Scheme.basicOpen_res, hW3]
    letI : Algebra Γ(Z, V j ⊓ V m) Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      (Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op).hom.toAlgebra
    haveI : IsLocalization.Away (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀))
        Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      hjm.isLocalization_of_eq_basicOpen _ (homOfLE inf_le_left) hT

    have hvan : Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
      have e1 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_right : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V i₀)).op) (hb j)
      have e2 := congrArg (Z.presheaf.map (homOfLE
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V m ⊓ V i₀)).op) (hb m)
      have e3 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op) (hW2 j m i₀)
      simp only [map_sub, map_mul, map_pow, res_res] at e1 e2 e3 ⊢
      rw [e1, e2, e3]
      ring
    obtain ⟨⟨_, ⟨e, rfl⟩⟩, he⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)))
      Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) _).mp hvan
    exact ⟨e, he⟩
  choose e he using stepB

  let E : ℕ := Finset.univ.sup (fun jm : Fin r × Fin r => e jm.1 jm.2)
  have hE : ∀ j m, e j m ≤ E := fun j m =>
    Finset.le_sup (f := fun jm : Fin r × Fin r => e jm.1 jm.2) (Finset.mem_univ (j, m))
  refine ⟨k₁ + E, fun k hk => ⟨fun j => b j * w j i₀ ^ (k - k₁), ?_, ?_⟩⟩
  ·
    simp only [hbi₀, hW1, one_pow, mul_one]
  · intro j m
    obtain ⟨E', hE'⟩ : ∃ E', k = k₁ + (e j m + E') := ⟨k - k₁ - e j m, by have := hE j m; omega⟩
    have hkk : k - k₁ = e j m + E' := by omega
    have c := hW2 j m i₀
    have d := he j m
    simp only [map_mul, map_pow, hkk]
    rw [hE']
    rw [c] at d ⊢
    linear_combination ((Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) *
      Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (w m i₀)) ^ E') * d

end S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace QPC2


theorem isImmersion_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf => by haveI := hi; haveI := hf; infer_instance⟩

theorem surjective_app_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : V = U)
    (hs : Function.Surjective (f.app U)) : Function.Surjective (f.app V) := by
  subst e; exact hs

theorem isClosedImmersion_morphismRestrict_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (hfU : IsAffineOpen (f ⁻¹ᵁ U))
    (hs : Function.Surjective (f.app U)) : IsClosedImmersion (f ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hfU
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
  refine ⟨hfU, ?_⟩
  rw [morphismRestrict_appTop]
  have e : U.ι ''ᵁ ⊤ = U := by simp [Scheme.Hom.image_top_eq_opensRange]
  have h1 : Function.Surjective (f.app (U.ι ''ᵁ ⊤)) := surjective_app_of_eq f U _ e hs
  have h2 : Function.Surjective
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨z, rfl⟩ := h2 y
  obtain ⟨x, rfl⟩ := h1 z
  exact ⟨x, ConcreteCategory.comp_apply _ _ _⟩

theorem isImmersion_of_affine_charts {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type*} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ := by
  haveI := isImmersion_respectsRight_isOpenImmersion
  have hrange : Set.range φ.base ⊆ ((⨆ j, W j : P.Opens) : Set P) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (⨆ j, φ ⁻¹ᵁ W j : Y.Opens) := by rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨j, hj⟩ := hy
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨j, hj⟩
  exact IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) W hrange
    (fun j => by
      haveI := isClosedImmersion_morphismRestrict_of_surjective φ (W j) (hWaff j) (hYaff j) (hsurj j)
      infer_instance)

end QPC2

theorem solution
    {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type v} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ :=
  QPC2.isImmersion_of_affine_charts φ W hWaff hYaff hcov hsurj

end S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GluedPres

variable {Y : Scheme.{u}} {r : ℕ} {V : Fin r → Y.Opens} (c : PhilipponFiniteCocycle.UnitCocycle V)

def Compat (x : ∀ j : Fin r, Γ(Y, V j)) : Prop :=
  ∀ i j, rO (inf_le_left : V i ⊓ V j ≤ V i) (x i) = c.u i j * rO (inf_le_right : V i ⊓ V j ≤ V j) (x j)

noncomputable def sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) :=
  PhilipponFiniteCocycle.glueMk c ⊤ (fun j => rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j)) fun i j => by
    rw [rO_rO, rO_rO]
    have h := congrArg (rO (PhilipponFiniteCocycle.leij ⊤ i j)) (hx i j)
    rw [map_mul, rO_rO, rO_rO] at h
    exact h

theorem glueComponent_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c ⊤ j (sec c x hx) = rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j) := rfl

theorem glueComponent_map_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) {W : Y.Opens} (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c W j ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (sec c x hx)) =
      rO (inf_le_right : W ⊓ V j ≤ V j) (x j) := by
  rw [PhilipponFiniteCocycle.glueComponent_map, glueComponent_sec, rO_rO]

theorem map_sec_eq_glueFrame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (i : Fin r)
    (hxi : ∀ j, rO (inf_le_left : V j ⊓ V i ≤ V j) (x j) = c.u j i) :
    (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (sec c x hx) = PhilipponFiniteCocycle.glueFrame c i := by
  apply PhilipponFiniteCocycle.glue_ext
  intro j
  rw [glueComponent_map_sec, PhilipponFiniteCocycle.glueComponent_glueFrame, ← hxi j, rO_rO]

theorem bijective_smul_of_map_eq_glueFrame (s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤)) (i : Fin r)
    (hs : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s = PhilipponFiniteCocycle.glueFrame c i)
    (W : Y.Opens) (hW : W ≤ V i) :
    Function.Bijective fun g : Γ(Y, W) => g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
  have key : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op (PhilipponFiniteCocycle.glueFrame c i) := by
    rw [← hs]
    change _ = ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op ≫
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op) s
    rw [← Functor.map_comp]; rfl
  rw [key]
  exact PhilipponFiniteCocycle.isFrameOn_glueFrame c i hW hW

theorem subsingleton_sections_bot (M : Y.Modules) : Subsingleton (M.val.obj (op (⊥ : Y.Opens))) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (M.val.presheaf.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover ⟨M.val.presheaf, M.isSheaf⟩ (⊥ : Y.Opens) hbot
  have h0 : (𝟙 (M.val.presheaf.obj (op (⊥ : Y.Opens))) : _ ⟶ _) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) a) h0
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) b) h0
    simp at this
    exact this
  rw [ha, hb]

theorem subsingleton_functions_bot : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (Y.sheaf.val.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover Y.sheaf (⊥ : Y.Opens) hbot
  let e := hT.uniqueUpToIso CommRingCat.punitIsTerminal
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ x : Γ(Y, (⊥ : Y.Opens)), e.inv.hom (e.hom.hom x) = x := fun x => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) x) e.hom_inv_id
    simpa using this
  rw [← h1 a, ← h1 b, Subsingleton.elim (e.hom.hom a) (e.hom.hom b)]

theorem bijective_smul_bot (M : Y.Modules) (s : Γ(M, ⊤)) (W : Y.Opens) (hW : W ≤ ⊥) :
    Function.Bijective fun g : Γ(Y, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(M, W)) := by
  have hW' : W = ⊥ := le_bot_iff.1 hW
  subst hW'
  haveI : Subsingleton (Γ(M, (⊥ : Y.Opens)) : Type _) := subsingleton_sections_bot M
  haveI : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := subsingleton_functions_bot
  exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, Subsingleton.elim _ _⟩⟩

theorem isUnit_of_frames {M : Y.Modules} {W : Y.Opens} (s t : Γ(M, W))
    (hs : Function.Bijective fun g : Γ(Y, W) => g • s) (ht : Function.Bijective fun g : Γ(Y, W) => g • t)
    (f : Γ(Y, W)) (h : s = f • t) : IsUnit f := by
  obtain ⟨f', hf'⟩ := hs.2 t
  have hf'' : f' • s = t := hf'
  have h1 : (f * f') • s = (1 : Γ(Y, W)) • s := by
    rw [one_smul, mul_smul, hf'', ← h]
  exact isUnit_iff_exists_inv.2 ⟨f', hs.1 h1⟩

theorem inf_le_basicOpen_of_frame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (W : Y.Opens)
    (hW : ∀ W' : Y.Opens, W' ≤ W → Function.Bijective fun g : Γ(Y, W') =>
      g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W')))
    (j : Fin r) : W ⊓ V j ≤ Y.basicOpen (x j) := by

  set W' : Y.Opens := W ⊓ V j with hW'
  let s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx)
  let t : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : W' ≤ V j)).op (PhilipponFiniteCocycle.glueFrame c j)
  have hs : Function.Bijective fun g : Γ(Y, W') => g • s := hW W' inf_le_left
  have ht : Function.Bijective fun g : Γ(Y, W') => g • t := PhilipponFiniteCocycle.isFrameOn_glueFrame c j (inf_le_right : W' ≤ V j) inf_le_right
  obtain ⟨f, hf⟩ := ht.2 s
  have hfu : IsUnit f := isUnit_of_frames s t hs ht f hf.symm

  have hcomp : rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = rO (inf_le_left : W' ⊓ V j ≤ W') f := by
    have h1 := congrArg (PhilipponFiniteCocycle.glueComponent c W' j) hf
    rw [PhilipponFiniteCocycle.glueComponent_smul, PhilipponFiniteCocycle.glueComponent_map, PhilipponFiniteCocycle.glueComponent_glueFrame, rO_rO,
      show rO ((inf_le_inf_right (V j) (inf_le_right : W' ≤ V j)).trans (le_of_eq (inf_comm (V j) (V j)))) (c.u j j) = 1 by
        rw [c.refl, map_one], mul_one] at h1
    rw [h1]
    exact (glueComponent_map_sec c x hx j).symm
  have hu : IsUnit (rO (inf_le_right : W' ⊓ V j ≤ V j) (x j)) := by rw [hcomp]; exact hfu.map _
  have hb := Y.basicOpen_of_isUnit hu
  rw [show rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = Y.presheaf.map (homOfLE (inf_le_right : W' ⊓ V j ≤ V j)).op (x j) from rfl,
    Scheme.basicOpen_res] at hb
  calc W ⊓ V j = W' ⊓ V j := by rw [hW', inf_assoc, inf_idem]
    _ = W' ⊓ V j ⊓ Y.basicOpen (x j) := hb.symm
    _ ≤ Y.basicOpen (x j) := inf_le_right

theorem eq_of_smul_sec_eq {x x' : ∀ j : Fin r, Γ(Y, V j)} (hx : Compat c x) (hx' : Compat c x') (i : Fin r)
    (hxi : x i = 1) {D : Y.Opens} (hD : V i ≤ D) (g : Γ(Y, D))
    (h : g • (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x hx) =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x' hx')) :
    rO hD g = x' i := by

  have h2 := congrArg (PhilipponFiniteCocycle.glueComponent c D i) h
  rw [PhilipponFiniteCocycle.glueComponent_smul, glueComponent_map_sec, glueComponent_map_sec, hxi, map_one, mul_one] at h2

  have hinj := (rO_bijective_of_le_le (inf_le_right : D ⊓ V i ≤ V i) (le_inf hD le_rfl)).1
  apply hinj
  rw [rO_rO]
  exact h2

end GluedPres

open GluedPres in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j)
    (k : ℕ) (hk : 0 < k) (c : PhilipponFiniteCocycle.UnitCocycle V)
    (hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k)
    (N : ℕ) (a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j))
    (ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m))
    (e : Fin r → Fin (N + 1)) (he : Function.Injective e) (hae : ∀ i j : Fin r, a (e i) j = w j i ^ k) :
    ∃ 𝔓 : (PhilipponFiniteCocycle.glueOfCocycle c).ProjPresentation πY N,
      (∀ (α : Fin (N + 1)) (j : Fin r), PhilipponFiniteCocycle.glueComponent c ⊤ j (𝔓.σ α) =
        Y.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V j ≤ V j)).op (a α j)) ∧
      ∃ hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)),
        (∀ i : Fin r, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) = V i) ∧
        (∀ (i : Fin r) (α : Fin (N + 1)),
          𝔓.toProj.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
              (V i) (hV i)
            (Proj.awayToSection _ (MvPolynomial.X (e i)) (ProjSpace.ratio B N (e i) α)) = a α i) := by
  classical

  have hx : ∀ α : Fin (N + 1), Compat c (a α) := by
    intro α i j
    show rO _ (a α i) = c.u i j * rO _ (a α j)
    rw [hc]
    exact ha α i j
  let σ : Fin (N + 1) → Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) := fun α => sec c (a α) (hx α)

  have hσe : ∀ i : Fin r,
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (σ (e i)) = PhilipponFiniteCocycle.glueFrame c i := by
    intro i
    refine map_sec_eq_glueFrame c (a (e i)) (hx _) i fun j => ?_
    show rO _ (a (e i) j) = c.u j i
    rw [hae, map_pow, hc]

  let U' : Fin (N + 1) → Y.Opens := fun α => if h : ∃ i, e i = α then V h.choose else ⊥
  have hU'e : ∀ i, U' (e i) = V i := by
    intro i
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [U', dif_pos h]
    rw [he h.choose_spec]
  have hU' : iSup U' = ⊤ := by
    apply top_le_iff.1
    rw [← hcov]
    exact iSup_le fun i => (hU'e i).symm.le.trans (le_iSup U' (e i))
  have hframe : ∀ (α : Fin (N + 1)) (W : Y.Opens), W ≤ U' α →
      Function.Bijective fun g : Γ(Y, W) =>
        g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (σ α) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
    intro α W hW
    by_cases h : ∃ i, e i = α
    · obtain ⟨i, rfl⟩ := h
      rw [hU'e] at hW
      exact bijective_smul_of_map_eq_glueFrame c (σ (e i)) i (hσe i) W hW
    · have hbot : U' α = ⊥ := dif_neg h
      rw [hbot] at hW
      exact bijective_smul_bot _ _ W hW
  obtain ⟨𝔓, h𝔓σ, h𝔓U⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top πY (PhilipponFiniteCocycle.glueOfCocycle c) N σ U' hU' hframe
  have hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) :=
    fun i => (hU'e i).symm.le.trans (h𝔓U (e i))
  refine ⟨𝔓, ?_, hV, ?_, ?_⟩
  ·
    intro α j
    rw [h𝔓σ]
    exact glueComponent_sec c (a α) (hx α) j
  ·
    intro i
    refine le_antisymm ?_ (hV i)
    intro y hy
    have hy' : y ∈ (⊤ : Y.Opens) := trivial
    rw [← hcov] at hy'
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy'
    have hle := inf_le_basicOpen_of_frame c (a (e i)) (hx (e i))
      (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
      (fun W' hW' => by have hf := 𝔓.frame (e i) W' hW'; rw [h𝔓σ] at hf; exact hf) j
    have hyj : y ∈ Y.basicOpen (a (e i) j) := hle ⟨hy, hj⟩
    rw [hae, Y.basicOpen_pow _ hk, hw3] at hyj
    exact hyj.2
  ·
    intro i α
    have hr := 𝔓.app_ratio_smul (e i) α
    rw [h𝔓σ] at hr
    have h1 := eq_of_smul_sec_eq c (hx (e i)) (hx α) i (by rw [hae, hw1, one_pow]) (hV i) _ hr
    exact h1

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace AmpleChartsAux

theorem exists_finset_forall_surjective {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C) (hf : f.FiniteType) :
    ∃ s : Finset C, ∀ (D : Type u) [CommRing D] (ψ : D →+* C) (θ : B →+* D), ψ.comp θ = f →
      (∀ x ∈ s, x ∈ Set.range ψ) → Function.Surjective ψ := by
  letI : Algebra B C := f.toAlgebra
  obtain ⟨s, hs⟩ := hf
  refine ⟨s, fun D _ ψ θ hcomp hsub => ?_⟩
  let S : Subalgebra B C :=
    { carrier := Set.range ψ
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul ψ a b⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add ψ a b⟩
      algebraMap_mem' := fun r => ⟨θ r, by rw [← RingHom.comp_apply, hcomp]; rfl⟩ }
  have hle : Algebra.adjoin B (s : Set C) ≤ S := Algebra.adjoin_le hsub
  intro c
  have hc : c ∈ Algebra.adjoin B (s : Set C) := by rw [hs]; trivial
  exact hle hc

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def φ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U.1) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 (by simp)

lemma fromSpec_comp (U : X.affineOpens) : U.2.fromSpec ≫ f = Spec.map (φ f U) := by
  rw [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)).symm

lemma finiteType_φ [LocallyOfFiniteType f] (U : X.affineOpens) : (φ f U).hom.FiniteType := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  rw [φ, CommRingCat.hom_comp]
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)

lemma SpecMap_awayToSection_comp_awayι {n : ℕ} (i : Fin (n + 1)) :
    Spec.map (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos =
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos).fromSpec := by
  have hU := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos
  haveI : IsAffine (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) := hU
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp, Proj.basicOpenIsoSpec_hom, IsAffineOpen.isoSpec_hom, Proj.basicOpenToSpec]

end AmpleChartsAux

open AmpleChartsAux in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType πY]
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY := by
  classical

  let Va : Fin r → Y.affineOpens := fun i => ⟨V i, hVaff i⟩

  have hgen := fun i => exists_finset_forall_surjective (φ πY (Va i)).hom (finiteType_φ πY (Va i))
  choose s hs using hgen

  let I : Type u := Σ i : Fin r, ↥(s i)
  haveI : Fintype I := inferInstance
  have hC1 := fun x : I => P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution
    V hVaff w hw1 hw2 hw3 x.1 (x.2 : Γ(Y, V x.1))
  choose k₀ hk₀ using hC1
  let k : ℕ := (Finset.univ.sup k₀) + 1
  have hk : 0 < k := Nat.succ_pos _
  have hkx : ∀ x : I, k₀ x ≤ k := fun x => (Finset.le_sup (Finset.mem_univ x)).trans (Nat.le_succ _)
  have ht := fun x : I => hk₀ x k (hkx x)
  choose t ht₁ ht₂ using ht

  let M : ℕ := Fintype.card I
  let eI : I ≃ Fin M := Fintype.equivFin I
  let N : ℕ := r + M
  let a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j) := fun α =>
    if h : α.val < r then (fun j => w j ⟨α.val, h⟩ ^ k)
    else if h' : α.val - r < M then t (eI.symm ⟨α.val - r, h'⟩) else fun _ => 0
  let e : Fin r → Fin (N + 1) := fun i => ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h; exact Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hae : ∀ i j : Fin r, a (e i) j = w j i ^ k := by
    intro i j; simp only [a, e, dif_pos i.isLt]
  have a_ext : ∀ (x : I) (j : Fin r), a ⟨r + (eI x).val, by omega⟩ j = t x j := by
    intro x j
    simp only [a]
    rw [dif_neg (by omega), dif_pos (by simp)]
    congr 1
    have : (⟨r + (eI x).val - r, by omega⟩ : Fin M) = eI x := Fin.ext (by simp)
    rw [this, Equiv.symm_apply_apply]
  have ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m) := by
    intro α j m
    by_cases h : α.val < r
    · simp only [a, dif_pos h, map_pow]
      rw [hw2 j m ⟨α.val, h⟩, mul_pow]
    · by_cases h' : α.val - r < M
      · simp only [a, dif_neg h, dif_pos h']
        exact ht₂ _ j m
      · simp only [a, dif_neg h, dif_neg h', map_zero, mul_zero]

  let c : PhilipponFiniteCocycle.UnitCocycle V :=
    { u := fun i j => rO (inf_le_left : V i ⊓ V j ≤ V i) (w i j) ^ k
      refl := fun i => by simp only [hw1, map_one, one_pow]
      cocycle := fun i j l => by
        simp only [map_pow, rO_rO, ← mul_pow]
        congr 1
        have h := congrArg (rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V i ⊓ V j ⊓ V l ≤ V i ⊓ V j)) (hw2 i j l)
        rw [map_mul, rO_rO, rO_rO, rO_rO] at h
        exact h.symm }
  have hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k :=
    fun _ _ => rfl

  obtain ⟨𝔓, -, hVle, hpre, happ⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution
      B Y πY r V hVaff hcov w hw1 hw3 k hk c hc N a ha e he hae

  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B
  let W : Fin r → (Proj 𝒜).Opens := fun i => Proj.basicOpen 𝒜 (MvPolynomial.X (e i))
  have hWaff : ∀ i, IsAffineOpen (W i) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos
  have hYaff : ∀ i, IsAffineOpen (𝔓.toProj ⁻¹ᵁ W i) := fun i => by rw [hpre i]; exact hVaff i
  have hcov' : (⨆ i, 𝔓.toProj ⁻¹ᵁ W i) = ⊤ := by
    have : (fun i => 𝔓.toProj ⁻¹ᵁ W i) = V := funext hpre
    rw [this]; exact hcov
  have hsurj : ∀ i, Function.Surjective (𝔓.toProj.app (W i)) := by
    intro i

    let ψ : HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)) →+* Γ(Y, V i) :=
      (𝔓.toProj.appLE (W i) (V i) (hVle i)).hom.comp (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))).hom

    have hψB : ψ.comp (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) = (φ πY (Va i)).hom := by
      have key : CommRingCat.ofHom (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) ≫
          Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) ≫ 𝔓.toProj.appLE (W i) (V i) (hVle i) = φ πY (Va i) := by
        apply Spec.map_injective
        have h' : ∀ (Z : Scheme.{u}) (g : Proj 𝒜 ⟶ Z),
            Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))) ≫
              Proj.awayι 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos ≫ g = (hWaff i).fromSpec ≫ g :=
          fun Z g => by rw [← Category.assoc, SpecMap_awayToSection_comp_awayι]
        rw [Spec.map_comp, Spec.map_comp, ← fromSpec_comp, ← ProjSpace.awayι_comp_π, Category.assoc, h',
          ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec 𝔓.toProj (hWaff i) (hVaff i) (hVle i), Category.assoc,
          𝔓.toProj_π]
      have := congrArg CommRingCat.Hom.hom key
      simp [CommRingCat.hom_comp, RingHom.comp_assoc] at this
      exact this

    have hgen : ∀ x ∈ s i, x ∈ Set.range ψ := by
      intro x hx
      refine ⟨ProjSpace.ratio B N (e i) ⟨r + (eI ⟨i, ⟨x, hx⟩⟩).val, by omega⟩, ?_⟩
      change (𝔓.toProj.appLE (W i) (V i) (hVle i)) (Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) _) = x
      rw [happ i, a_ext ⟨i, ⟨x, hx⟩⟩ i, ht₁]
    have hψ : Function.Surjective ψ := hs i _ ψ _ hψB hgen

    have h1 : Function.Surjective (𝔓.toProj.appLE (W i) (V i) (hVle i)) := Function.Surjective.of_comp hψ
    have h2 : 𝔓.toProj.appLE (W i) (V i) (hVle i) = 𝔓.toProj.app (W i) ≫ Y.presheaf.map (homOfLE (hVle i)).op := rfl
    rw [h2] at h1
    have hbij := rO_bijective_of_le_le (X := Y) (hVle i) (le_of_eq (hpre i))
    intro y
    obtain ⟨x, hx⟩ := h1 (rO (hVle i) y)
    exact ⟨x, hbij.1 hx⟩
  refine ⟨N, 𝔓.toProj, ?_, 𝔓.toProj_π⟩
  exact P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution
    𝔓.toProj W hWaff hYaff hcov' hsurj

end S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P5FQP

theorem compactSpace_of_isImmersion_proj_of_isNoetherianRing
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {M : Scheme.{u}} {n : ℕ}
    (ι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)) [IsImmersion ι] : CompactSpace M := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (ProjSpace.π 𝒪 n)
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (ProjSpace.π 𝒪 n)
  haveI : IsNoetherian P := {}
  have hc : IsCompact (Set.range ι) := TopologicalSpace.NoetherianSpace.isCompact _
  rw [← Set.image_univ, ← ι.isEmbedding.isCompact_iff] at hc
  exact ⟨hc⟩

theorem exists_fin_cover {X : Scheme.{u}} [CompactSpace X] (O : X → X.Opens) (hO : ∀ x, x ∈ O x) :
    ∃ (r : ℕ) (c : Fin r → X), (⨆ i, O (c i)) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (O x : Set X)) (fun x => (O x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hO x⟩)
  refine ⟨t.card, fun i => (t.equivFin.symm i).1, ?_⟩
  apply top_le_iff.mp
  intro y _
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
  obtain ⟨hxt, hyx⟩ := Set.mem_iUnion.mp hx
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, by simpa using hyx⟩

end P5FQP

namespace P12FQP
open P5FQP

theorem exists_affineCover_cocycle_of_isImmersion_proj
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {M : Scheme.{u}} {n : ℕ}
    (ι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)) [IsImmersion ι] :
    ∃ (r : ℕ) (U : Fin r → M.Opens) (w : ∀ i j : Fin r, Γ(M, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      (∀ i, w i i = 1) ∧
      (∀ i j k : Fin r,
        M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
          M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
            M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k)) ∧
      (∀ i j : Fin r, M.basicOpen (w i j) = U i ⊓ U j) := by
  classical
  haveI : CompactSpace M := compactSpace_of_isImmersion_proj_of_isNoetherianRing ι
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪

  have hA1 : ∀ x : M, ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) 𝒪), F ∈ 𝒜 d ∧ 0 < d ∧
      x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F ∧ IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) := by
    intro x
    obtain ⟨d, F, hFd, hd, hS, haff, -⟩ :=
      P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution 𝒜 ι {x}
    exact ⟨d, F, hFd, hd, hS x (Finset.mem_singleton_self x), haff⟩
  choose d F hFd hd hmem haff using hA1
  obtain ⟨r, c, hcov⟩ := exists_fin_cover (fun x => ι ⁻¹ᵁ Proj.basicOpen 𝒜 (F x)) hmem

  let D : ℕ := ∏ i : Fin r, d (c i)
  have hDpos : 0 < D := Finset.prod_pos fun i _ => hd (c i)
  have hdvd : ∀ i : Fin r, d (c i) ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let e : Fin r → ℕ := fun i => D / d (c i)
  have he : ∀ i, e i * d (c i) = D := fun i => Nat.div_mul_cancel (hdvd i)
  have hepos : ∀ i, 0 < e i := fun i => Nat.div_pos (Nat.le_of_dvd hDpos (hdvd i)) (hd (c i))
  let G : Fin r → MvPolynomial (Fin (n + 1)) 𝒪 := fun i => F (c i) ^ e i
  have hG : ∀ i, G i ∈ 𝒜 D := by
    intro i
    have := SetLike.pow_mem_graded (e i) (hFd (c i))
    rwa [smul_eq_mul, he i] at this
  have hGF : ∀ i, Proj.basicOpen 𝒜 (G i) = Proj.basicOpen 𝒜 (F (c i)) := fun i =>
    Proj.basicOpen_pow 𝒜 _ _ (hepos i)

  obtain ⟨v, -, hv1, hv2, hv3⟩ :=
    P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution 𝒜 hDpos G hG
  obtain ⟨hu1, hu2, hu3⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution ι
      (fun i => Proj.basicOpen 𝒜 (G i)) v hv1 hv2 hv3
  refine ⟨r, fun i => ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i), fun i j => ι.app _ (v i j), ?_, ?_, hu1, hu2, hu3⟩
  · intro i
    show IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i))
    rw [hGF i]
    exact haff (c i)
  · show (⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i)) = ⊤
    rw [show (⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i)) = ⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (F (c i)) from
      iSup_congr fun i => by rw [hGF i]]
    exact hcov

end P12FQP

open P12FQP in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {Z M : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ζ : Z ⟶ M) [IsFinite ζ]
    (hM : ∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM) :
    ∃ (qpn : ℕ) (qpι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = ζ ≫ πM := by
  classical
  obtain ⟨n, ι, hι, hιπ⟩ := hM
  haveI : IsImmersion ι := hι

  obtain ⟨r, U, w, hUaff, hUcov, hw1, hw2, hw3⟩ := P12FQP.exists_affineCover_cocycle_of_isImmersion_proj ι
  obtain ⟨hw1', hw2', hw3'⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution ζ U w hw1 hw2 hw3

  haveI : LocallyOfFiniteType ι := by
    rw [← ι.liftCoborder_ι]; infer_instance
  haveI : LocallyOfFiniteType πM := by
    rw [← hιπ]; infer_instance
  haveI : LocallyOfFiniteType (ζ ≫ πM) := inferInstance

  have hVaff : ∀ i : Fin r, IsAffineOpen (ζ ⁻¹ᵁ U i) := fun i => (hUaff i).preimage ζ
  have hVcov : (⨆ i, ζ ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hUcov, Scheme.Hom.preimage_top]
  exact P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution
    𝒪 Z (ζ ≫ πM) r (fun i => ζ ⁻¹ᵁ U i) hVaff hVcov (fun i j => ζ.app (U i) (w i j)) hw1' hw2' hw3'

end S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing
end P2MW


open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveNormalization

lemma topological_dimension_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [show topologicalKrullDim X = Order.krullDim X from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  simp_rw [Order.krullDim_eq_iSup_coheight, ringKrullDim_stalk_eq_coheight]

lemma topological_dimension_eq_of_surjective_of_stalk_dimension
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Surjective f.base)
    (hd : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) =
      ringKrullDim (X.presheaf.stalk (f y))) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  rw [topological_dimension_eq_iSup_stalk, topological_dimension_eq_iSup_stalk]
  simp_rw [hd]
  exact hf.iSup_comp (fun x : X => ringKrullDim (X.presheaf.stalk x))

lemma exists_closed_embedding_of_finite_over_projective
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (ν : Y ⟶ X) [IsFinite ν]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (m : ℕ)
      (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by
  obtain ⟨m, j, hj, hπ⟩ :=
    P2MW.S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing.solution
      π ν ⟨n, i, inferInstance, hi⟩
  letI := hj
  haveI : IsProper (j ≫ ProjSpace.π K m) := by rw [hπ]; infer_instance
  haveI : IsProper j := IsProper.of_comp j (ProjSpace.π K m)
  exact ⟨m, j, IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range, hπ⟩

end PhilipponProjectiveNormalization


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

namespace PhilipponProjectiveNormalization

/-- An open set lifts through a morphism that is an isomorphism over its image. -/
lemma exists_open_lift_of_isIso_morphismRestrict
    {U G H : Scheme.{u}} (t : U ⟶ G) [IsOpenImmersion t] (ν : H ⟶ G)
    [IsIso (ν ∣_ t.opensRange)] :
    ∃ t' : U ⟶ H, IsOpenImmersion t' ∧ t' ≫ ν = t := by
  let t' : U ⟶ H := t.isoOpensRange.hom ≫ inv (ν ∣_ t.opensRange) ≫
    (ν ⁻¹ᵁ t.opensRange).ι
  refine ⟨t', inferInstance, ?_⟩
  dsimp only [t']
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]

end PhilipponProjectiveNormalization



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveNormalization

/-- Finite projective normalization retaining a specified normal open chart. -/
theorem exists_normal_projective_finite_cover_with_open_lift
    (K : Type u) [Field K] {X U : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (t : U ⟶ X) [IsOpenImmersion t]
    (ht : ∀ u : U, IsIntegrallyClosed (X.presheaf.stalk (t u))) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X) (t' : U ⟶ Y),
      IsIntegral Y ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsFinite ν ∧ Surjective ν ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      IsOpenImmersion t' ∧ t' ≫ ν = t ∧
      (∀ V : X.Opens, (∀ x ∈ V, IsIntegrallyClosed (X.presheaf.stalk x)) →
        IsIso (ν ∣_ V)) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by
  obtain ⟨Y, ν, hY, hnormal, hν, hsurj, hdim, hiso⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral K π
  letI := hY
  letI := hν
  have hnormalRange : ∀ x ∈ t.opensRange, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact ht u
  letI := hiso t.opensRange hnormalRange
  obtain ⟨t', ht', hfac⟩ := exists_open_lift_of_isIso_morphismRestrict t ν
  exact ⟨Y, ν, t', hY, hnormal, hν, ⟨hsurj⟩,
    topological_dimension_eq_of_surjective_of_stalk_dimension ν hsurj hdim,
    ht', hfac, hiso, exists_closed_embedding_of_finite_over_projective K π ν n i hi⟩

end PhilipponProjectiveNormalization



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra


set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponNormalProjectiveCompactification

lemma normal_stalk_spec (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (x : Spec (.of A)) : IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := by
  letI : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
    (StructureSheaf.toStalk A x).hom.toAlgebra
  haveI : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) x.asIdeal := by
    convert! StructureSheaf.IsLocalization.to_stalk A x
  exact isIntegrallyClosed_of_isLocalization ((Spec (.of A)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

/-- Compactification and normalization retain the given normal affine model and its map. -/
theorem exists_normal_projective_compactification_with_map
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra k A] [Algebra.FiniteType k A]
    (S : Scheme.{u}) (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (a : Spec (.of A) ⟶ S) [IsDominant a]
    (ha : a ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (N : Scheme.{u}) (q : N ⟶ S) (t : Spec (.of A) ⟶ N),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper q ∧ Surjective q ∧ IsOpenImmersion t ∧ IsDominant t ∧ t ≫ q = a ∧
      topologicalKrullDim N = topologicalKrullDim (Spec (.of A)) ∧
      ∃ (d : ℕ) (j : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π k d = q ≫ π := by
  obtain ⟨G, p, u, hG, hp, hps, hu, hud, hup, hdG, n, j, hj, hjbase⟩ :=
    PhilipponAffineProjectiveCompactification.exists_integral_projective_compactification_with_map
      k A S π m i hi a ha
  letI := hG
  letI := hp
  letI := hps
  letI := hu
  letI := hj
  have hnormalRange (x : Spec (.of A)) : IsIntegrallyClosed (G.presheaf.stalk (u x)) := by
    letI := normal_stalk_spec A x
    exact IsIntegrallyClosed.of_equiv (asIso (u.stalkMap x)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, ν, t, hN, hnN, hν, hsν, hdν, ht, htν, _hiso, d, l, hl, hlbase⟩ :=
    PhilipponProjectiveNormalization.exists_normal_projective_finite_cover_with_open_lift
      k (p ≫ π) n j hjbase u hnormalRange
  letI := hN
  letI := hν
  letI := hsν
  letI := ht
  let q : N ⟶ S := ν ≫ p
  have htq : t ≫ q = a := by
    dsimp only [q]
    rw [← Category.assoc, htν, hup]
  have htd : IsDominant t := ⟨t.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  refine ⟨N, q, t, hN, hnN, inferInstance, inferInstance, ht, htd, htq,
    hdν.trans hdG, d, l, hl, ?_⟩
  simpa only [q, Category.assoc] using hlbase

end PhilipponNormalProjectiveCompactification



set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponFiniteFieldAffineMap
open PhilipponAlterationProjection

/-- An actual normal affine model of a finite function-field extension carries a dominant
map to the original integral scheme, with exact generic-spectrum compatibility. -/
theorem exists_normal_affine_model_with_generic_map
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    ∀ (E : Type u) [Field E] [Algebra S.functionField E] [Algebra k E]
      [IsScalarTower k S.functionField E] [FiniteDimensional S.functionField E],
    ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧
      IsFractionRing B E ∧
      ∃ a : Spec (.of B) ⟶ S, IsDominant a ∧
        a ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ a =
          Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) ≫
            S.fromSpecStalk (genericPoint S) := by
  classical
  letI := functionFieldAlgebra π
  intro E _ _ _ _ _
  letI := functionField_essFiniteType π
  letI : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k S.functionField E
  obtain ⟨U, hU, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint S ∈ (⊤ : S.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint S, hη⟩⟩
  let R := Γ(S, U)
  letI := chartAlgebra π U
  letI := chart_finiteType π U hU
  letI := chart_functionField_tower π U
  let ι : R →ₐ[k] E := (IsScalarTower.toAlgHom k S.functionField E).comp
    (IsScalarTower.toAlgHom k R S.functionField)
  have hι : Function.Injective ι :=
    (algebraMap S.functionField E).injective.comp (S.germToFunctionField_injective U)
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k R).out
  let T := s.image ι
  obtain ⟨B, hBft, hBn, hBE, hTB⟩ :=
    PhilipponNormalAffineFieldModel.exists_normal_affine_field_model_containing k E T
  letI := hBft
  letI := hBn
  letI := hBE
  have hgen : Algebra.adjoin k (s : Set R) ≤ B.comap ι := by
    apply Algebra.adjoin_le
    intro x hx
    exact hTB (Finset.mem_image_of_mem ι hx)
  have hmem (x : R) : ι x ∈ B := by
    rw [hs] at hgen
    exact hgen (Algebra.mem_top : x ∈ (⊤ : Subalgebra k R))
  let ψ : R →ₐ[k] B := ι.codRestrict B hmem
  have hψ : Function.Injective ψ := (AlgHom.injective_codRestrict ι B hmem).mpr hι
  haveI : IsDominant (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ψ.toRingHom).mpr
    rw [(RingHom.injective_iff_ker_eq_bot ψ.toRingHom).mp hψ]
    exact bot_le
  haveI : IsDominant hU.fromSpec :=
    ⟨hU.fromSpec.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let a := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec
  have ha : a ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    dsimp only [a]
    rw [Category.assoc, fromSpec_comp_structure π U hU, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact ψ.commutes r
  have hring : CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom (algebraMap B E) =
      S.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap S.functionField E) := by
    ext r
    rfl
  have hgeneric : Spec.map (S.germToFunctionField U) ≫ hU.fromSpec =
      S.fromSpecStalk (genericPoint S) := hU.fromSpecStalk_eq_fromSpecStalk hη
  have hcompat : Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) ≫
        S.fromSpecStalk (genericPoint S) := by
    dsimp only [a]
    rw [← Category.assoc, ← Spec.map_comp, hring, Spec.map_comp, Category.assoc, hgeneric]
    rfl
  exact ⟨B, hBft, hBn, hBE, a, inferInstance, ha, hcompat⟩

end PhilipponFiniteFieldAffineMap



set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponFieldModelDimension
open PhilipponAlterationProjection

lemma affine_dimension_eq_fraction_trdeg
    (k A F : Type u) [Field k] [CommRing A] [IsDomain A] [Field F]
    [Algebra k A] [Algebra A F] [Algebra k F] [IsScalarTower k A F]
    [Algebra.FiniteType k A] [IsFractionRing A F] :
    topologicalKrullDim (Spec (.of A)) =
      (Cardinal.toENat (Algebra.trdeg k F) : WithBot ℕ∞) := by
  haveI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr (IsFractionRing.injective A F)
  letI : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have h := trdeg_add_eq k A (A := F)
  rw [trdeg_eq_zero (R := A) (A := F), add_zero] at h
  change topologicalKrullDim (PrimeSpectrum A) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A, h]

lemma dimension_eq_functionField_trdeg
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    letI := functionFieldAlgebra π
    topologicalKrullDim S =
      (Cardinal.toENat (Algebra.trdeg k S.functionField) : WithBot ℕ∞) := by
  letI := functionFieldAlgebra π
  obtain ⟨U, hU, hη, _⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint S ∈ (⊤ : S.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint S, hη⟩⟩
  letI := chartAlgebra π U
  letI := chart_finiteType π U hU
  letI := chart_functionField_tower π U
  letI := functionField_isFractionRing_of_isAffineOpen S U hU
  have hdim := PhilipponAlterationProjection.dimension_eq_of_open_immersion hU.fromSpec π
  exact hdim.symm.trans (affine_dimension_eq_fraction_trdeg k Γ(S, U) S.functionField)

end PhilipponFieldModelDimension



set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponFiniteFieldProjectiveBase
open PhilipponAlterationProjection

/-- A finite extension of the actual function field of a projective integral variety has
a normal projective model over that variety. A dense normal affine chart retains the
given field as its fraction field, and the generic-spectrum diagram commutes exactly. -/
theorem exists_normal_projective_base_of_finite_functionField_extension
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π) :
    letI := functionFieldAlgebra π
    ∀ (E : Type u) [Field E] [Algebra S.functionField E] [Algebra k E]
      [IsScalarTower k S.functionField E] [FiniteDimensional S.functionField E],
    ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧
      IsFractionRing B E ∧
      ∃ (N : Scheme.{u}) (q : N ⟶ S) (t : Spec (.of B) ⟶ N),
        IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        IsProper q ∧ Surjective q ∧ IsOpenImmersion t ∧ IsDominant t ∧
        topologicalKrullDim N = topologicalKrullDim S ∧
        t ≫ (q ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ q =
          Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) ≫
            S.fromSpecStalk (genericPoint S) ∧
        ∃ (d : ℕ) (j : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π k d = q ≫ π := by
  letI := functionFieldAlgebra π
  intro E _ _ _ _ _
  obtain ⟨B, hBft, hBn, hBE, a, ha, habase, hageneric⟩ :=
    PhilipponFiniteFieldAffineMap.exists_normal_affine_model_with_generic_map k π E
  letI := hBft
  letI := hBn
  letI := hBE
  letI := ha
  obtain ⟨N, q, t, hN, hnN, hq, hsq, ht, htd, htq, hdN, d, j, hj, hjbase⟩ :=
    PhilipponNormalProjectiveCompactification.exists_normal_projective_compactification_with_map
      k B S π m i hi a habase
  have htr := trdeg_add_eq k S.functionField (A := E)
  rw [trdeg_eq_zero (R := S.functionField) (A := E), add_zero] at htr
  have hdim : topologicalKrullDim N = topologicalKrullDim S := by
    calc
      topologicalKrullDim N = topologicalKrullDim (Spec (.of B)) := hdN
      _ = (Cardinal.toENat (Algebra.trdeg k E) : WithBot ℕ∞) :=
        PhilipponFieldModelDimension.affine_dimension_eq_fraction_trdeg k B E
      _ = (Cardinal.toENat (Algebra.trdeg k S.functionField) : WithBot ℕ∞) := by rw [htr]
      _ = topologicalKrullDim S :=
        (PhilipponFieldModelDimension.dimension_eq_functionField_trdeg k π).symm
  have htbase : t ≫ (q ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Category.assoc, htq, habase]
  have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ q =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) ≫
        S.fromSpecStalk (genericPoint S) := by
    rw [htq]
    exact hageneric
  exact ⟨B, hBft, hBn, hBE, N, q, t, hN, hnN, hq, hsq, ht, htd, hdim,
    htbase, hgeneric, d, j, hj, hjbase⟩

end PhilipponFiniteFieldProjectiveBase



set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponFiniteResidueFieldProjectiveBase
open PhilipponAlterationProjection

/-- The base model can be constructed directly from the generic-point residue field used
by the actual fibre, with its exact generic-spectrum map retained. -/
theorem exists_normal_projective_base_of_finite_genericResidueField_extension
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI := residueAlgebra π η
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E],
    ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧
      IsFractionRing B E ∧
      ∃ (N : Scheme.{u}) (q : N ⟶ S) (t : Spec (.of B) ⟶ N),
        IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        IsProper q ∧ Surjective q ∧ IsOpenImmersion t ∧ IsDominant t ∧
        topologicalKrullDim N = topologicalKrullDim S ∧
        t ≫ (q ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ q =
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
            S.fromSpecResidueField η ∧
        ∃ (d : ℕ) (j : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π k d = q ≫ π := by
  letI := residueAlgebra π η
  intro E _ _ _ _ _
  have hηeq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  let F := S.functionField
  let κ := S.residueField (genericPoint S)
  letI : Algebra k F := functionFieldAlgebra π
  letI : Algebra F κ := (S.residue (genericPoint S)).hom.toAlgebra
  letI : Algebra F E :=
    ((algebraMap κ E).comp (S.residue (genericPoint S)).hom).toAlgebra
  letI : IsScalarTower F κ E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k F E := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [IsScalarTower.algebraMap_apply k κ E r]
    rfl
  letI : FiniteDimensional F κ := Module.Finite.of_surjective
    (Algebra.linearMap F κ) (S.residue_surjective (genericPoint S))
  letI : FiniteDimensional F E := Module.Finite.trans κ E
  obtain ⟨B, hBft, hBn, hBE, N, q, t, hN, hnN, hq, hsq, ht, htd, hdim,
    htbase, hgeneric, d, j, hj, hjbase⟩ :=
    PhilipponFiniteFieldProjectiveBase.exists_normal_projective_base_of_finite_functionField_extension
      k π m i hi E
  have hmaps : Spec.map (CommRingCat.ofHom (algebraMap F E)) =
      Spec.map (CommRingCat.ofHom (algebraMap κ E)) ≫ Spec.map (S.residue (genericPoint S)) := by
    rw [← Spec.map_comp]
    rfl
  have hgenericκ : Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ q =
      Spec.map (CommRingCat.ofHom (algebraMap κ E)) ≫
        S.fromSpecResidueField (genericPoint S) := by
    rw [hgeneric, hmaps, Category.assoc]
    rfl
  exact ⟨B, hBft, hBn, hBE, N, q, t, hN, hnN, hq, hsq, ht, htd, hdim,
    htbase, hgenericκ, d, j, hj, hjbase⟩

end PhilipponFiniteResidueFieldProjectiveBase


theorem solution
    (k : Type u) [Field k] {S : Scheme.{u}} [IsIntegral S]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (η : S) (hη : IsGenericPoint η Set.univ) :
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫
        S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∀ (E : Type u) [Field E] [Algebra (S.residueField η) E] [Algebra k E]
      [IsScalarTower k (S.residueField η) E] [FiniteDimensional (S.residueField η) E],
    ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧
      IsFractionRing B E ∧
      ∃ (N : Scheme.{u}) (q : N ⟶ S) (t : Spec (.of B) ⟶ N),
        IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        IsProper q ∧ Surjective q ∧ IsOpenImmersion t ∧ IsDominant t ∧
        topologicalKrullDim N = topologicalKrullDim S ∧
        t ≫ (q ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ q =
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫
            S.fromSpecResidueField η ∧
        ∃ (d : ℕ) (j : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π k d = q ≫ π := by
  exact PhilipponFiniteResidueFieldProjectiveBase.exists_normal_projective_base_of_finite_genericResidueField_extension k π m i hi η hη
