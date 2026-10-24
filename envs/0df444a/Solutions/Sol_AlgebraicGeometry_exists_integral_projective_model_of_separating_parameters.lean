-- Prove2me | solution 1 for AlgebraicGeometry.exists_integral_projective_model_of_separating_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T17:37:39.625984+00:00
-- url     : https://prove2.me/submissions/b4e4931b-1f8b-4a06-b526-351affb85b25

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_exists_dense_affine_separating_function_field_parameters
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

universe u


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



open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection.ProjectiveAffineChart

/-- The standard affine chart, indexed by an arbitrary finite variable type. -/
noncomputable def finiteVariableEmbedding (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] :
    Spec (.of (MvPolynomial ι R)) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card ι + 1)) R) :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.toRingEquiv.toRingHom) ≫
    embedding R (Fintype.card ι)

instance finiteVariableEmbedding_isOpenImmersion (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] : IsOpenImmersion (finiteVariableEmbedding R ι) := by
  haveI : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.bijective
  unfold finiteVariableEmbedding
  infer_instance

lemma finiteVariableEmbedding_over (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] :
    finiteVariableEmbedding R ι ≫ ProjSpace.π R (Fintype.card ι) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R)) := by
  rw [finiteVariableEmbedding, Category.assoc, embedding_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.commutes r

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



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

/-- The integral graph closure of a map on a dense open of a projective variety. -/
theorem exists_integral_projective_graph_closure
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (ρ : Y ⟶ Spec (.of K)) [IsProper ρ]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (m : ℕ)
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π K m = ρ)
    (U : X.Opens) (hU : Dense (U : Set X))
    (a : (U : Scheme) ⟶ Y) (ha : a ≫ ρ = U.ι ≫ π) :
    ∃ (G : Scheme.{u}) (p : G ⟶ X) (q : G ⟶ Y) (s : (U : Scheme) ⟶ G),
      IsIntegral G ∧ IsProper p ∧ Surjective p ∧ IsProper q ∧
      IsOpenImmersion s ∧ IsDominant s ∧
      (∀ u : (U : Scheme), IsIso (p.stalkMap (s u))) ∧
      s ≫ p = U.ι ∧ s ≫ q = a ∧ p ≫ π = q ≫ ρ ∧
      ∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  letI : Nonempty U := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI : IsIntegral (U : Scheme) := inferInstance
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  letI : NoetherianSpace (U : Scheme) := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let b : (U : Scheme) ⟶ pullback π ρ := pullback.lift U.ι a ha.symm
  have hbfst : b ≫ pullback.fst π ρ = U.ι := by simp only [b, pullback.lift_fst]
  haveI : IsImmersion (b ≫ pullback.fst π ρ) := by rw [hbfst]; infer_instance
  haveI : IsImmersion b := IsImmersion.of_comp b (pullback.fst π ρ)
  haveI : QuasiCompact b := inferInstance
  obtain ⟨hG, _, _⟩ := b.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
  letI := hG
  let G := b.image
  let p : G ⟶ X := b.imageι ≫ pullback.fst π ρ
  let q : G ⟶ Y := b.imageι ≫ pullback.snd π ρ
  let s : (U : Scheme) ⟶ G := b.toImage
  have hsp : s ≫ p = U.ι := by
    simp only [s, p, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact hbfst
  have hsq : s ≫ q = a := by
    simp only [s, q, ← Category.assoc, Scheme.Hom.toImage_imageι]
    simp only [b, pullback.lift_snd]
  have hpfield : ∀ u : (U : Scheme), IsIso (p.stalkMap (s u)) := by
    intro u
    have h : IsIso ((s ≫ p).stalkMap u) := by rw [hsp]; infer_instance
    rw [Scheme.Hom.stalkMap_comp] at h
    letI : IsIso (p.stalkMap (s u) ≫ s.stalkMap u) := h
    exact IsIso.of_isIso_comp_right (p.stalkMap (s u)) (s.stalkMap u)
  have hsurj : Surjective p := by
    constructor
    have hc : IsClosed (Set.range p) := p.isClosedMap.isClosed_range
    have hsub : (U : Set X) ⊆ Set.range p := by
      intro x hx
      refine ⟨s ⟨x, hx⟩, ?_⟩
      have h := congrArg (fun f : (U : Scheme) ⟶ X => f ⟨x, hx⟩) hsp
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h
    have hall : Set.univ ⊆ Set.range p := by
      rw [← hU.closure_eq]
      exact closure_minimal hsub hc
    exact fun x => hall (Set.mem_univ x)
  obtain ⟨d, l, _, hl, hlπ⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      π ρ n i inferInstance hi m j inferInstance hj
  letI := hl
  refine ⟨G, p, q, s, hG, inferInstance, hsurj, inferInstance,
    inferInstance, inferInstance, hpfield, hsp, hsq, ?_, d, b.imageι ≫ l, inferInstance, ?_⟩
  · simp only [p, q, Category.assoc, pullback.condition]
  · simp only [p, Category.assoc, hlπ]

end PhilipponAlterationProjection


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

/-- A projective graph model retaining a separating affine projection on a dense open. -/
theorem exists_integral_projective_model_of_separating_parameters
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ S : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : S → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) ∧
      ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
        ∃ hne : Nonempty U, ∃ a : S → Γ(X, U),
          (∀ x : S, @Scheme.germToFunctionField X _ U hne (a x) = x.val) ∧
          ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial S K)),
            f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.eval₂Hom
                ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
            IsDominant f ∧
            f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) = U.ι ≫ π ∧
            ∃ (G : Scheme.{u}) (p : G ⟶ X)
              (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card S + 1)) K))
              (t : (U : Scheme) ⟶ G)
              (e : Spec (.of (MvPolynomial S K)) ⟶
                Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card S + 1)) K)),
              IsIntegral G ∧ topologicalKrullDim G = topologicalKrullDim X ∧
              IsProper p ∧ Surjective p ∧ IsProper q ∧
              IsOpenImmersion t ∧ IsDominant t ∧
              (∀ u : (U : Scheme), IsIso (p.stalkMap (t u))) ∧
              IsOpenImmersion e ∧
              e ≫ ProjSpace.π K (Fintype.card S) =
                Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) ∧
              t ≫ p = U.ι ∧ t ≫ q = f ≫ e ∧
              p ≫ π = q ≫ ProjSpace.π K (Fintype.card S) ∧
              ∃ (d : ℕ)
                (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
                IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  letI : Algebra K X.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  obtain ⟨S, hb, hf, hsep, U, hU, hdense, hne, a, ha, f, hfeq, hdom, hover⟩ :=
    AlgebraicGeometry.exists_dense_affine_separating_function_field_parameters K π
  letI := hne
  let e := ProjectiveAffineChart.finiteVariableEmbedding K S
  let b := f ≫ e
  have hbbase : b ≫ ProjSpace.π K (Fintype.card S) = U.ι ≫ π := by
    dsimp only [b, e]
    rw [Category.assoc, ProjectiveAffineChart.finiteVariableEmbedding_over, hover]
  obtain ⟨G, p, q, t, hG, hp, hsurj, hq, ht, htdom, hpfield, htp, htq, hbase, d, k, hk, hkbase⟩ :=
    exists_integral_projective_graph_closure K π (ProjSpace.π K (Fintype.card S))
      n i hi (Fintype.card S) (𝟙 _) (by simp) U hdense b hbbase
  letI := hG
  letI := hp
  letI := ht
  have hdim : topologicalKrullDim G = topologicalKrullDim X :=
    (dimension_eq_of_open_immersion t (p ≫ π)).symm.trans
      (dimension_eq_of_open_immersion U.ι π)
  have hSdim := dimension_eq_card_of_function_field_basis π S hb
  refine ⟨S, hb, hf, hsep, hSdim, U, hU, hdense, hne, a, ha, f, hfeq, hdom, hover,
    G, p, q, t, e, hG, hdim, hp, hsurj, hq, ht, htdom, hpfield,
    inferInstance, ?_, htp, htq, hbase, d, k, hk, hkbase⟩
  exact ProjectiveAffineChart.finiteVariableEmbedding_over K S

end PhilipponAlterationProjection


theorem solution
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ S : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : S → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) ∧
      ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
        ∃ hne : Nonempty U, ∃ a : S → Γ(X, U),
          (∀ x : S, @Scheme.germToFunctionField X _ U hne (a x) = x.val) ∧
          ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial S K)),
            f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              (MvPolynomial.eval₂Hom
                ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
            IsDominant f ∧
            f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) = U.ι ≫ π ∧
            ∃ (G : Scheme.{u}) (p : G ⟶ X)
              (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card S + 1)) K))
              (t : (U : Scheme) ⟶ G)
              (e : Spec (.of (MvPolynomial S K)) ⟶
                Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card S + 1)) K)),
              IsIntegral G ∧ topologicalKrullDim G = topologicalKrullDim X ∧
              IsProper p ∧ Surjective p ∧ IsProper q ∧
              IsOpenImmersion t ∧ IsDominant t ∧
              (∀ u : (U : Scheme), IsIso (p.stalkMap (t u))) ∧
              IsOpenImmersion e ∧
              e ≫ ProjSpace.π K (Fintype.card S) =
                Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) ∧
              t ≫ p = U.ι ∧ t ≫ q = f ≫ e ∧
              p ≫ π = q ≫ ProjSpace.π K (Fintype.card S) ∧
              ∃ (d : ℕ)
                (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
                IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  exact PhilipponAlterationProjection.exists_integral_projective_model_of_separating_parameters K π n i hi
