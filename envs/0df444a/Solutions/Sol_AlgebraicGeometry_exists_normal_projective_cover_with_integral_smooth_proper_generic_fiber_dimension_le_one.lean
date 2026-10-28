-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_cover_with_integral_smooth_proper_generic_fiber_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T00:38:55.489658+00:00
-- url     : https://prove2.me/submissions/0bdb9c78-2e44-43da-a0b0-e67c549ff1fb

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_PhilipponMultiplicity_GenericCurveCoverFamily
import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
import Theorems.Thm_AlgebraicGeometry_hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
import Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily

universe u
noncomputable section


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
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponCurveFamilyModel

/-- Complete a relative projective family without carrying the generic-field
presentation through the geometric construction. -/
lemma exists_curve_model_of_relative_projective_family
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
    (pY : Y ⟶ U) [Smooth pY] [IsProper pY]
    (nM : ℕ) (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) A))
    [IsClosedImmersion iM] (tY : Y ⟶ M) [IsOpenImmersion tY]
    (j : U ⟶ Spec (.of A))
    (hpYeq : tY ≫ iM ≫ ProjSpace.π A nM = pY ≫ j)
    (hjbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = u ≫ qN ≫ πS)
    (aY : Y ⟶ X) [IsDominant aY] (hqa : aY ≫ q = pY ≫ u ≫ qN)
    (E : Type u) [Field E] (b : Spec (.of E) ⟶ U) [IsDominant b]
    (C₀ : Scheme.{u}) (eC₀ : C₀ ⟶ Y) (p₀ : C₀ ⟶ Spec (.of E))
    (hpC₀ : IsPullback eC₀ p₀ pY b) (hdC₀ : topologicalKrullDim C₀ ≤ 1) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
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
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (fX ≫ πX)
  have hIGeneric : IsIntegral (fN.fiber (genericPoint N)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant fN
  have hgeneric (ηN : N) (hηN : IsGenericPoint ηN Set.univ) :
      IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
      IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1 := by
    have he : ηN = genericPoint N := hηN.eq (genericPoint_spec N)
    have hi : IsIntegral (fN.fiber ηN) :=
      (congrArg (fun x : N => IsIntegral (fN.fiber x)) he).mpr hIGeneric
    have hs := PhilipponGenericFiberSmoothTransport.smooth_genericFiber_of_isPullback
      tW (W.ι ≫ p₁) fN u₁ hpull ηN hηN
    have hp : IsProper (fN.fiberToSpecResidueField ηN) :=
      MorphismProperty.pullback_snd fN (N.fromSpecResidueField ηN) inferInstance
    exact ⟨hi, hs, hp, hgenericDim ηN hηN⟩

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
    inferInstance, hW, hsmW, hprW, hsurW, habsW, hG, hnG, hfX, hsfX, hfN, hsfN,
    htW, hdtW, hpull, hgeneric, hcomm, hcomp, hdG, ⟨nN, iN, hiN, hbaseN⟩,
    dG, jG, hjG, hjGbase⟩


/-- Globalize the actual finite-base covering-family preparation into a
normal projective model over the same normal projective base, with a
cartesian smooth proper family on a dense smooth base open. -/
theorem exists_curve_model_of_covering_family_data
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) (hqπ : q ≫ πS = πX) (η : S)
    (hP : HasNormalProjectiveBaseSmoothCurveCoverFamily k πS q η) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  letI : Algebra k (S.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ πS.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
  obtain ⟨E, _hE, hrest⟩ := hP
  letI : Algebra k E := ((algebraMap (S.residueField η) E).comp (algebraMap k (S.residueField η))).toAlgebra
  obtain ⟨B, hBft, _hBn, hBE, N, qN, tN, hN, hnN, hqN, hsqN, htN, hdtN, hdN,
    htbase, _hgen, ⟨nN, iN, hiN, hbaseN⟩, a, _ha, nM, M, iM, hiM,
    U, j, hj, _hdj, hu, hdu, Y, Z, pY, pZ, tY, tZ, h,
    hpY, hpZ, _hflatZ, _hprZ, hover, _hprh, _hsurh, hsmY, hprY, hdomY,
    C₀, p₀, a₀, _hsm₀, _hpr₀, hdC₀, _hpra₀, _hsura₀, _hbase₀, _hproj₀,
    b, eC₀, hbu, hpC₀, _hrec⟩ := hrest
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
  haveI : IsOpenImmersion j := hj
  haveI : IsOpenImmersion u := hu
  haveI : IsDominant u := hdu
  haveI : Nonempty U := ⟨b (genericPoint (Spec (.of E)))⟩
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion u
  haveI : Smooth pY := hsmY
  haveI : IsProper pY := hprY
  haveI : IsDominant (h ≫ tZ) := hdomY
  have hYq : (h ≫ tZ) ≫ q = pY ≫ u ≫ qN := by
    calc
      (h ≫ tZ) ≫ q = h ≫ (pZ ≫ u ≫ qN) := by rw [Category.assoc, hpZ.w]
      _ = pY ≫ u ≫ qN := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ u ≫ qN) hover
  haveI : IsOpenImmersion tY := MorphismProperty.of_isPullback hpY.flip (inferInstance : IsOpenImmersion j)
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
  exact exists_curve_model_of_relative_projective_family k A πS πX mX iX hiX q hqπ
    qN hnN hdN nN iN hbaseN u pY nM iM tY j hpY.w hjbase (h ≫ tZ) hYq E b C₀ eC₀ p₀ hpC₀ hdC₀

end PhilipponCurveFamilyModel


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponCurveFamilyApplication

/-- Apply the accepted finite-generic-field covering data and its global
normal projective completion to the original projective fibration. -/
theorem exists_curve_family_model
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
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  apply PhilipponCurveFamilyModel.exists_curve_model_of_covering_family_data
    k πS πX mX iX hiX q hqπ η
  exact AlgebraicGeometry.hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
    k πS mS iS hiS q η hη hdim

end PhilipponCurveFamilyApplication

theorem solution
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
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) ≤ 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  exact PhilipponCurveFamilyApplication.exists_curve_family_model k πS mS iS hiS πX mX iX hiX q hqπ η hη hdim
