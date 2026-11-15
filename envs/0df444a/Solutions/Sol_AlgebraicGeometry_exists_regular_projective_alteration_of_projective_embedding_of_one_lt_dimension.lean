-- Prove2me | solution 1 for AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding_of_one_lt_dimension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-14T19:01:15.654867+00:00
-- url     : https://prove2.me/submissions/4552dc8d-18c6-4f64-acbb-5f80d8493dff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Theorems.Thm_AlgebraicGeometry_exists_normal_integral_projective_finite_cover
import Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_normal_projective_of_one_lt_dimension

universe u

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
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
end

noncomputable section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

theorem PhilipponProperOpenCompactification.isIso
    {Z Y S : Scheme.{u}} (j : Z ⟶ Y) (π : Y ⟶ S)
    [IsOpenImmersion j] [IsDominant j] [IsSeparated π]
    [IsProper (j ≫ π)] : IsIso j := by
  have : IsProper j := IsProper.of_comp j π
  have : Surjective j := inferInstance
  have : Epi j.base := (TopCat.epi_iff_surjective j.base).mpr j.surjective
  exact IsOpenImmersion.isIso j

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationOpenRestriction

lemma finite_restrict_pullback {Z Y X C : Scheme.{u}}
    (a : Z ⟶ X) (c : Z ⟶ Y) (j : X ⟶ C) (f : Y ⟶ C)
    (H : IsPullback a c j f) (W : C.Opens) [IsFinite (f ∣_ W)] :
    IsFinite (a ∣_ (j ⁻¹ᵁ W)) := by
  have H' := Scheme.Hom.isPullback_resLE H (US := W) (UT := f ⁻¹ᵁ W)
    (UX := j ⁻¹ᵁ W) le_rfl le_rfl (UY := a ⁻¹ᵁ (j ⁻¹ᵁ W)) (by
      rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, inf_idem])
  have hf : IsFinite (f.resLE W (f ⁻¹ᵁ W) le_rfl) := by
    simpa [Scheme.Hom.resLE] using (inferInstance : IsFinite (f ∣_ W))
  have h := MorphismProperty.of_isPullback H'.flip (P := @IsFinite) hf
  simpa [Scheme.Hom.resLE] using h

/-- Restricting one regular projective alteration of an integral proper
compactification gives an alteration with the same regular projective compactification. -/
theorem exists_of_compactification
    (K : Type u) [Field K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (π : X ⟶ Spec (.of K)) (πC : C ⟶ Spec (.of K))
    (j : X ⟶ C) [IsOpenImmersion j] [IsDominant j] (hj : j ≫ πC = π)
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ C) [IsProper f] [IsDominant f]
    (hfinite : ∃ W : C.Opens, Nonempty W ∧ IsFinite (f ∣_ W))
    (πY : Y ⟶ Spec (.of K)) [IsProper πY]
    (hf : f ≫ πC = πY) (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (m : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K m = πY) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ IsDominant a ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of K)),
        IsIntegral Y ∧ IsProper πY ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        ∃ c : Z ⟶ Y, IsOpenImmersion c ∧ IsDominant c ∧ c ≫ πY = a ≫ π ∧
        ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = πY := by
  let Z := pullback j f
  let a : Z ⟶ X := pullback.fst j f
  let c : Z ⟶ Y := pullback.snd j f
  haveI : Surjective f := inferInstance
  haveI : Surjective a := inferInstanceAs (Surjective (pullback.fst j f))
  haveI : Nonempty Z := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨z, -⟩ := a.surjective x
    exact ⟨z⟩
  haveI : IsOpenImmersion c := inferInstanceAs (IsOpenImmersion (pullback.snd j f))
  haveI : IsIntegral Z := isIntegral_of_isOpenImmersion c
  haveI : IsDominant c := ⟨c.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have H : IsPullback a c j f := IsPullback.of_hasPullback j f
  obtain ⟨W, hW, hfin⟩ := hfinite
  letI := hfin
  have hV : Nonempty (j ⁻¹ᵁ W) := by
    obtain ⟨x, hx⟩ := j.denseRange.exists_mem_open W.isOpen (by
      obtain ⟨w⟩ := hW
      exact ⟨w.val, w.property⟩)
    exact ⟨⟨x, hx⟩⟩
  refine ⟨Z, a, inferInstance, inferInstance, inferInstance,
    ⟨j ⁻¹ᵁ W, hV, finite_restrict_pullback a c j f H W⟩,
    Y, πY, inferInstance, inferInstance, hreg, c, inferInstance, inferInstance, ?_,
    m, i, inferInstance, hi⟩
  rw [← hf, ← Category.assoc, ← H.w, Category.assoc, hj]

end PhilipponAlterationOpenRestriction

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponBirationalAlterationComposition

/-- A proper map from an integral scheme with an open section is an
isomorphism over the section's original nonempty open. -/
theorem isIso_restrict_of_open_section {X Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ X) [IsProper p] (U : X.Opens) [Nonempty U]
    (s : U.toScheme ⟶ Y) [IsOpenImmersion s] (hs : s ≫ p = U.ι) :
    IsIso (p ∣_ U) := by
  let L := p ⁻¹ᵁ U
  have hr : Set.range s ⊆ Set.range L.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨s x, ?_⟩, rfl⟩
    change (s ≫ p) x ∈ U
    rw [hs]
    exact x.property
  let t := IsOpenImmersion.lift L.ι s hr
  have ht : t ≫ L.ι = s := IsOpenImmersion.lift_fac ..
  have htp : t ≫ (p ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, ht, hs, Category.id_comp]
  haveI : IsOpenImmersion (t ≫ L.ι) := ht.symm ▸ inferInstance
  haveI : IsOpenImmersion t := IsOpenImmersion.of_comp t L.ι
  haveI : Nonempty L.toScheme := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨t x⟩
  haveI : IsIntegral L.toScheme := isIntegral_of_isOpenImmersion L.ι
  haveI : IsDominant t :=
    ⟨t.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : IsProper (t ≫ (p ∣_ U)) := htp.symm ▸ inferInstance
  haveI : IsIso t := PhilipponProperOpenCompactification.isIso t (p ∣_ U)
  have h : p ∣_ U = inv t := by
    rw [← cancel_epi t, htp, IsIso.hom_inv_id]
  rw [h]
  infer_instance

/-- Finiteness on a local cartesian model descends to its open image. -/
theorem finite_restrict_image {L Z U X : Scheme.{u}}
    (p : L ⟶ U) (i : L ⟶ Z) (j : U ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion j] (H : IsPullback p i j q)
    (W : U.Opens) [IsFinite (p ∣_ W)] :
    IsFinite (q ∣_ (W.ι ≫ j).opensRange) := by
  have h := (isPullback_morphismRestrict p W).paste_vert H
  haveI : IsFinite (pullback.snd q (W.ι ≫ j)) :=
    h.flip.isoPullback_inv_snd ▸
      (inferInstance : IsFinite (h.flip.isoPullback.inv ≫ (p ∣_ W)))
  exact ((MorphismProperty.arrow_mk_iso_iff @IsFinite)
    (morphismRestrictOpensRange q (W.ι ≫ j))).mpr inferInstance

/-- A map finite over a nonempty open remains generically finite after
composition with a map that is an isomorphism over a nonempty open. -/
theorem finite_open_comp {Z Y X : Scheme.{u}} [IsIntegral Y]
    (q : Z ⟶ Y) (p : Y ⟶ X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)]
    (V : Y.Opens) [Nonempty V] [IsFinite (q ∣_ V)] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite ((q ≫ p) ∣_ W) := by
  let L := p ⁻¹ᵁ U
  let b : L.toScheme ⟶ X := L.ι ≫ p
  have hb : b = (p ∣_ U) ≫ U.ι := (morphismRestrict_ι p U).symm
  haveI : IsOpenImmersion b := hb.symm ▸ inferInstance
  have hbr : b.opensRange = U := by
    ext x
    change x ∈ Set.range b ↔ x ∈ U
    rw [hb, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (p ∣_ U).surjective.range_eq, Set.image_univ, Scheme.Opens.range_ι]
    rfl
  haveI : Nonempty L.toScheme := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨inv (p ∣_ U) x⟩
  let W : L.toScheme.Opens := L.ι ⁻¹ᵁ V
  haveI : Nonempty W := by
    have hL : (L : Set Y).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty L.toScheme)
      exact ⟨x.val, x.property⟩
    have hV : (V : Set Y).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty V)
      exact ⟨x.val, x.property⟩
    obtain ⟨y, hyL, hyV⟩ :=
      nonempty_preirreducible_inter L.isOpen V.isOpen hL hV
    exact ⟨⟨⟨y, hyL⟩, hyV⟩⟩
  have H : IsPullback (q ∣_ L) (q ⁻¹ᵁ L).ι b (q ≫ p) := by
    apply IsOpenImmersion.isPullback
    · dsimp only [b]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ p) (morphismRestrict_ι q L).symm
    · rw [hbr, Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage]
  haveI : IsFinite ((q ∣_ L) ∣_ W) :=
    PhilipponAlterationOpenRestriction.finite_restrict_pullback
      (q ∣_ L) (q ⁻¹ᵁ L).ι L.ι q (isPullback_morphismRestrict q L) V
  refine ⟨(W.ι ≫ b).opensRange, ?_,
    finite_restrict_image (q ∣_ L) (q ⁻¹ᵁ L).ι b (q ≫ p) H W⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  exact ⟨⟨(W.ι ≫ b) w, ⟨w, rfl⟩⟩⟩

end PhilipponBirationalAlterationComposition

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponFiniteAlterationComposition

/-- An integral source has only its generic point over the generic point
of an integral target under a dominant locally quasi-finite map. -/
theorem preimage_genericPoint {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsDominant p] [LocallyQuasiFinite p] :
    p ⁻¹' {genericPoint X} = {genericPoint Y} := by
  have hpη := PhilipponGenericDominance.genericPoint_eq_of_dominant p
  ext y
  change p y = genericPoint X ↔ y = genericPoint Y
  constructor
  · intro hy
    exact ((p.isDiscrete_preimage_singleton (genericPoint X)).eq_of_specializes
      (genericPoint_specializes y) hpη hy).symm
  · rintro rfl
    exact hpη

/-- A finite dominant map admits a nonempty target open whose entire
inverse image lies in any prescribed nonempty open of its integral source. -/
theorem exists_open_preimage_le {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ X) [IsFinite p] [IsDominant p]
    (V : Y.Opens) [Nonempty V] :
    ∃ W : X.Opens, Nonempty W ∧ p ⁻¹ᵁ W ≤ V := by
  let W : X.Opens := ⟨(p '' (V : Set Y)ᶜ)ᶜ,
    (p.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))
  have hηW : genericPoint X ∈ W := by
    rintro ⟨y, hy, hpy⟩
    have hyη : y = genericPoint Y := by
      have hy' : y ∈ p ⁻¹' {genericPoint X} := hpy
      rw [preimage_genericPoint p] at hy'
      exact hy'
    exact hy (hyη.symm ▸ hηV)
  refine ⟨W, ⟨⟨genericPoint X, hηW⟩⟩, ?_⟩
  intro y hy
  change p y ∉ p '' (V : Set Y)ᶜ at hy
  by_contra hyV
  exact hy ⟨y, hyV, rfl⟩

/-- Finiteness over an open restricts to every smaller target open. -/
theorem finite_restrict_of_le {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (D V : Y.Opens) (hDV : D ≤ V) [IsFinite (q ∣_ V)] :
    IsFinite (q ∣_ D) := by
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ D
  have h := PhilipponBirationalAlterationComposition.finite_restrict_image
    (q ∣_ V) (q ⁻¹ᵁ V).ι V.ι q (isPullback_morphismRestrict q V) W
  have he : (W.ι ≫ V.ι).opensRange = D := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ D) = D
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hDV]
  exact (congrArg (fun E : Y.Opens => IsFinite (q ∣_ E)) he).mp h

/-- Generic finiteness survives composition with a finite dominant map.
This applies in particular to finite normalization, without first
assuming an isomorphism locus for the normalization map. -/
theorem finite_open_comp {Z Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (q : Z ⟶ Y) (p : Y ⟶ X) [IsFinite p] [IsDominant p]
    (V : Y.Opens) [Nonempty V] [IsFinite (q ∣_ V)] :
    ∃ W : X.Opens, Nonempty W ∧ IsFinite ((q ≫ p) ∣_ W) := by
  obtain ⟨W, hW, hWV⟩ := exists_open_preimage_le p V
  haveI : IsFinite (q ∣_ (p ⁻¹ᵁ W)) := finite_restrict_of_le q _ V hWV
  refine ⟨W, hW, ?_⟩
  rw [morphismRestrict_comp]
  infer_instance

end PhilipponFiniteAlterationComposition

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite normalization reduces the higher-dimensional regular alteration
problem to normal projective targets over the same arbitrary field. The
normal-target construction is an explicit hypothesis; its conclusion
includes generic finiteness, which is proved to survive composition. -/
theorem PhilipponRegularAlterationNormalization.exists_of_normal_case
    (K : Type u) [Field K]
    (H : ∀ {T : Scheme.{u}} [IsIntegral T] (σ : T ⟶ Spec (.of K))
      (m : ℕ) (j : T ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K))
      [IsClosedImmersion j], j ≫ ProjSpace.π K m = σ →
      (∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) →
      1 < topologicalKrullDim T →
      ∃ (Y : Scheme.{u}) (a : Y ⟶ T),
        IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        (∃ V : T.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
        ∃ (r : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)),
          IsClosedImmersion i ∧ i ≫ ProjSpace.π K r = a ≫ σ)
    {X : Scheme.{u}} [IsIntegral X] (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  haveI : IsProper π := by rw [← hι]; infer_instance
  obtain ⟨N, p, hN, hnormal, hfinite, hsurj, hdimN, m, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_normal_integral_projective_finite_cover K π n ι hι
  letI := hN
  letI := hfinite
  letI := hsurj
  letI := hj
  obtain ⟨Y, q, hY, hproperq, hsurjq, hreg, ⟨V, hV, hVfinite⟩,
    r, i, hi, hibase⟩ := H (p ≫ π) m j hjbase hnormal (by rw [hdimN]; exact hdim)
  letI := hproperq
  letI := hsurjq
  letI := hV
  letI := hVfinite
  refine ⟨Y, q ≫ p, hY, inferInstance, inferInstance, hreg,
    PhilipponFiniteAlterationComposition.finite_open_comp q p V,
    r, i, hi, ?_⟩
  simpa only [Category.assoc] using hibase

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  apply PhilipponRegularAlterationNormalization.exists_of_normal_case K ?_ π n ι hι hdim
  intro T hT σ m j hj hjbase hnormal hdimT
  exact AlgebraicGeometry.exists_regular_projective_alteration_of_normal_projective_of_one_lt_dimension
    K σ m j hjbase hnormal hdimT

end

#print axioms PhilipponGenericDominance.genericFiber_inclusion
#print axioms PhilipponGenericDominance.of_recovered_generic_cover
#print axioms PhilipponProperOpenCompactification.isIso
#print axioms PhilipponAlterationOpenRestriction.finite_restrict_pullback
#print axioms PhilipponAlterationOpenRestriction.exists_of_compactification
#print axioms PhilipponBirationalAlterationComposition.isIso_restrict_of_open_section
#print axioms PhilipponBirationalAlterationComposition.finite_restrict_image
#print axioms PhilipponBirationalAlterationComposition.finite_open_comp
#print axioms PhilipponFiniteAlterationComposition.preimage_genericPoint
#print axioms PhilipponFiniteAlterationComposition.exists_open_preimage_le
#print axioms PhilipponFiniteAlterationComposition.finite_restrict_of_le
#print axioms PhilipponFiniteAlterationComposition.finite_open_comp
#print axioms PhilipponRegularAlterationNormalization.exists_of_normal_case
#print axioms solution
