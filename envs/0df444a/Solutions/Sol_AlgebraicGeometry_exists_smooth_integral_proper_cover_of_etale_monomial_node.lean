-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_integral_proper_cover_of_etale_monomial_node
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-29T03:21:49.186737+00:00
-- url     : https://prove2.me/submissions/516307e6-5533-4657-969f-889c89bf9e87

import Definitions.Def_MvPolynomial_CrossingResolution
import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_smooth_integral_proper_cover_of_monomial

universe u

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponModificationBaseChange

/-- An isomorphism over an open subset remains so after arbitrary base change. -/
theorem isIso_restrict_pullback_snd
    {Y X V : Scheme.{u}} (q : Y ⟶ X) (g : V ⟶ X) (U : X.Opens)
    [IsIso (q ∣_ U)] :
    IsIso ((pullback.snd q g) ∣_ (g ⁻¹ᵁ U)) := by
  have : IsIso (pullback.snd q U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict q U]
    infer_instance
  have : IsIso (pullback.snd (pullback.snd q U.ι) (g ∣_ U)) := by
    infer_instance
  have h1 : IsIso (pullback.snd q ((g ∣_ U) ≫ U.ι)) := by
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd q U.ι (g ∣_ U)]
    infer_instance
  rw [morphismRestrict_ι] at h1
  have : IsIso (pullback.snd (pullback.snd q g) (g ⁻¹ᵁ U).ι) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd q g (g ⁻¹ᵁ U).ι]
    infer_instance
  unfold morphismRestrict
  infer_instance

end PhilipponModificationBaseChange

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponEtaleModification

/-- The integral source of a cover remains integral on an integral etale chart
that meets the open set where the cover is an isomorphism. -/
theorem isIntegral_pullback
    {Y X V : Scheme.{u}} (q : Y ⟶ X) (g : V ⟶ X) (U : X.Opens)
    [IsIntegral Y] [IsIntegral V] [Surjective q] [Etale g]
    [IsIso (q ∣_ U)] (hU : (g ⁻¹ᵁ U : Set V).Nonempty) :
    IsIntegral (pullback q g) := by
  obtain ⟨v, hv⟩ := hU
  have hneY : (q ⁻¹ᵁ U : Set Y).Nonempty := by
    obtain ⟨y, hy⟩ := (inferInstance : Surjective q).surj (g v)
    refine ⟨y, ?_⟩
    change q y ∈ U
    rw [hy]
    exact hv
  have hdY : Dense (q ⁻¹ᵁ U : Set Y) := (q ⁻¹ᵁ U).isOpen.dense hneY
  have hdP := hdY.preimage (pullback.fst q g).isOpenMap
  have heq : (pullback.fst q g) ⁻¹ᵁ (q ⁻¹ᵁ U) =
      (pullback.snd q g) ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  change Dense ((pullback.fst q g) ⁻¹ᵁ (q ⁻¹ᵁ U) : Set (pullback q g : Scheme.{u})) at hdP
  rw [heq] at hdP
  haveI : Nonempty (g ⁻¹ᵁ U).toScheme := ⟨⟨v, hv⟩⟩
  haveI : IsIntegral (g ⁻¹ᵁ U).toScheme :=
    isIntegral_of_isOpenImmersion (g ⁻¹ᵁ U).ι
  haveI : IsIso ((pullback.snd q g) ∣_ (g ⁻¹ᵁ U)) :=
    PhilipponModificationBaseChange.isIso_restrict_pullback_snd q g U
  haveI : IsIntegral ((pullback.snd q g) ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme :=
    IsIntegral.of_isIso (inv ((pullback.snd q g) ∣_ (g ⁻¹ᵁ U)))
  haveI : IsReduced (pullback q g) :=
    AlgebraicGeometry.isReduced_of_flat_of_formallyUnramified_of_isIntegral
      (pullback.fst q g)
  haveI : IrreducibleSpace (pullback q g : Scheme.{u}) := by
    apply (irreducibleSpace_def (pullback q g : Scheme.{u})).mpr
    let i := ((pullback.snd q g) ⁻¹ᵁ (g ⁻¹ᵁ U)).ι
    have hd : DenseRange i := by
      simpa only [DenseRange, Scheme.Opens.range_ι, i] using hdP
    have hir : IsIrreducible (Set.range i) := by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ
          ((pullback.snd q g) ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme).image i i.continuous.continuousOn
    change IsIrreducible (Set.univ : Set (pullback q g : Scheme.{u}))
    rw [← hd.closure_range]
    exact hir.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem base_change_properties
    {Y X V S : Scheme.{u}} (q : Y ⟶ X) (g : V ⟶ X) (π : X ⟶ S) (U : X.Opens)
    [IsIntegral Y] [IsIntegral V] [IsProper q] [Surjective q] [Etale g]
    [Smooth (q ≫ π)] [IsIso (q ∣_ U)]
    (hU : (g ⁻¹ᵁ U : Set V).Nonempty) :
    IsIntegral (pullback q g) ∧ IsProper (pullback.snd q g) ∧
      Surjective (pullback.snd q g) ∧
      Smooth (pullback.snd q g ≫ (g ≫ π)) ∧
      IsIso ((pullback.snd q g) ∣_ (g ⁻¹ᵁ U)) := by
  refine ⟨isIntegral_pullback q g U hU, inferInstance, inferInstance, ?_,
    PhilipponModificationBaseChange.isIso_restrict_pullback_snd q g U⟩
  rw [← Category.assoc, ← pullback.condition, Category.assoc]
  infer_instance

end PhilipponEtaleModification

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponEtaleMonomialNodeCover

lemma nonempty_basicOpen_U
    {R : Type u} [CommRing R] [Nontrivial R] (c : R) :
    (PrimeSpectrum.basicOpen (U c) : Set (PrimeSpectrum (CrossingQuotient R c))).Nonempty := by
  let x : PrimeSpectrum R := Classical.choice inferInstance
  let φ := lift c (1 : R) c (by simp)
  refine ⟨PrimeSpectrum.comap φ.toRingHom x, ?_⟩
  change φ (U c) ∉ x.asIdeal
  rw [lift_U]
  exact x.isPrime.one_notMem

theorem exists_cover
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ)
    (V : Scheme.{u}) [IsIntegral V]
    (g : V ⟶ Spec (.of (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))))
    [Etale g] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ V),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ g ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K)))) ∧
      IsIso (q ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (MvPolynomial.monomial d (1 : K)))) := by
  obtain ⟨Y, q, hY, hp, hs, hm, hi⟩ :=
    MvPolynomial.CrossingQuotient.exists_smooth_integral_proper_cover_of_monomial K σ d
  letI := hY
  letI := hp
  letI := hs
  letI := hm
  letI := hi
  haveI : IrreducibleSpace
      (PrimeSpectrum (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))) :=
    hs.surj.irreducibleSpace q.continuous
  have hdU := (PrimeSpectrum.basicOpen (U (MvPolynomial.monomial d (1 : K)))).isOpen.dense
    (nonempty_basicOpen_U (MvPolynomial.monomial d (1 : K)))
  have hU : (g ⁻¹ᵁ PrimeSpectrum.basicOpen
      (U (MvPolynomial.monomial d (1 : K))) : Set V).Nonempty :=
    (hdU.preimage g.isOpenMap).nonempty
  exact ⟨pullback q g, pullback.snd q g,
    PhilipponEtaleModification.base_change_properties q g _ _ hU⟩

end PhilipponEtaleMonomialNodeCover

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

theorem solution
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ)
    (V : Scheme.{u}) [IsIntegral V]
    (g : V ⟶ Spec (.of (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))))
    [Etale g] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ V),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ g ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (MvPolynomial.monomial d 1))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K)))) ∧
      IsIso (q ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (MvPolynomial.monomial d (1 : K)))) := by
  exact PhilipponEtaleMonomialNodeCover.exists_cover K σ d V g
