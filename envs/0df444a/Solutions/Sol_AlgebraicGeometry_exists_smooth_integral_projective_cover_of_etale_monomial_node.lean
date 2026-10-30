-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_integral_projective_cover_of_etale_monomial_node
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-29T15:30:37.36378+00:00
-- url     : https://prove2.me/submissions/77decfb1-a8c3-4754-9b9a-2cc8b24a0ef7

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_MvPolynomial_CrossingResolution
import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_smooth_integral_projective_cover_of_monomial

universe u

noncomputable section

set_option autoImplicit false
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

end PhilipponEtaleMonomialNodeCover

end

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
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponProjectiveEmbeddingBaseChange

def embedding {X P V S : Scheme.{u}} (q : X ⟶ S) (p : P ⟶ S)
    (j : X ⟶ P) (hj : j ≫ p = q) (g : V ⟶ S) :
    pullback q g ⟶ pullback g p :=
  pullback.lift (pullback.snd q g) (pullback.fst q g ≫ j)
    (by rw [Category.assoc, hj, pullback.condition])

@[reassoc (attr := simp)]
lemma embedding_fst {X P V S : Scheme.{u}} (q : X ⟶ S) (p : P ⟶ S)
    (j : X ⟶ P) (hj : j ≫ p = q) (g : V ⟶ S) :
    embedding q p j hj g ≫ pullback.fst g p = pullback.snd q g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma embedding_snd {X P V S : Scheme.{u}} (q : X ⟶ S) (p : P ⟶ S)
    (j : X ⟶ P) (hj : j ≫ p = q) (g : V ⟶ S) :
    embedding q p j hj g ≫ pullback.snd g p = pullback.fst q g ≫ j :=
  pullback.lift_snd _ _ _

instance embedding_isClosedImmersion {X P V S : Scheme.{u}}
    (q : X ⟶ S) (p : P ⟶ S) (j : X ⟶ P) [IsClosedImmersion j]
    (hj : j ≫ p = q) (g : V ⟶ S) : IsClosedImmersion (embedding q p j hj g) := by
  let a := pullback.map g q g p (𝟙 V) j (𝟙 S) (by simp) (by simp [hj])
  haveI : IsClosedImmersion a :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion (𝟙 V)) (inferInstance : IsClosedImmersion j)
      (by simp) hj.symm
  have heq : embedding q p j hj g = (pullbackSymmetry q g).hom ≫ a := by
    apply pullback.hom_ext <;> simp [embedding, a]
  rw [heq]
  infer_instance

end PhilipponProjectiveEmbeddingBaseChange

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 70000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponEtaleMonomialNodeProjectiveCover

theorem exists_cover
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ)
    (V : Scheme.{u}) [IsIntegral V]
    (g : V ⟶ Spec (.of (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))))
    [Etale g] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ V),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ g ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K)))) ∧
      IsIso (q ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (monomial d (1 : K)))) ∧
      ∃ (N : ℕ) (j : Y ⟶ pullback g
          (ProjSpace.π (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K))) N)),
        IsClosedImmersion j ∧ j ≫ pullback.fst _ _ = q := by
  obtain ⟨Y, q, hY, hp, hs, hm, hi, N, j, hj, hjbase⟩ :=
    MvPolynomial.CrossingQuotient.exists_smooth_integral_projective_cover_of_monomial K σ d
  haveI := hY
  haveI := hp
  haveI := hs
  haveI := hm
  haveI := hi
  haveI := hj
  haveI : IrreducibleSpace
      (PrimeSpectrum (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))) :=
    hs.surj.irreducibleSpace q.continuous
  have hdU := (PrimeSpectrum.basicOpen (U (monomial d (1 : K)))).isOpen.dense
    (PhilipponEtaleMonomialNodeCover.nonempty_basicOpen_U (monomial d (1 : K)))
  have hU : (g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (monomial d (1 : K))) : Set V).Nonempty :=
    (hdU.preimage g.isOpenMap).nonempty
  obtain ⟨hZ, hpZ, hsZ, hmZ, hiZ⟩ :=
    PhilipponEtaleModification.base_change_properties q g
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K))))
      (PrimeSpectrum.basicOpen (U (monomial d (1 : K)))) hU
  let e := PhilipponProjectiveEmbeddingBaseChange.embedding q _ j hjbase g
  refine ⟨pullback q g, pullback.snd q g, hZ, hpZ, hsZ, hmZ, hiZ,
    N, e, inferInstance, ?_⟩
  exact PhilipponProjectiveEmbeddingBaseChange.embedding_fst _ _ _ _ _

end PhilipponEtaleMonomialNodeProjectiveCover

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

theorem solution
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ)
    (V : Scheme.{u}) [IsIntegral V]
    (g : V ⟶ Spec (.of (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))))
    [Etale g] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ V),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ g ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (MvPolynomial σ K)
          (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K)))).comp
            (MvPolynomial.C : K →+* MvPolynomial σ K)))) ∧
      IsIso (q ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (monomial d (1 : K)))) ∧
      ∃ (N : ℕ) (j : Y ⟶ pullback g
          (ProjSpace.π (CrossingQuotient (MvPolynomial σ K) (monomial d (1 : K))) N)),
        IsClosedImmersion j ∧ j ≫ pullback.fst _ _ = q := by
  exact PhilipponEtaleMonomialNodeProjectiveCover.exists_cover K σ d V g
