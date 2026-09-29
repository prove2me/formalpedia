-- Prove2me | solution 1 for AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dc78a1a1-1a5c-5a5d-b085-0eca45e0e58c

import Mathlib
import Theorems.Thm_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsZariskiLocalAtTarget.restrict Surjective morphismRestrict_comp IsClosedImmersion.of_isPreimmersion IsProper Scheme.Hom.isoOpensRange_inv_comp morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom LocallyQuasiFinite morphismRestrictRestrict IsFinite Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact IsAffine IsZariskiLocalAtTarget LocallyOfFiniteType Spec Spec.map Scheme Spec.map_surjective QuasiCompact.compactSpace_of_compactSpace IsOpenImmersion SpecMapRestrictBasicOpenIso IsClosedImmersion IsSeparated HasRingHomProperty.Spec_iff IsProper.of_comp IsFinite.SpecMap_iff Scheme.Opens morphismRestrictEq nonempty_isColimit_binaryCofanMk_of_isCompl HasRingHomProperty Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply"
p2m_open "AlgebraicGeometry"

theorem isFinite_ι_of_isClosed {X : Scheme.{u}} (W : X.Opens) (hW : IsClosed (W : Set X)) : IsFinite W.ι := by
  haveI : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion W.ι (by rw [Scheme.Opens.range_ι]; exact hW)
  infer_instance

namespace IsFinite p2m_export "AlgebraicGeometry.IsFinite" "of_comp SpecMap_iff" end IsFinite
p2m_open_scoped "AlgebraicGeometry.IsFinite" in

theorem IsFinite.of_forall_isClosed_of_iSup_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (U : Fin n → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hcl : ∀ i, IsClosed ((U i : Set X))) (hfin : ∀ i, IsFinite ((U i).ι ≫ f)) :
    IsFinite f := by
  induction n generalizing X with
  | zero =>
    haveI : IsEmpty X := ⟨fun x => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hU, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, -⟩ := hx
      exact Fin.elim0 i⟩
    infer_instance
  | succ n ih =>

    let V : X.Opens := U 0
    let W : X.Opens := ⟨(V : Set X)ᶜ, (hcl 0).isOpen_compl⟩
    have hWcl : IsClosed (W : Set X) := by
      show IsClosed (V : Set X)ᶜ
      exact (U 0).2.isClosed_compl
    have hVW : IsCompl V.ι.opensRange W.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
      refine IsCompl.of_eq ?_ ?_
      · apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot]
        exact Set.inter_compl_self _
      · apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top]
        exact Set.union_compl_self _
    obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V.ι W.ι hVW

    haveI hV : IsFinite (V.ι ≫ f) := hfin 0
    haveI hW : IsFinite (W.ι ≫ f) := by
      haveI : IsFinite W.ι := isFinite_ι_of_isClosed W hWcl
      refine ih (W.ι ≫ f) (fun i => W.ι ⁻¹ᵁ U i.succ) ?_ ?_ ?_
      ·
        refine top_le_iff.mp fun w _ => ?_
        have hw : W.ι.base w ∈ (⊤ : X.Opens) := trivial
        rw [← hU, TopologicalSpace.Opens.mem_iSup] at hw
        obtain ⟨i, hi⟩ := hw
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exfalso
          have : W.ι.base w ∈ (W : Set X) := by rw [← Scheme.Opens.range_ι W]; exact ⟨w, rfl⟩
          exact this hi
        · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hi⟩
      · intro i
        exact (hcl i.succ).preimage W.ι.continuous
      · intro i
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
        haveI := hfin i.succ
        infer_instance

    let e := hc.coconePointUniqueUpToIso (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u}))
    have hVι : V.ι ≫ e.hom = coprod.inl := by
      have h__af := (hc.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u})) ⟨WalkingPair.left⟩)
      simp at h__af
      exact h__af
    have hWι : W.ι ≫ e.hom = coprod.inr := by
      have h__af := (hc.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (V : Scheme.{u}) (W : Scheme.{u})) ⟨WalkingPair.right⟩)
      simp at h__af
      exact h__af
    have hdesc : e.inv ≫ f = coprod.desc (V.ι ≫ f) (W.ι ≫ f) := by
      apply coprod.hom_ext
      · rw [coprod.inl_desc, ← hVι]; erw [Category.assoc, e.hom_inv_id_assoc]
      · rw [coprod.inr_desc, ← hWι]; erw [Category.assoc, e.hom_inv_id_assoc]
    have h1 : IsFinite (coprod.desc (V.ι ≫ f) (W.ι ≫ f)) := inferInstance
    have h2 : IsFinite (e.hom : X ⟶ (V : Scheme.{u}) ⨿ (W : Scheme.{u})) := inferInstance
    have h3 : IsFinite ((e.hom : X ⟶ (V : Scheme.{u}) ⨿ (W : Scheme.{u})) ≫ coprod.desc (V.ι ≫ f) (W.ι ≫ f)) :=
      MorphismProperty.comp_mem @IsFinite _ _ h2 h1
    rw [← hdesc, e.hom_inv_id_assoc] at h3
    exact h3

end AlgebraicGeometry

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsZariskiLocalAtTarget.restrict Surjective morphismRestrict_comp IsClosedImmersion.of_isPreimmersion IsProper Scheme.Hom.isoOpensRange_inv_comp morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom LocallyQuasiFinite morphismRestrictRestrict IsFinite Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact IsAffine IsZariskiLocalAtTarget LocallyOfFiniteType Spec Spec.map Scheme Spec.map_surjective QuasiCompact.compactSpace_of_compactSpace IsOpenImmersion SpecMapRestrictBasicOpenIso IsClosedImmersion IsSeparated HasRingHomProperty.Spec_iff IsProper.of_comp IsFinite.SpecMap_iff Scheme.Opens morphismRestrictEq nonempty_isColimit_binaryCofanMk_of_isCompl HasRingHomProperty Scheme.Opens.opensRange_ι Scheme.Hom.comp_apply"
namespace GFLocal
p2m_open "AlgebraicGeometry"

theorem exists_isFinite_restrict_chart {R : Type u} [CommRing R] {A : CommRingCat.{u}}
    (φ : CommRingCat.of R ⟶ A) (hft : φ.hom.FiniteType) (hqf : φ.hom.QuasiFinite)
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ ∀ s : R, IsFinite (Spec.map φ ∣_ PrimeSpectrum.basicOpen (r * s)) := by
  let D : R → (Spec (CommRingCat.of R)).Opens := fun t => PrimeSpectrum.basicOpen t
  algebraize [φ.hom]
  obtain ⟨r, hr, hfin⟩ := Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes (A := A) p hp
  refine ⟨r, hr, fun s => ?_⟩

  have h1 : IsFinite (Spec.map φ ∣_ PrimeSpectrum.basicOpen r) := by
    refine (MorphismProperty.arrow_mk_iso_iff @IsFinite (SpecMapRestrictBasicOpenIso φ r)).mpr ?_
    exact (IsFinite.SpecMap_iff _).mpr hfin

  have hle : PrimeSpectrum.basicOpen (r * s) ≤ PrimeSpectrum.basicOpen r := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have h2 := IsZariskiLocalAtTarget.restrict h1 ((D r).ι ⁻¹ᵁ D (r * s))
  have h3 := (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict (Spec.map φ) (D r) ((D r).ι ⁻¹ᵁ D (r * s)))).mp h2
  have heq : (D r).ι ''ᵁ ((D r).ι ⁻¹ᵁ D (r * s)) = D (r * s) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictEq (Spec.map φ) heq)).mp h3

theorem main {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ IsFinite (f ∣_ PrimeSpectrum.basicOpen r) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have hA : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i => by
    show IsAffine (X.affineCover.X _); infer_instance

  let c : ∀ i : 𝒰.I₀, Spec (Γ(𝒰.X i, ⊤)) ⟶ X := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  have hc : ∀ i, IsOpenImmersion (c i) := fun i => inferInstance
  have hchart : ∀ i : 𝒰.I₀, ∃ r : R, r ∉ p ∧ ∀ s : R, IsFinite ((c i ≫ f) ∣_ PrimeSpectrum.basicOpen (r * s)) := by
    intro i
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (c i ≫ f)
    have hft : φ.hom.FiniteType := by
      have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    have hqf : φ.hom.QuasiFinite := by
      have : LocallyQuasiFinite (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    obtain ⟨r, hr, h⟩ := exists_isFinite_restrict_chart φ hft hqf p hp
    exact ⟨r, hr, fun s => by have := h s; rwa [hφ] at this⟩
  choose rr hrr hfinr using hchart
  have hprime : p.IsPrime := hp.1.1
  refine ⟨∏ i, rr i, (hprime.prod_mem_iff.not.mpr (by simpa using hrr)), ?_⟩
  set r := ∏ i, rr i with hr
  set V : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen r

  let h : ∀ i : 𝒰.I₀, ((c i) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ (f ⁻¹ᵁ V).toScheme := fun i => (c i) ∣_ (f ⁻¹ᵁ V)
  have hfin : ∀ i, IsFinite (h i ≫ f ∣_ V) := by
    intro i
    rw [← morphismRestrict_comp]
    have : r = rr i * ∏ j ∈ Finset.univ.erase i, rr j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [show V = PrimeSpectrum.basicOpen (rr i * ∏ j ∈ Finset.univ.erase i, rr j) by rw [← this]]
    exact hfinr i _

  have hclosed : ∀ i, IsClosed (Set.range (h i)) := by
    intro i
    have : IsProper (h i) := IsProper.of_comp (h i) (f ∣_ V)
    exact (h i).isClosedMap.isClosed_range

  let U : 𝒰.I₀ → (f ⁻¹ᵁ V).toScheme.Opens := fun i => (h i).opensRange
  have hcov : ⨆ i, U i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    set j := 𝒰.idx ((f ⁻¹ᵁ V).ι x) with hj
    obtain ⟨y, hy⟩ : ∃ y, 𝒰.f j y = (f ⁻¹ᵁ V).ι x := 𝒰.covers ((f ⁻¹ᵁ V).ι x)
    have hy' : c j ((𝒰.X j).isoSpec.hom y) = (f ⁻¹ᵁ V).ι x := by
      calc c j ((𝒰.X j).isoSpec.hom y) = ((𝒰.X j).isoSpec.hom ≫ c j) y := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (𝒰.f j) y := by simp only [c, Iso.hom_inv_id_assoc]
        _ = (f ⁻¹ᵁ V).ι x := hy
    have hyV : (𝒰.X j).isoSpec.hom y ∈ (c j) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
      show c j _ ∈ f ⁻¹ᵁ V
      rw [hy']; exact x.2
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ⟨⟨_, hyV⟩, ?_⟩⟩
    apply (f ⁻¹ᵁ V).ι.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    simpa using hy'
  have hUfin : ∀ i, IsFinite ((U i).ι ≫ f ∣_ V) := by
    intro i
    rw [← Scheme.Hom.isoOpensRange_inv_comp (h i), Category.assoc]
    infer_instance

  let e := (Fintype.equivFin 𝒰.I₀).symm
  refine IsFinite.of_forall_isClosed_of_iSup_eq_top (f ∣_ V) (U ∘ e) ?_ (fun k => hclosed (e k))
    (fun k => hUfin (e k))
  rw [← hcov]
  exact (Function.Surjective.iSup_comp e.surjective U)

end AlgebraicGeometry.GFLocal

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ IsFinite (f ∣_ PrimeSpectrum.basicOpen r) :=
  AlgebraicGeometry.GFLocal.main f p hp

end S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
end P2MW
export P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes (solution)
