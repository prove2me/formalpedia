-- Prove2me | solution 1 for AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/65ddef87-259f-5002-acd7-db916787c2a4

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

universe u

namespace SolCH

section Coprod

lemma coprodMap_of {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {X Y X' Y' : Scheme.{u}} (a : X ⟶ X') (b : Y ⟶ Y') (ha : P a) (hb : P b) :
    P (coprod.map a b) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{u, u} X' Y') ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · show P (pullback.snd (coprod.map a b) coprod.inl)
    have hP := (isPullback_inl_inl_coprodMap a b).flip
    rw [← hP.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso _ _).mpr ha
  · show P (pullback.snd (coprod.map a b) coprod.inr)
    have hP := (isPullback_inr_inr_coprodMap a b).flip
    rw [← hP.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso _ _).mpr hb

scoped instance isOpenImmersion_coprodMap {X Y X' Y' : Scheme.{u}} (a : X ⟶ X') (b : Y ⟶ Y')
    [IsOpenImmersion a] [IsOpenImmersion b] : IsOpenImmersion (coprod.map a b) :=
  coprodMap_of (P := @IsOpenImmersion) a b ‹_› ‹_›

scoped instance isProper_coprodMap {X Y X' Y' : Scheme.{u}} (a : X ⟶ X') (b : Y ⟶ Y')
    [IsProper a] [IsProper b] : IsProper (coprod.map a b) :=
  coprodMap_of (P := @IsProper) a b ‹_› ‹_›

scoped instance isProper_coprodDesc {U V X : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X)
    [IsProper a] [IsProper b] : IsProper (coprod.desc a b) := by
  have : coprod.desc a b = coprod.map a b ≫ coprod.desc (𝟙 X) (𝟙 X) := by
    ext <;> simp
  rw [this]
  infer_instance

lemma range_coprodDesc {U V X : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X) :
    Set.range (coprod.desc a b) = Set.range a ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨(w | w), rfl⟩ := (coprodMk U V).surjective w
    · left
      refine ⟨w, ?_⟩
      rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]
    · right
      refine ⟨w, ?_⟩
      rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact ⟨(coprod.inl : U ⟶ U ⨿ V) w, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : V ⟶ U ⨿ V) w, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

end Coprod

section Envelope

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

def HasEnvelope (S : Set X) : Prop :=
  ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Set.range π = S ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f

lemma HasEnvelope.empty : HasEnvelope f ∅ := by
  refine ⟨∅, ∅, Scheme.emptyTo X, 𝟙 _, Scheme.emptyTo _, ?_, ?_, inferInstance, ?_, Subsingleton.elim _ _⟩
  · haveI : IsClosedImmersion (Scheme.emptyTo X) :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Set.range_eq_empty]; exact isClosed_empty)
    infer_instance
  · exact Set.range_eq_empty _
  · haveI : IsClosedImmersion (Scheme.emptyTo (Spec (CommRingCat.of A))) :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Set.range_eq_empty]; exact isClosed_empty)
    infer_instance

variable {f}

lemma HasEnvelope.union {S T : Set X} (hS : HasEnvelope f S) (hT : HasEnvelope f T) :
    HasEnvelope f (S ∪ T) := by
  obtain ⟨X₁, P₁, π₁, j₁, q₁, hπ₁, hr₁, hj₁, hq₁, h₁⟩ := hS
  obtain ⟨X₂, P₂, π₂, j₂, q₂, hπ₂, hr₂, hj₂, hq₂, h₂⟩ := hT
  refine ⟨X₁ ⨿ X₂, P₁ ⨿ P₂, coprod.desc π₁ π₂, coprod.map j₁ j₂, coprod.desc q₁ q₂,
    inferInstance, ?_, inferInstance, inferInstance, ?_⟩
  · rw [range_coprodDesc, hr₁, hr₂]
  · ext
    · simp [h₁, h₂]
    · simp [h₁, h₂]

variable (f)

lemma HasEnvelope.of_isIntegral [IsNoetherianRing A] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] {Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i] :
    HasEnvelope f (Set.range i) := by
  obtain ⟨X', P, π', j, q, hπ', hsurj, hj, hq, hcomm⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral (i ≫ f)
  refine ⟨X', P, π' ≫ i, j, q, inferInstance, ?_, hj, hq, by rw [hcomm, Category.assoc]⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.surj.range_eq, Set.image_univ]

end Envelope

section Reduced

variable {X : Scheme.{u}}

lemma isReduced_subscheme_vanishingIdeal (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  haveI : ∀ U : X.affineOpens, _root_.IsReduced ((Γ(X, (U : X.Opens)) : Type u) ⧸ I.ideal U) :=
      fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    show (I.ideal U).IsRadical
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    show IsReduced (Spec (.of ((Γ(X, (U : X.Opens)) : Type u) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

lemma isIntegral_subscheme_vanishingIdeal (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI := isReduced_subscheme_vanishingIdeal Z
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have h : IsIrreducible ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set X) := by
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Subtype.irreducibleSpace h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Reduced

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

lemma hasEnvelope_of_mem_irreducibleComponents (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    HasEnvelope f Z := by
  let Zc : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  haveI := isIntegral_subscheme_vanishingIdeal Zc hZ.1
  have := HasEnvelope.of_isIntegral f (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    at this

lemma hasEnvelope_biUnion (s : Finset (Set X)) (hs : ↑s ⊆ irreducibleComponents X) :
    HasEnvelope f (⋃ Z ∈ s, Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasEnvelope.empty f
  | insert Z s hZs ih =>
    rw [Finset.set_biUnion_insert]
    rw [Finset.coe_insert] at hs
    exact (hasEnvelope_of_mem_irreducibleComponents f Z (hs (Set.mem_insert _ _))).union
      (ih ((Set.subset_insert _ _).trans hs))

theorem main :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  obtain ⟨X', P, π, j, q, hπ, hr, hj, hq, hc⟩ :=
    hasEnvelope_biUnion f hfin.toFinset (by simp)
  refine ⟨X', P, π, j, q, hπ, ⟨?_⟩, hj, hq, hc⟩
  rw [← Set.range_eq_univ, hr, Set.eq_univ_iff_forall]
  intro x
  simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]
  exact ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

end Main

end SolCH
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  SolCH.main f

end S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated (solution)
