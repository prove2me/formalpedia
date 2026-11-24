-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
-- name    : Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:27.467802+00:00
-- url     : https://prove2.me/theorems/aacd3bc5-af1c-4917-9c67-0203146f5498
-- title:
--   Scheme Coproduct
-- statement:
--   Definitions and structural lemmas for Scheme Coproduct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeCoproduct.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.Blowup
theorem range_coprod_inr_eq_compl (X Y : Scheme.{u}) :
    Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base
      = (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)ᶜ := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr ..
  exact h.compl_eq.symm
theorem isClosed_range_coprod_inl (X Y : Scheme.{u}) :
    IsClosed (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr X Y
  have hopen : IsOpen (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) :=
    (coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
  rw [← isOpen_compl_iff, h.compl_eq]
  exact hopen
theorem isOpen_range_coprod_inl (X Y : Scheme.{u}) :
    IsOpen (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) :=
  (coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
theorem isClosed_range_coprod_inr (X Y : Scheme.{u}) :
    IsClosed (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := by
  rw [range_coprod_inr_eq_compl X Y, isClosed_compl_iff]
  exact isOpen_range_coprod_inl X Y
instance instIsClosedImmersionCoprodInl (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inl X Y⟩
instance instIsClosedImmersionCoprodInr (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inr X Y⟩
theorem isClosedEmbedding_coprod_inl_base (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
  ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩
instance instQuasiCompactCoprodInl (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inl_base X Y).isCompact_preimage hU
theorem isClosedEmbedding_coprod_inr_base (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inr : Y ⟶ X ⨿ Y).base :=
  ⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inr X Y⟩
instance instQuasiCompactCoprodInr (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inr : Y ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inr_base X Y).isCompact_preimage hU
section
variable {ι : Type u} (X : ι → Scheme.{u}) [HasCoproduct X]
theorem sigmaι_base_ne {i j : ι} (hij : i ≠ j) (x : ↥(X i)) (y : ↥(X j)) :
    (Sigma.ι X i).base x ≠ (Sigma.ι X j).base y := by
  intro h
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff X i j x y).mp h))
def iSupOpensRangeSigmaι {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y] : (∐ Y).Opens :=
  ⟨⋃ i, Set.range ⇑(Sigma.ι Y i).base,
    isOpen_iUnion fun i => (Sigma.ι Y i).isOpenEmbedding.isOpen_range⟩
theorem range_sigmaι_subset_iUnion {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (i : κ) : Set.range ⇑(Sigma.ι Y i).base ⊆ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := by
  rw [Scheme.Opens.range_ι]
  intro z hz
  show z ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base
  exact Set.mem_iUnion.mpr ⟨i, hz⟩
theorem surjective_base_of_comp_eq_id {A B : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ A)
    (hgh : g ≫ h = 𝟙 A) : Function.Surjective ⇑h.base := by
  intro x
  refine ⟨g.base x, ?_⟩
  have h1 := congrArg (fun m : A ⟶ A => m.base x) hgh
  simpa using h1
theorem exists_sigmaι_base_eq {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (x : ↥(∐ Y)) : ∃ (i : κ) (y : ↥(Y i)), (Sigma.ι Y i).base y = x := by
  have hid : (Sigma.desc fun i =>
      IsOpenImmersion.lift (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i) (range_sigmaι_subset_iUnion Y i)) ≫
        (iSupOpensRangeSigmaι Y).ι = 𝟙 (∐ Y) := by
    apply Sigma.hom_ext
    intro i
    have hfac := IsOpenImmersion.lift_fac (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i)
      (range_sigmaι_subset_iUnion Y i)
    simp [hfac]
  obtain ⟨w, hw⟩ := surjective_base_of_comp_eq_id _ _ hid x
  have hmem : x ∈ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := ⟨w, hw⟩
  rw [Scheme.Opens.range_ι] at hmem
  have hmem2 : x ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base := hmem
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem2
  exact ⟨i, y, hy⟩
theorem isClosed_range_sigmaι (j : ι) : IsClosed (Set.range ⇑(Sigma.ι X j).base) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  obtain ⟨i, y, rfl⟩ := exists_sigmaι_base_eq X x
  have hij : i ≠ j := by
    intro h
    subst h
    exact hx ⟨y, rfl⟩
  refine ⟨Set.range ⇑(Sigma.ι X i).base, ?_,
    (Sigma.ι X i).isOpenEmbedding.isOpen_range, Set.mem_range_self y⟩
  intro u hu
  obtain ⟨z, rfl⟩ := hu
  rw [Set.mem_compl_iff]
  intro hmem
  obtain ⟨w, hw⟩ := hmem
  exact sigmaι_base_ne X hij z w hw.symm
theorem isClosedImmersion_sigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) := by
  constructor
  exact ⟨(Sigma.ι X j).isOpenEmbedding.toIsEmbedding, isClosed_range_sigmaι X j⟩
instance instIsClosedImmersionSigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) :=
  isClosedImmersion_sigmaι X j
theorem isClosedEmbedding_sigmaι_base {κ : Type u} (Y : κ → Scheme.{u})
    [HasCoproduct Y] (j : κ) (hc : IsClosed (Set.range ⇑(Sigma.ι Y j).base)) :
    Topology.IsClosedEmbedding ⇑(Sigma.ι Y j).base :=
  ⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩
theorem quasiCompact_sigmaι (j : ι) : QuasiCompact (Sigma.ι X j) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_sigmaι_base X j (isClosed_range_sigmaι X j)).isCompact_preimage hU
instance instQuasiCompactSigmaι (j : ι) : QuasiCompact (Sigma.ι X j) :=
  quasiCompact_sigmaι X j
end
end FunctorialResolution.Blowup


