-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- name    : Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:28.566499+00:00
-- url     : https://prove2.me/theorems/83525cfd-bad9-4946-95cb-60e21c1b19b7
-- title:
--   Blowup Coproduct
-- statement:
--   Definitions and structural lemmas for Blowup Coproduct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_iso_hom_comp
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_of_comap_of_isOpenImmersion_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FunctorialResolution.Blowup
theorem isAffineOpen_image {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    (V : W.Opens) (hV : IsAffineOpen V) : IsAffineOpen (g ''ᵁ V) :=
  hV.image_of_isOpenImmersion g
theorem base_comp_apply {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) (x : U) :
    (f ≫ g).base x = g.base (f.base x) := by simp
theorem range_fst_subset_range_inl {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B)
    (s : PullbackCone (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B)) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inl : A' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy : (PullbackCone.fst s).base t ∈ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
    rw [range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]
    exact hmem
  obtain ⟨b, hb⟩ := hy
  have e1 : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) := by
    have h := congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition
    simpa using h
  have hmapr : ((coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  have e2 : (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b)
      = (coprod.inr : B ⟶ A ⨿ B).base (q.base b) := by
    rw [← base_comp_apply, hmapr, base_comp_apply]
  have key : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.map p q).base ((coprod.inr : B' ⟶ A' ⨿ B').base b) := by rw [hb]
  have hfin : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      = (coprod.inr : B ⟶ A ⨿ B).base (q.base b) := by rw [← e1, key, e2]
  have hmem2 : (coprod.inl : A ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := ⟨q.base b, hfin.symm⟩
  rw [range_coprod_inr_eq_compl A B] at hmem2
  exact hmem2 ⟨(PullbackCone.snd s).base t, rfl⟩
theorem range_fst_subset_range_inr {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B)
    (s : PullbackCone (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B)) :
    Set.range ⇑(PullbackCone.fst s).base ⊆ Set.range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A' B', Set.mem_compl_iff]
  intro hy
  obtain ⟨a, ha⟩ := hy
  have e1 : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t) := by
    have h := congrArg (fun m : s.pt ⟶ A ⨿ B => m.base t) s.condition
    simpa using h
  have hmapl : ((coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  have e2 : (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a)
      = (coprod.inl : A ⟶ A ⨿ B).base (p.base a) := by
    rw [← base_comp_apply, hmapl, base_comp_apply]
  have key : (coprod.map p q).base ((PullbackCone.fst s).base t)
      = (coprod.map p q).base ((coprod.inl : A' ⟶ A' ⨿ B').base a) := by rw [ha]
  have hfin : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      = (coprod.inl : A ⟶ A ⨿ B).base (p.base a) := by rw [← e1, key, e2]
  have hmem2 : (coprod.inr : B ⟶ A ⨿ B).base ((PullbackCone.snd s).base t)
      ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := ⟨(PullbackCone.snd s).base t, rfl⟩
  rw [range_coprod_inr_eq_compl A B, hfin] at hmem2
  exact hmem2 ⟨p.base a, rfl⟩
theorem isPullback_coprod_inl_map {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B) :
    IsPullback (coprod.inl : A' ⟶ A' ⨿ B') p (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B) := by
  have hw : (coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
      (range_fst_subset_range_inl p q s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inl p q s) ≫ p) ≫ (coprod.inl : A ⟶ A ⨿ B)
        = PullbackCone.snd s ≫ (coprod.inl : A ⟶ A ⨿ B) := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inl : A' ⟶ A' ⨿ B')
        = IsOpenImmersion.lift (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
            (range_fst_subset_range_inl p q s) ≫ (coprod.inl : A' ⟶ A' ⨿ B') := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2
theorem isPullback_coprod_inr_map {A B A' B' : Scheme.{u}} (p : A' ⟶ A) (q : B' ⟶ B) :
    IsPullback (coprod.inr : B' ⟶ A' ⨿ B') q (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B) := by
  have hw : (coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
      (range_fst_subset_range_inr p q s)) ?_ ?_ ?_)
  · intro s
    simp [IsOpenImmersion.lift_fac]
  · intro s
    have hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : (IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inr p q s) ≫ q) ≫ (coprod.inr : B ⟶ A ⨿ B)
        = PullbackCone.snd s ≫ (coprod.inr : B ⟶ A ⨿ B) := by
      rw [Category.assoc, ← hw, ← Category.assoc, hl]
      exact s.condition
    exact (cancel_mono _).mp h2
  · intro s m hm _
    have hl : IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
        (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = PullbackCone.fst s := by
      simp [IsOpenImmersion.lift_fac]
    have h2 : m ≫ (coprod.inr : B' ⟶ A' ⨿ B')
        = IsOpenImmersion.lift (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
            (range_fst_subset_range_inr p q s) ≫ (coprod.inr : B' ⟶ A' ⨿ B') := by
      rw [hm, hl]
    exact (cancel_mono _).mp h2
theorem IsBlowupAlongIdealSheaf.coprod {X₁ X₂ X₁' X₂' : Scheme.{u}} {π₁ : X₁' ⟶ X₁} {π₂ : X₂' ⟶ X₂}
    {I : (X₁ ⨿ X₂).IdealSheafData}
    (h₁ : IsBlowupAlongIdealSheaf π₁ (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)))
    (h₂ : IsBlowupAlongIdealSheaf π₂ (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))) :
    IsBlowupAlongIdealSheaf (coprod.map π₁ π₂) I := by
  have hb₁ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))
      (I.comap (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) := by
    have hpb := isPullback_coprod_inl_map π₁ π₂
    have hfac : hpb.isoPullback.symm.hom ≫ π₁
        = pullback.snd (coprod.map π₁ π₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h₁.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hb₂ : IsBlowupAlongIdealSheaf (pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
      (I.comap (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)) := by
    have hpb := isPullback_coprod_inr_map π₁ π₂
    have hfac : hpb.isoPullback.symm.hom ≫ π₂
        = pullback.snd (coprod.map π₁ π₂) (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h₂.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hoi : ∀ b : Bool, IsOpenImmersion
      (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂)
        (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) b) := by
    intro b
    cases b
    · exact (inferInstance : IsOpenImmersion (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))
    · exact (inferInstance : IsOpenImmersion (coprod.inl : X₁ ⟶ X₁ ⨿ X₂))
  refine IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover (coprod.map π₁ π₂) I
    (fun b : Bool => cond b X₁ X₂)
    (Bool.rec (motive := fun b : Bool => (cond b X₁ X₂) ⟶ X₁ ⨿ X₂)
      (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) ?_ ?_
  · intro x
    by_cases hx : x ∈ Set.range ⇑(coprod.inl : X₁ ⟶ X₁ ⨿ X₂).base
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      have hx' : x ∈ Set.range ⇑(coprod.inr : X₂ ⟶ X₁ ⨿ X₂).base := by
        rw [range_coprod_inr_eq_compl X₁ X₂]
        exact hx
      exact hx'
  · intro b
    cases b
    · exact hb₂
    · exact hb₁
end FunctorialResolution.Blowup


