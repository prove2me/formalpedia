-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_smooth_finite_surjective_cover_of_integral_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T12:55:13.491475+00:00
-- url     : https://prove2.me/submissions/02a397ad-3a78-4fd6-a494-5e15769cfbf2

import Mathlib
import Theorems.Thm_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem
import Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_finite_and_surjective_of_distinct_images_of_finite_cover

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace PhilipponCurveSelection

/-- Two distinct rational points force a smooth proper curve with distinct images.
This is the first step toward a finite smooth cover of a proper integral curve. -/
theorem exists_curve_with_distinct_images
    {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (.of K)) [IsProper y] [IsIntegral Y]
    (p q : Spec (.of K) ⟶ Y) (hp : p ≫ y = 𝟙 _) (hq : q ≫ y = 𝟙 _)
    (hpq : p ≠ q) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (.of K)),
      IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ IsIntegral C ∧
      ∃ (f : C ⟶ Y), f ≫ y = c ∧
        ∃ a b : Spec (.of K) ⟶ C,
          a ≫ c = 𝟙 _ ∧ b ≫ c = 𝟙 _ ∧ a ≫ f ≠ b ≫ f := by
  classical
  by_contra hnone
  have hS : ∀ (C : Scheme.{u}) (c : C ⟶ Spec (.of K)) [IsProper c]
      [SmoothOfRelativeDimension 1 c] [IsIntegral C] (f : C ⟶ Y), f ≫ y = c →
      ∀ a b : Spec (.of K) ⟶ C, a ≫ c = 𝟙 _ → b ≫ c = 𝟙 _ →
        a ≫ f ∈ ({p} : Set (Spec (.of K) ⟶ Y)) → b ≫ f ∈ ({p} : Set _) := by
    intro C c _ _ _ f hf a b ha hb hpa
    have hab : a ≫ f = b ≫ f := by
      by_contra hne
      exact hnone ⟨C, c, inferInstance, inferInstance, inferInstance, f, hf,
        a, b, ha, hb, hne⟩
    rwa [← hab]
  have hqp := AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem
    y {p} p hp (Set.mem_singleton p) hS q hq
  exact hpq (Set.mem_singleton_iff.mp hqp).symm

end PhilipponCurveSelection

namespace PhilipponSmoothFiniteCover

lemma not_subsingleton_smooth_curve
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [SmoothOfRelativeDimension 1 c] :
    ¬ Subsingleton C := by
  intro h
  let := h
  have hx : IsClosed ({genericPoint C} : Set C) := by
    have : ({genericPoint C} : Set C) = Set.univ :=
      Set.eq_univ_iff_forall.mpr (fun x => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))
    rw [this]
    exact isClosed_univ
  have hdim := SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed K c 1
    (genericPoint C) hx
  have hzero : ringKrullDim (C.presheaf.stalk (genericPoint C)) = 0 :=
    ringKrullDim_eq_zero_of_field C.functionField
  exact zero_ne_one (hzero.symm.trans hdim)

lemma exists_two_sections
    {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (.of K)) [LocallyOfFiniteType y] [Nonempty Y]
    (hY : ¬ Subsingleton Y) :
    ∃ p q : Spec (.of K) ⟶ Y, p ≫ y = 𝟙 _ ∧ q ≫ y = 𝟙 _ ∧ p ≠ q := by
  classical
  have hd := AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed y
  obtain ⟨x, p, hp, hpx⟩ := hd.nonempty
  by_contra hnone
  have hsame : ∀ q : Spec (.of K) ⟶ Y, q ≫ y = 𝟙 _ → q = p := by
    intro q hq
    by_contra hne
    exact hnone ⟨p, q, hp, hq, Ne.symm hne⟩
  have hsub : {z : Y | ∃ q : Spec (.of K) ⟶ Y,
      q ≫ y = 𝟙 _ ∧ q (IsLocalRing.closedPoint K) = z} ⊆ {x} := by
    rintro z ⟨q, hq, hqz⟩
    rw [hsame q hq] at hqz
    exact Set.mem_singleton_iff.mpr (hqz.symm.trans hpx)
  let : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id y p hp
  have hrange : Set.range p = ({x} : Set Y) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Set.mem_singleton_iff.mpr
        ((congrArg p (Subsingleton.elim a (IsLocalRing.closedPoint K))).trans hpx)
    · intro hz
      exact ⟨IsLocalRing.closedPoint K, hpx.trans (Set.mem_singleton_iff.mp hz).symm⟩
  have hx : IsClosed ({x} : Set Y) := by
    rw [← hrange]
    exact p.isClosedEmbedding.isClosed_range
  have hfull : Set.univ ⊆ ({x} : Set Y) := by
    rw [← hd.closure_eq]
    exact closure_minimal hsub hx
  apply hY
  exact ⟨fun a b => (Set.mem_singleton_iff.mp (hfull (Set.mem_univ a))).trans
    (Set.mem_singleton_iff.mp (hfull (Set.mem_univ b))).symm⟩

end PhilipponSmoothFiniteCover

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {C W : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (g : W ⟶ C)
    [IsIntegral W] [IsFinite g] [Surjective g] :
    ∃ (D : Scheme.{u}) (ν : D ⟶ W),
      IsIntegral D ∧ IsFinite ν ∧ Surjective ν ∧
        SmoothOfRelativeDimension 1 ((ν ≫ g) ≫ c) := by
  let w := g ≫ c
  have hW : ¬ Subsingleton W := by
    intro h
    let := h
    apply PhilipponSmoothFiniteCover.not_subsingleton_smooth_curve c
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := g.surjective x
    obtain ⟨b, rfl⟩ := g.surjective y
    exact congrArg g (Subsingleton.elim a b)
  obtain ⟨p, q, hp, hq, hpq⟩ := PhilipponSmoothFiniteCover.exists_two_sections w hW
  obtain ⟨D, d, hproper, hsmooth, hD, f, hf, a, b, ha, hb, hne⟩ :=
    PhilipponCurveSelection.exists_curve_with_distinct_images w p q hp hq hpq
  let := hD
  let := hproper
  let := hsmooth
  obtain ⟨hfinite, hsurj⟩ :=
    SmoothProperCurve.finite_and_surjective_of_distinct_images_of_finite_cover
      K c g d f hf a b ha hb hne
  refine ⟨D, f, hD, hfinite, hsurj, ?_⟩
  change SmoothOfRelativeDimension 1 (f ≫ w)
  rw [hf]
  exact hsmooth
