-- Prove2me | solution 1 for AlgebraicGeometry.exists_alteration_with_regular_projective_compactification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-08T05:23:13.651886+00:00
-- url     : https://prove2.me/submissions/e13a8098-8c1e-4c3f-80f5-af713e14bb74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_exists_integral_proper_compactification_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_isProper
import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
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

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π] :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X),
      IsIntegral Z ∧ IsProper a ∧ IsDominant a ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (Y : Scheme.{u}) (πY : Y ⟶ Spec (.of K)),
        IsIntegral Y ∧ IsProper πY ∧
        (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
        ∃ c : Z ⟶ Y, IsOpenImmersion c ∧ IsDominant c ∧ c ≫ πY = a ≫ π ∧
        ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
          IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = πY := by
  obtain ⟨C, πC, hC, hproperC, j, hj, hdj, hjbase⟩ :=
    AlgebraicGeometry.exists_integral_proper_compactification_of_isSeparated K π
  letI := hC
  letI := hproperC
  letI := hj
  letI := hdj
  obtain ⟨Y, f, hY, hproperf, hsurjf, hregular, hfinite, m, i, hi, hibase⟩ :=
    AlgebraicGeometry.exists_regular_projective_alteration_of_isProper K πC
  letI := hY
  letI := hproperf
  letI := hsurjf
  letI := hi
  exact PhilipponAlterationOpenRestriction.exists_of_compactification K π πC j hjbase
    f hfinite (f ≫ πC) rfl hregular m i hibase

#print axioms PhilipponAlterationOpenRestriction.finite_restrict_pullback
#print axioms PhilipponAlterationOpenRestriction.exists_of_compactification
#print axioms solution
