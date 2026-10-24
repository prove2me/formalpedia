-- Prove2me | solution 1 for AlgebraicGeometry.exists_finite_extension_smooth_proper_cover_of_proper_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-24T02:19:53.187839+00:00
-- url     : https://prove2.me/submissions/133301b8-6c20-4ea3-81cc-f0958e70c925

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact

universe u


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

lemma proper_of_isPullback_field
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (f' : X' ⟶ Spec (.of K)) (g : X' ⟶ X)
    (h : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hp : IsProper f') : IsProper f := by
  letI := hp
  letI : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact
  haveI : IsSeparated f := MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K)
      (inferInstance : IsSeparated f')
  haveI : UniversallyClosed f := MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.flip (fpqc_fieldMap k K)
      (inferInstance : UniversallyClosed f')
  exact ⟨⟩

end PhilipponFieldModelProperties



set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponFiniteCurveCover

/-- A smooth proper geometric curve cover and its map descend together to a finite
intermediate field. The map to the original curve remains proper and surjective. -/
theorem exists_finite_smooth_proper_cover
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective b := (PhilipponFieldModelProperties.fpqc_fieldMap k K).1.1
  obtain ⟨Z, a, ha, hsurj, hsmooth, _hdZ, _emb⟩ :=
    AlgebraicGeometry.exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one k K π hdim
  letI := ha
  letI := hsurj
  let pZ : Z ⟶ Spec (.of K) := a ≫ pullback.snd π b
  haveI : IsProper pZ := inferInstance
  letI : Smooth pZ := hsmooth
  letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace π
  letI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated π
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace pZ
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated pZ
  let φ : Z ⟶ C := a ≫ pullback.fst π b
  have hφ : φ ≫ π = pZ ≫ b := by
    simp only [φ, pZ, Category.assoc, pullback.condition]
  haveI : Surjective φ := inferInstance
  obtain ⟨E, hE, Y, p, hYqc, hYqs, hpft, g, f, hpb, hover, hrec⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic k K C π Z pZ φ hφ
  letI := hE
  letI := hpft
  have hs : Smooth p := PhilipponFieldModelProperties.smooth_of_isPullback_field
    E K p pZ g hpb hsmooth
  have hp : IsProper p := PhilipponFieldModelProperties.proper_of_isPullback_field
    E K p pZ g hpb inferInstance
  letI := hp
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsProper (f ≫ π) := by rw [hover]; infer_instance
  have hf : IsProper f := IsProper.of_comp f π
  have hsf : Surjective f := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := (inferInstance : Surjective φ).surj x
    refine ⟨g z, ?_⟩
    change (g ≫ f) z = x
    rw [hrec]
    exact hz
  exact ⟨E, hE, Y, f, p, hf, hsf, hs, hp, hover⟩

end PhilipponFiniteCurveCover


theorem solution
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  exact PhilipponFiniteCurveCover.exists_finite_smooth_proper_cover k K π hdim
