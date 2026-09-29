-- Prove2me | solution 1 for AlgebraicGeometry.surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/397f9a9e-e538-52b6-a803-e3b4065a75be

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FFSquare

theorem specMap_algebraMap {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) := by
  refine ⟨⟨fun x => ?_⟩, ?_, inferInstance⟩
  · haveI : Subsingleton ↥(Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    obtain ⟨y⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of Ω)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap F Ω).Flat
    rw [RingHom.Flat]
    exact inferInstance

theorem main {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
    (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
    Surjective r ∧ Flat r ∧ QuasiCompact r := by
  obtain ⟨h1, h2, h3⟩ := specMap_algebraMap (F := F) (Ω := Ω)
  exact ⟨MorphismProperty.of_isPullback (P := @Surjective) hr.flip h1,
    MorphismProperty.of_isPullback (P := @Flat) hr.flip h2,
    MorphismProperty.of_isPullback (P := @QuasiCompact) hr.flip h3⟩

end FFSquare

theorem solution
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
    (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
    Surjective r ∧ Flat r ∧ QuasiCompact r :=
  FFSquare.main r hr

end S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field (solution)
