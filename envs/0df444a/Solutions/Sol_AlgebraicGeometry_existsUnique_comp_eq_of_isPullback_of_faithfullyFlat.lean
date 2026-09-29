-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fb63bc0f-3cb5-5043-b1c4-4a79374b6ece

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace BenchQD1a

theorem flat_specMap {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show (algebraMap S S').Flat
  have h : (algebraMap S S').toAlgebra = ‹Algebra S S'› := Algebra.algebra_ext _ _ fun _ => rfl
  unfold RingHom.Flat
  rw [h]; infer_instance

theorem main
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    {Y : Scheme.{u}} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap S S'))
  let ιL := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))
  let ιR := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)

  haveI : Flat ι := flat_specMap
  haveI : Surjective ι := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  haveI : QuasiCompact ι := inferInstance
  haveI : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : QuasiCompact p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : EffectiveEpi p := inferInstance

  have hSpec : IsPullback ιL ιR ι ι :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')
  have hbig : IsPullback (t'' ≫ ιR) q₁ ι (t' ≫ ι) := hq₁.flip.paste_horiz hSpec.flip
  have hbig' : IsPullback (q₂ ≫ t') q₁ ι (p ≫ t) := by
    rw [hq₂.w, hp.w]; exact hbig
  have hPB : IsPullback q₂ q₁ p p := IsPullback.of_right hbig' hq.symm hp.flip

  have key : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ T'), g₁ ≫ p = g₂ ≫ p → g₁ ≫ φ' = g₂ ≫ φ' := by
    intro Z g₁ g₂ hg
    have h1 := hPB.lift_fst g₂ g₁ hg.symm
    have h2 := hPB.lift_snd g₂ g₁ hg.symm
    calc g₁ ≫ φ' = (hPB.lift g₂ g₁ hg.symm ≫ q₁) ≫ φ' := by rw [h2]
      _ = hPB.lift g₂ g₁ hg.symm ≫ (q₂ ≫ φ') := by rw [Category.assoc, hφ']
      _ = g₂ ≫ φ' := by rw [← Category.assoc, h1]
  refine ⟨EffectiveEpi.desc p φ' key, EffectiveEpi.fac p φ' key, fun φ hφ => EffectiveEpi.uniq p φ' key φ hφ⟩

end BenchQD1a

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    {Y : Scheme.{u}} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' :=
  BenchQD1a.main t t' p hp t'' q₁ q₂ hq₁ hq₂ hq φ' hφ'

end S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat (solution)
