-- Prove2me | solution 1 for AlgebraicGeometry.smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/015888f8-65c2-5894-8c4d-93cfa763cef3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation f]
    (hgen : ∀ x : X, (f.base x).asIdeal = ⊥ → x ∈ f.smoothLocus) :
    Smooth (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A L)))) := by
  classical
  set jL := Spec.map (CommRingCat.ofHom (algebraMap A L)) with hjL
  set fst := pullback.fst f jL with hfst
  set snd := pullback.snd f jL with hsnd
  set V : X.Opens := f.smoothLocus with hV

  haveI hsm : Smooth (V.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self V

  have hsq : IsPullback fst snd f jL := IsPullback.of_hasPullback f jL
  have hsqV : IsPullback (fst ∣_ V) ((fst ⁻¹ᵁ V).ι ≫ snd) (V.ι ≫ f) jL :=
    (isPullback_morphismRestrict fst V).paste_vert hsq
  haveI : Smooth ((fst ⁻¹ᵁ V).ι ≫ snd) := MorphismProperty.of_isPullback (P := @Smooth) hsqV hsm

  have hmem : ∀ z : ↑(pullback f jL), fst.base z ∈ V := by
    intro z
    apply hgen
    have h1 : f.base (fst.base z) = jL.base (snd.base z) := by
      change (fst ≫ f).base z = (snd ≫ jL).base z
      rw [pullback.condition]
    rw [h1]
    change Ideal.comap (algebraMap A L) (snd.base z).asIdeal = ⊥
    have h2 : (snd.base z).asIdeal = ⊥ := by
      ext a; simp only [Ideal.mem_bot]
      constructor
      · intro ha; by_contra hne
        exact (snd.base z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha (IsUnit.mk0 a hne))
      · rintro rfl; exact Ideal.zero_mem _
    rw [h2, Ideal.comap_bot_of_injective _ (IsFractionRing.injective A L)]

  have htop : ((fst ⁻¹ᵁ V).ι ≫ snd).smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top _
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine top_le_iff.mp (fun z _ => ?_)
  have hz' : (⟨z, hmem z⟩ : ↥(fst ⁻¹ᵁ V)) ∈ (fst ⁻¹ᵁ V).ι ⁻¹ᵁ snd.smoothLocus := by
    rw [htop]; trivial
  exact hz'

end S_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing
end P2MW
export P2MW.S_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing (solution)
