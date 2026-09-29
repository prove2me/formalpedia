-- Prove2me | solution 1 for AlgebraicGeometry.exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/95be9e2e-ad68-568f-bc80-593ae0e4d629

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective

set_option autoImplicit false

universe u

namespace GDich

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem main
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : Spec (CommRingCat.of O) ⟶ S}
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {k : Type u} [Field k] (toκ : O →+* k) (hκ : Function.Surjective toκ)
    {gk : Spec (CommRingCat.of k) ⟶ S} (hφ : Spec.map (CommRingCat.ofHom toκ) ≫ g = gk)
    (x : ↥(pullback f g)) :
    (∃ y : ↥(pullback f gT), (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).base y = x) ∨
    (∃ z : ↥(pullback f gk), (mapOnProdOver f (Spec.map (CommRingCat.ofHom toκ)) hφ).base z = x) := by
  set s : ↥(Spec (CommRingCat.of O)) := (pullback.snd f g).base x with hs
  rcases eq_or_ne s.asIdeal ⊥ with h0 | h0
  ·
    left
    let t : ↥(Spec (CommRingCat.of T')) := ⟨⊥, Ideal.bot_prime⟩
    have hst : (pullback.snd f g).base x = (Spec.map (CommRingCat.ofHom (algebraMap O T'))).base t := by
      apply PrimeSpectrum.ext
      change s.asIdeal = Ideal.comap (algebraMap O T') (⊥ : Ideal T')
      rw [h0, Ideal.comap_bot_of_injective (algebraMap O T') (IsFractionRing.injective O T')]
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) x t hst
    exact ⟨p, hp⟩
  ·
    right
    have hmax : s.asIdeal = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := s.2) h0)
    let t : ↥(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.bot_prime⟩
    have hst : (pullback.snd f g).base x = (Spec.map (CommRingCat.ofHom toκ)).base t := by
      apply PrimeSpectrum.ext
      change s.asIdeal = Ideal.comap toκ (⊥ : Ideal k)
      rw [hmax, ← RingHom.ker_eq_comap_bot]
      exact (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective toκ hκ)).symm
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_mapOnProdOver f (Spec.map (CommRingCat.ofHom toκ)) hφ) x t hst
    exact ⟨p, hp⟩

end GDich

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : Spec (CommRingCat.of O) ⟶ S}
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {k : Type u} [Field k] (toκ : O →+* k) (hκ : Function.Surjective toκ)
    {gk : Spec (CommRingCat.of k) ⟶ S} (hφ : Spec.map (CommRingCat.ofHom toκ) ≫ g = gk)
    (x : ↥(pullback f g)) :
    (∃ y : ↥(pullback f gT), (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).base y = x) ∨
    (∃ z : ↥(pullback f gk), (mapOnProdOver f (Spec.map (CommRingCat.ofHom toκ)) hφ).base z = x) :=
  GDich.main f T' hψ toκ hκ hφ x

end S_AlgebraicGeometry_exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mapOnProdOver_apply_eq_or_of_isFractionRing_of_surjective (solution)
