-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8d8949fe-785e-5983-be3e-5716b4a06f42

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O) ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g = gT)
    {r : ℕ} (E : RelEffCartierDiv f r gT)
    (J : (pullback f g).IdealSheafData) [Flat (J.subschemeι ≫ pullback.snd f g)]
    (hJ : J.comap (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) = E.I) :
    ∃ Ebar : RelEffCartierDiv f r g, Ebar.I = J ∧
      Ebar.pullbackAlong (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ = E := by
  obtain ⟨I, hfinE, hflatE, hlfpE, hrkE⟩ := E
  dsimp only at hJ
  subst hJ
  set ψ : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (algebraMap O T')) with hψdef
  set h := J.subschemeι ≫ pullback.snd f g with hh
  haveI : IsNoetherianRing O := inferInstance

  haveI : IsProper h := inferInstance
  haveI : LocallyOfFiniteType h := inferInstance
  haveI : LocallyOfFinitePresentation h := inferInstance

  have sq := isPullback_comap_snd_over (f := f) J ψ hψ
  haveI := hfinE
  haveI := hflatE
  haveI : LocallyQuasiFinite (pullback.snd h ψ) := by
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  haveI : LocallyQuasiFinite h :=
    AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber
      (R := O) (K := T') h
  haveI : IsFinite h := IsFinite.of_isProper_of_locallyQuasiFinite h

  have hrank : ∀ t : Spec (CommRingCat.of O), h.finrank t = r := by
    have hlc : IsLocallyConstant h.finrank := h.isLocallyConstant_finrank
    haveI : PreconnectedSpace (Spec (CommRingCat.of O)) :=
      inferInstanceAs (PreconnectedSpace (PrimeSpectrum O))
    have hη : ∀ s : Spec (CommRingCat.of T'), h.finrank (ψ s) = r := by
      intro s
      rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ sq s]
      exact hrkE s
    obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of T')) := inferInstance
    intro t
    rw [hlc.apply_eq_of_preconnectedSpace t (ψ s)]
    exact hη s
  refine ⟨⟨J, ‹IsFinite h›, ‹Flat h›, ‹LocallyOfFinitePresentation h›, hrank⟩, rfl, ?_⟩
  exact RelEffCartierDiv.ext rfl

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_flat_of_comap_mapOnProdOver_eq_of_isDiscreteValuationRing (solution)
