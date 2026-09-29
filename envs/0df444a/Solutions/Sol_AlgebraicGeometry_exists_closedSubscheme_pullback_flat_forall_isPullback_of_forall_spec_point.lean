-- Prove2me | solution 1 for AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/217d45ac-30f9-5a4d-9a36-2505a1cbe061

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point
import Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem solution
    (S : Type u) [CommRing S] {X H : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (πH : H ⟶ Spec (CommRingCat.of S))
    (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{u}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s πH)

    (hnat : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{u}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (Z'' : Scheme.{u}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (e : Z'' ⟶ Z),
          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1)

    (hsurj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (Z : Scheme.{u}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          pt S' s Z ι hι hfl hfp = x)

    (hinj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{u}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s)),
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) :
    ∃ (𝒵 : Scheme.{u}) (ι : 𝒵 ⟶ pullback f πH), IsClosedImmersion ι ∧ Flat (ι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι ≫ pullback.snd f πH) ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd f s))
        (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
        ∃ e : Z ⟶ 𝒵,
          IsPullback e (ιZ ≫ pullback.snd f s) (ι ≫ pullback.snd f πH) (pt S' s Z ιZ hι hfl hfp).1 ∧
          ιZ ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
              (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = e ≫ ι := by

  obtain ⟨ZV, ιV, hclV, hflV, hfpV, jV, htaut, hjcl, hjV, hjfl, hjfp, hcompat⟩ :=
    AlgebraicGeometry.exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point S f πH pt hnat hsurj hinj

  have hcov : ⨆ V : H.affineOpens, (pullback.snd f πH) ⁻¹ᵁ V.1 = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  obtain ⟨I₀, hI₀⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top
    (fun V : H.affineOpens => (pullback.snd f πH) ⁻¹ᵁ V.1) hcov (fun V => (jV V).ker) (fun V V' => hcompat V V')

  exact AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq S f πH pt hnat hsurj hinj ZV ιV hclV hflV hfpV jV htaut hjcl hjV hjfl hjfp hcompat I₀ hI₀

end S_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
end P2MW
export P2MW.S_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point (solution)
