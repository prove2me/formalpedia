-- Prove2me | solution 1 for AlgebraicGeometry.IdealSheafData.flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/44e3aac9-00c0-5f62-a8b1-228651f1b34c

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

namespace P2mWs41USc1

open _root_.AlgebraicGeometry.Scheme in

theorem of_forall_affineOpens {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {XH H : Scheme.{u}} (I₀ : XH.IdealSheafData) (p : XH ⟶ H)
    (ZV : H.affineOpens → Scheme.{u}) (jV : ∀ V : H.affineOpens, ZV V ⟶ ↑(p ⁻¹ᵁ V.1))
    (hjcl : ∀ V, IsClosedImmersion (jV V))
    (hj : ∀ V, P (jV V ≫ p ∣_ V.1))
    (hI₀ : ∀ V : H.affineOpens, I₀.comap (p ⁻¹ᵁ V.1).ι = (jV V).ker) :
    P (I₀.subschemeι ≫ p) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := P) (fun V : H.affineOpens => V.1) (iSup_affineOpens_eq_top H)
  intro V

  have hker : ∀ J : (↑(p ⁻¹ᵁ V.1) : Scheme.{u}).IdealSheafData, J = (jV V).ker → P (J.subschemeι ≫ p ∣_ V.1) := by
    rintro J rfl
    haveI := hjcl V
    have e : (jV V).toImage ≫ (jV V).ker.subschemeι = jV V := (jV V).toImage_imageι
    have : P ((jV V).toImage ≫ (jV V).ker.subschemeι ≫ p ∣_ V.1) := by
      rw [← Category.assoc, e]; exact hj V
    exact (P.cancel_left_of_respectsIso _ _).mp this
  have h1 := hker _ (hI₀ V)

  rw [morphismRestrict_comp]
  let e : (↑(I₀.subschemeι ⁻¹ᵁ p ⁻¹ᵁ V.1) : Scheme.{u}) ≅ (I₀.comap (p ⁻¹ᵁ V.1).ι).subscheme :=
    (pullbackRestrictIsoRestrict I₀.subschemeι (p ⁻¹ᵁ V.1)).symm ≪≫ pullbackSymmetry I₀.subschemeι (p ⁻¹ᵁ V.1).ι ≪≫
      (I₀.comapIso (p ⁻¹ᵁ V.1).ι).symm
  have hfac : I₀.subschemeι ∣_ p ⁻¹ᵁ V.1 = e.hom ≫ (I₀.comap (p ⁻¹ᵁ V.1).ι).subschemeι := by
    rw [← cancel_mono (p ⁻¹ᵁ V.1).ι]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, morphismRestrict_ι,
      Scheme.IdealSheafData.comapIso_inv_subschemeι, pullbackSymmetry_hom_comp_fst]
    rw [← pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc]
  rw [hfac, Category.assoc]
  exact (P.cancel_left_of_respectsIso e.hom _).mpr h1

end P2mWs41USc1

open P2mWs41USc1 in
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
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι)

    (ZV : H.affineOpens → Scheme.{u})
      (ιV : ∀ V : H.affineOpens, ZV V ⟶ pullback f (V.2.fromSpec ≫ πH))
      (hclV : ∀ V : H.affineOpens, IsClosedImmersion (ιV V))
      (hflV : ∀ V : H.affineOpens, Flat (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (hfpV : ∀ V : H.affineOpens, LocallyOfFinitePresentation (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (jV : ∀ V : H.affineOpens, ZV V ⟶ ↑((pullback.snd f πH) ⁻¹ᵁ V.1))

      (htaut : ∀ V : H.affineOpens,
        pt Γ(H, V.1) (V.2.fromSpec ≫ πH) (ZV V) (ιV V) (hclV V) (hflV V) (hfpV V) = ⟨V.2.fromSpec, rfl⟩)

      (hjcl : ∀ V : H.affineOpens, IsClosedImmersion (jV V))
      (hjV : ∀ V : H.affineOpens,
        jV V ≫ ((pullback.snd f πH) ⁻¹ᵁ V.1).ι =
          ιV V ≫ pullback.map f (V.2.fromSpec ≫ πH) f πH (𝟙 X) V.2.fromSpec (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]))

      (hjfl : ∀ V : H.affineOpens, Flat (jV V ≫ (pullback.snd f πH) ∣_ V.1))
      (hjfp : ∀ V : H.affineOpens, LocallyOfFinitePresentation (jV V ≫ (pullback.snd f πH) ∣_ V.1))

      (hcompat : ∀ V V' : H.affineOpens,
        (jV V).ker.comap ((pullback f πH).homOfLE
            (inf_le_left : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V.1)) =
        (jV V').ker.comap ((pullback f πH).homOfLE
            (inf_le_right : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V'.1)))
    (I₀ : (pullback f πH).IdealSheafData)
    (hI₀ : ∀ V : H.affineOpens, I₀.comap ((pullback.snd f πH) ⁻¹ᵁ V.1).ι = (jV V).ker) :
    Flat (I₀.subschemeι ≫ pullback.snd f πH) ∧ LocallyOfFinitePresentation (I₀.subschemeι ≫ pullback.snd f πH) := by
  exact ⟨of_forall_affineOpens (P := @Flat) I₀ (pullback.snd f πH) ZV jV hjcl hjfl hI₀,
    of_forall_affineOpens (P := @LocallyOfFinitePresentation) I₀ (pullback.snd f πH) ZV jV hjcl hjfp hI₀⟩

end S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker
end P2MW
export P2MW.S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker (solution)
