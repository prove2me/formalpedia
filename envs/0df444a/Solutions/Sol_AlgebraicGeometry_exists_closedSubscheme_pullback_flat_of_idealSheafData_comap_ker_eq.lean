-- Prove2me | solution 1 for AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/58e2b98f-a700-5de2-83d2-e8f24144da2d

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker
import Theorems.Thm_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

namespace UnivSubAsm

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem isPullback_map {X B W W' : Scheme.{u}} (f : X ⟶ B) (t : W ⟶ B) (d : W' ⟶ W) (t' : W' ⟶ B) (hd : t' = d ≫ t)
    (h : t' ≫ 𝟙 B = d ≫ t) :
    IsPullback (pullback.map f t' f t (𝟙 X) d (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h)
      (pullback.snd f t') (pullback.snd f t) d := by
  refine IsPullback.of_right ?_ (by simp [pullback.map]) (IsPullback.of_hasPullback f t)
  have e : pullback.map f t' f t (𝟙 X) d (𝟙 B) (by rw [Category.comp_id, Category.id_comp]) h ≫ pullback.fst f t =
      pullback.fst f t' := by simp [pullback.map]
  rw [e, ← hd]
  exact IsPullback.of_hasPullback f t'

end UnivSubAsm

open UnivSubAsm

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
    ∃ (𝒵 : Scheme.{u}) (ι : 𝒵 ⟶ pullback f πH), IsClosedImmersion ι ∧ Flat (ι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι ≫ pullback.snd f πH) ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd f s))
        (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
        ∃ e : Z ⟶ 𝒵,
          IsPullback e (ιZ ≫ pullback.snd f s) (ι ≫ pullback.snd f πH) (pt S' s Z ιZ hι hfl hfp).1 ∧
          ιZ ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
              (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = e ≫ ι := by
  classical
  obtain ⟨hflat, hlfp⟩ := AlgebraicGeometry.IdealSheafData.flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker S f πH pt hnat hsurj hinj ZV ιV hclV hflV hfpV jV htaut hjcl hjV hjfl hjfp hcompat I₀ hI₀
  refine ⟨I₀.subscheme, I₀.subschemeι, inferInstance, hflat, hlfp, ?_⟩
  intro S' _ s Z ιZ hι hfl hfp
  haveI := hι
  have hK : I₀.comap (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2])) = ιZ.ker := AlgebraicGeometry.IdealSheafData.comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point S f πH pt hnat hsurj hinj ZV ιV hclV hflV hfpV jV htaut hjcl hjV hjfl hjfp hcompat I₀ hI₀ S' s Z ιZ hι hfl hfp
  have hker : (I₀.comap (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]))).subschemeι.ker = ιZ.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hK]
  haveI : IsIso (IsClosedImmersion.lift _ ιZ hker.le) := IsClosedImmersion.isIso_lift _ _ hker
  let i : Z ≅ pullback (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2])) I₀.subschemeι :=
    asIso (IsClosedImmersion.lift _ ιZ hker.le) ≪≫ I₀.comapIso _
  have hi₁ : i.hom ≫ pullback.fst _ _ = ιZ := by
    simp [i, Scheme.IdealSheafData.comapIso_hom_fst]
  have hcomm : ιZ ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = (i.hom ≫ pullback.snd _ _) ≫ I₀.subschemeι := by
    have h0 : (i.hom ≫ pullback.fst _ _) ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = (i.hom ≫ pullback.snd _ _) ≫ I₀.subschemeι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    rwa [hi₁] at h0
  refine ⟨i.hom ≫ pullback.snd _ _, ?_, hcomm⟩
  have sq : IsPullback ιZ (i.hom ≫ pullback.snd _ _) (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2])) I₀.subschemeι :=
    IsPullback.of_iso_pullback ⟨hcomm⟩ i hi₁ rfl
  have sqB : IsPullback (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2])) (pullback.snd f s) (pullback.snd f πH) (pt S' s Z ιZ hι hfl hfp).1 :=
    isPullback_map f πH (pt S' s Z ιZ hι hfl hfp).1 s (pt S' s Z ιZ hι hfl hfp).2.symm _
  exact sq.flip.paste_vert sqB

end S_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq (solution)
