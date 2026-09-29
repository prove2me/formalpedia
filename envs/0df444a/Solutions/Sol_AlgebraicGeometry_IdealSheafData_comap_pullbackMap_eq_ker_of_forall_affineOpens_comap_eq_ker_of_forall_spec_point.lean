-- Prove2me | solution 1 for AlgebraicGeometry.IdealSheafData.comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ca002728-0545-5926-8ca3-1dff82dda24f

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace UScSol

section bc

variable {X B T T' : Scheme.{u}} (f : X ⟶ B) (g : T ⟶ B) (g' : T' ⟶ B) (a : T' ⟶ T)

@[scoped simp]
theorem bcMap_fst (e₁ : f ≫ 𝟙 B = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 B = a ≫ g) :
    pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂ ≫ pullback.fst f g = pullback.fst f g' := by
  show pullback.lift _ _ _ ≫ _ = _
  rw [pullback.lift_fst, Category.comp_id]

@[scoped simp]
theorem bcMap_snd (e₁ : f ≫ 𝟙 B = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 B = a ≫ g) :
    pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂ ≫ pullback.snd f g = pullback.snd f g' ≫ a := by
  show pullback.lift _ _ _ ≫ _ = _
  rw [pullback.lift_snd]

theorem isPullback_bcMap (e₁ : f ≫ 𝟙 B = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 B = a ≫ g) :
    IsPullback (pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂) (pullback.snd f g') (pullback.snd f g) a := by
  have ha : a ≫ g = g' := by rw [← e₂, Category.comp_id]
  refine IsPullback.of_right (h₁₂ := pullback.fst f g) (h₂₂ := g) (v₁₃ := f) ?_ (bcMap_snd f g g' a e₁ e₂) ?_
  · rw [bcMap_fst, ha]
    exact IsPullback.of_hasPullback f g'
  · exact IsPullback.of_hasPullback f g

theorem isOpenImmersion_bcMap [IsOpenImmersion a] (e₁ : f ≫ 𝟙 B = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 B = a ≫ g) :
    IsOpenImmersion (pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂) :=
  MorphismProperty.of_isPullback (isPullback_bcMap f g g' a e₁ e₂).flip inferInstance

theorem range_bcMap (e₁ : f ≫ 𝟙 B = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 B = a ≫ g) :
    Set.range (pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂) = (pullback.snd f g) ⁻¹' Set.range a := by
  have h := isPullback_bcMap f g g' a e₁ e₂
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr, Set.image_univ, Scheme.Pullback.range_fst]
  exact (ConcreteCategory.bijective_of_isIso h.isoPullback.hom.base).2

theorem bcMap_comp {T'' : Scheme.{u}} (g'' : T'' ⟶ B) (a' : T'' ⟶ T') (e₁ : f ≫ 𝟙 B = 𝟙 X ≫ f)
    (e₂ : g' ≫ 𝟙 B = a ≫ g) (e₂' : g'' ≫ 𝟙 B = a' ≫ g') (e₂'' : g'' ≫ 𝟙 B = (a' ≫ a) ≫ g) :
    pullback.map f g'' f g' (𝟙 X) a' (𝟙 B) e₁ e₂' ≫ pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂ =
      pullback.map f g'' f g (𝟙 X) (a' ≫ a) (𝟙 B) e₁ e₂'' := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, bcMap_fst, bcMap_fst]
  · rw [Category.assoc, bcMap_snd, ← Category.assoc, bcMap_snd, bcMap_snd, Category.assoc]

theorem bcMap_congr {a a' : T' ⟶ T} (h : a = a') (e₁ e₁' : f ≫ 𝟙 B = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 B = a ≫ g)
    (e₂' : g' ≫ 𝟙 B = a' ≫ g) :
    pullback.map f g' f g (𝟙 X) a (𝟙 B) e₁ e₂ = pullback.map f g' f g (𝟙 X) a' (𝟙 B) e₁' e₂' := by
  subst h; rfl

end bc

section chart

variable {S : Type u} [CommRing S] {X H : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (πH : H ⟶ Spec (CommRingCat.of S))

noncomputable abbrev mV (V : H.affineOpens) : pullback f (V.2.fromSpec ≫ πH) ⟶ pullback f πH :=
  pullback.map f (V.2.fromSpec ≫ πH) f πH (𝟙 X) V.2.fromSpec (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id])

scoped instance isOpenImmersion_mV (V : H.affineOpens) : IsOpenImmersion (mV f πH V) :=
  isOpenImmersion_bcMap _ _ _ _ _ _

theorem range_mV (V : H.affineOpens) :
    Set.range (mV f πH V) = Set.range ((pullback.snd f πH) ⁻¹ᵁ V.1).ι := by
  rw [range_bcMap, IsAffineOpen.range_fromSpec, Scheme.Opens.range_ι]
  rfl

noncomputable def eV (V : H.affineOpens) : pullback f (V.2.fromSpec ≫ πH) ≅ ↑((pullback.snd f πH) ⁻¹ᵁ V.1) :=
  IsOpenImmersion.isoOfRangeEq (mV f πH V) ((pullback.snd f πH) ⁻¹ᵁ V.1).ι (range_mV f πH V)

@[scoped simp]
theorem eV_hom_ι (V : H.affineOpens) : (eV f πH V).hom ≫ ((pullback.snd f πH) ⁻¹ᵁ V.1).ι = mV f πH V :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem mV_snd (V : H.affineOpens) : mV f πH V ≫ pullback.snd f πH = pullback.snd _ _ ≫ V.2.fromSpec :=
  bcMap_snd _ _ _ _ _ _

end chart

theorem ker_comp_iso_comap {Z A B : Scheme.{u}} (i : Z ⟶ A) [IsClosedImmersion i] (e : A ≅ B) :
    (i ≫ e.hom).ker.comap e.hom = i.ker := by
  have sq : IsPullback i (𝟙 Z) e.hom (i ≫ e.hom) := IsPullback.of_vert_isIso ⟨by rw [Category.id_comp]⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h := Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom (pullback.fst e.hom (i ≫ e.hom))
  rw [sq.isoPullback_hom_fst] at h
  exact h.symm

theorem idealSheafData_ext_of_openImmersions {Y : Scheme.{u}} {κ : Type u} (Yk : κ → Scheme.{u}) (nk : ∀ k, Yk k ⟶ Y)
    [hn : ∀ k, IsOpenImmersion (nk k)] (hcov : ∀ y : Y, ∃ k, y ∈ Set.range (nk k)) (I J : Y.IdealSheafData)
    (h : ∀ k, I.comap (nk k) = J.comap (nk k)) : I = J := by
  classical
  let Uof : (Σ k : κ, (Yk k).affineOpens) → Y.affineOpens :=
    fun i => ⟨(nk i.1) ''ᵁ i.2.1, i.2.2.image_of_isOpenImmersion _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top Uof ?_ fun i => ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨k, z, rfl⟩ := hcov y
    obtain ⟨U₀, hU₀aff, hzU₀, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp ((Yk k).isBasis_affineOpens))
      (show z ∈ (⊤ : (Yk k).Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, ⟨U₀, hU₀aff⟩⟩, ⟨z, hzU₀, rfl⟩⟩
  · have hk := congrArg (fun I' : (Yk i.1).IdealSheafData => I'.ideal i.2) (h i.1)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hk
    exact Ideal.comap_injective_of_surjective _ ((nk i.1).appIso i.2.1).symm.commRingCatIsoToRingEquiv.surjective hk

section transport

variable
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

include hnat in
theorem transport_model {S' S'' : Type u} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (Z : Scheme.{u}) (ι : Z ⟶ pullback f s) (hcl : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) :
    ∃ (Z'' : Scheme.{u}) (ι'' : Z'' ⟶ pullback f s'') (hcl'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
      (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s'')),
      (pt S'' s'' Z'' ι'' hcl'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hcl hfl hfp).1 ∧
      ι.ker.comap (pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hs])) = ι''.ker := by
  haveI := hcl
  let n := pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hs])
  let Z'' := pullback n ι
  let ι'' : Z'' ⟶ pullback f s'' := pullback.fst n ι
  have P : IsPullback (pullback.snd n ι) (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) :=
    (IsPullback.of_hasPullback n ι).flip.paste_vert (isPullback_bcMap f s s'' _ _ _)
  have hcl'' : IsClosedImmersion ι'' := inferInstance
  have hfl'' : Flat (ι'' ≫ pullback.snd f s'') := MorphismProperty.of_isPullback P hfl
  have hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s'') := MorphismProperty.of_isPullback P hfp
  refine ⟨Z'', ι'', hcl'', hfl'', hfp'', ?_, ?_⟩
  · exact hnat S' S'' ψ s s'' hs Z ι hcl hfl hfp Z'' ι'' hcl'' hfl'' hfp'' (pullback.snd n ι) P pullback.condition
  · exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion ι n).symm

end transport

end UScSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.UScSol"

open UScSol in
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
    ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd f s))
      (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
      I₀.comap (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2])) = ιZ.ker := by
  classical
  intro S' _ s Z ιZ hι hfl hfp
  haveI := hι

  set x := pt S' s Z ιZ hι hfl hfp with hx

  have hIV : ∀ V : H.affineOpens, I₀.comap (mV f πH V) = (ιV V).ker := by
    intro V
    haveI := hclV V
    have hj : jV V = ιV V ≫ (eV f πH V).hom := by
      rw [← cancel_mono ((pullback.snd f πH ⁻¹ᵁ V.1).ι), Category.assoc, eV_hom_ι]; exact hjV V
    rw [← eV_hom_ι, Scheme.IdealSheafData.comap_comp, hI₀, hj, ker_comp_iso_comap]

  let κ := Σ V : H.affineOpens, {g : S' // (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S')) ⊆ x.1.base ⁻¹' (V.1 : Set H)}
  let Sg : κ → Type u := fun k => Localization.Away k.2.1
  letI : ∀ k, CommRing (Sg k) := fun k => inferInstance
  let ψ : ∀ k : κ, S' →+* Sg k := fun k => algebraMap S' (Localization.Away k.2.1)
  let sg : ∀ k : κ, Spec (CommRingCat.of (Sg k)) ⟶ Spec (CommRingCat.of S) := fun k => Spec.map (CommRingCat.ofHom (ψ k)) ≫ s
  let nk : ∀ k : κ, pullback f (sg k) ⟶ pullback f s := fun k =>
    pullback.map f (sg k) f s (𝟙 X) (Spec.map (CommRingCat.ofHom (ψ k))) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id])
  haveI : ∀ k, IsOpenImmersion (nk k) := fun k => isOpenImmersion_bcMap _ _ _ _ _ _
  have hrange : ∀ k : κ, Set.range (Spec.map (CommRingCat.ofHom (ψ k))) = (PrimeSpectrum.basicOpen k.2.1 : Set (PrimeSpectrum S')) :=
    fun k => PrimeSpectrum.localization_away_comap_range (Localization.Away k.2.1) k.2.1
  refine idealSheafData_ext_of_openImmersions (fun k => pullback f (sg k)) nk (fun y => ?_) _ _ fun k => ?_
  ·
    obtain ⟨V₀, hV₀aff, hyV₀, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp H.isBasis_affineOpens)
      (show x.1 (pullback.snd f s y) ∈ (⊤ : H.Opens) from trivial)
    have hopen : IsOpen (x.1.base ⁻¹' (V₀ : Set H)) := V₀.2.preimage x.1.base.hom.continuous
    obtain ⟨_, ⟨g, rfl⟩, hyg, hgV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show pullback.snd f s y ∈ x.1.base ⁻¹' (V₀ : Set H) from hyV₀) hopen
    refine ⟨⟨⟨V₀, hV₀aff⟩, ⟨g, hgV⟩⟩, ?_⟩
    rw [range_bcMap, Set.mem_preimage, hrange]
    exact hyg
  ·
    obtain ⟨V, g, hg⟩ := k

    obtain ⟨Z₁, ι₁, hcl₁, hfl₁, hfp₁, hpt₁, hker₁⟩ :=
      transport_model S f πH pt hnat (ψ ⟨V, g, hg⟩) s (sg ⟨V, g, hg⟩) rfl Z ιZ hι hfl hfp

    have hsub : Set.range (Spec.map (CommRingCat.ofHom (ψ ⟨V, g, hg⟩)) ≫ x.1) ⊆ Set.range V.2.fromSpec := by
      rw [IsAffineOpen.range_fromSpec, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
      exact Set.image_subset_iff.mpr hg
    let l : Spec (CommRingCat.of (Sg ⟨V, g, hg⟩)) ⟶ Spec Γ(H, V.1) := IsOpenImmersion.lift V.2.fromSpec _ hsub
    have hl : l ≫ V.2.fromSpec = Spec.map (CommRingCat.ofHom (ψ ⟨V, g, hg⟩)) ≫ x.1 := IsOpenImmersion.lift_fac _ _ hsub
    let φ : Γ(H, V.1) →+* Sg ⟨V, g, hg⟩ := (Spec.preimage l).hom
    have hφ : Spec.map (CommRingCat.ofHom φ) = l := by rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage l
    have hs' : Spec.map (CommRingCat.ofHom φ) ≫ (V.2.fromSpec ≫ πH) = sg ⟨V, g, hg⟩ := by
      rw [hφ, ← Category.assoc, hl, Category.assoc, x.2]

    obtain ⟨Z₂, ι₂, hcl₂, hfl₂, hfp₂, hpt₂, hker₂⟩ :=
      transport_model S f πH pt hnat φ (V.2.fromSpec ≫ πH) (sg ⟨V, g, hg⟩) hs' (ZV V) (ιV V) (hclV V) (hflV V) (hfpV V)

    have hpteq : pt _ (sg ⟨V, g, hg⟩) Z₁ ι₁ hcl₁ hfl₁ hfp₁ = pt _ (sg ⟨V, g, hg⟩) Z₂ ι₂ hcl₂ hfl₂ hfp₂ := by
      apply Subtype.ext
      rw [hpt₁, hpt₂, htaut V, hφ]
      exact hl.symm
    obtain ⟨e, he⟩ := hinj _ (sg ⟨V, g, hg⟩) Z₁ Z₂ ι₁ ι₂ hcl₁ hcl₂ hfl₁ hfl₂ hfp₁ hfp₂ hpteq
    have hk12 : ι₁.ker = ι₂.ker := by rw [← he, Scheme.Hom.ker_comp_of_isIso]

    have hnm : nk ⟨V, g, hg⟩ ≫ pullback.map f s f πH (𝟙 X) x.1 (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, x.2]) =
        pullback.map f (sg ⟨V, g, hg⟩) f (V.2.fromSpec ≫ πH) (𝟙 X) (Spec.map (CommRingCat.ofHom φ)) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hs']) ≫ mV f πH V := by
      rw [bcMap_comp f πH s x.1 (sg ⟨V, g, hg⟩) (Spec.map (CommRingCat.ofHom (ψ ⟨V, g, hg⟩))) _ _ _
          (by rw [Category.comp_id, Category.assoc, x.2]),
        bcMap_comp f πH (V.2.fromSpec ≫ πH) V.2.fromSpec (sg ⟨V, g, hg⟩) (Spec.map (CommRingCat.ofHom φ)) _ _ _
          (by rw [Category.comp_id, Category.assoc, hs'])]
      exact bcMap_congr f πH (sg ⟨V, g, hg⟩) (by rw [hφ]; exact hl.symm) _ _ _ _
    rw [← Scheme.IdealSheafData.comap_comp, hnm, Scheme.IdealSheafData.comap_comp, hIV, hker₂, ← hk12]
    exact hker₁.symm

end S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point
end P2MW
export P2MW.S_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point (solution)
