-- Prove2me | solution 1 for AlgebraicGeometry.exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/321f27e2-32cb-505f-a223-523ea4cec0d1

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace USbSol

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

noncomputable abbrev resH {V W : H.Opens} (h : W ≤ V) : Γ(H, V) ⟶ Γ(H, W) := H.presheaf.map (homOfLE h).op

theorem spec_resH_fromSpec (V W : H.affineOpens) (h : W.1 ≤ V.1) :
    Spec.map (resH (H := H) h) ≫ V.2.fromSpec = W.2.fromSpec :=
  IsAffineOpen.map_fromSpec V.2 W.2 (homOfLE h).op

noncomputable abbrev nVW (V W : H.affineOpens) (h : W.1 ≤ V.1) :
    pullback f (W.2.fromSpec ≫ πH) ⟶ pullback f (V.2.fromSpec ≫ πH) :=
  pullback.map f (W.2.fromSpec ≫ πH) f (V.2.fromSpec ≫ πH) (𝟙 X) (Spec.map (CommRingCat.ofHom (resH (H := H) h).hom)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, CommRingCat.ofHom_hom, ← Category.assoc, spec_resH_fromSpec])

theorem nVW_mV (V W : H.affineOpens) (h : W.1 ≤ V.1) : nVW f πH V W h ≫ mV f πH V = mV f πH W := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, bcMap_fst, bcMap_fst]
  · rw [Category.assoc, bcMap_snd, ← Category.assoc, bcMap_snd, bcMap_snd, Category.assoc, CommRingCat.ofHom_hom,
      spec_resH_fromSpec]

theorem isPullback_nVW (V W : H.affineOpens) (h : W.1 ≤ V.1) :
    IsPullback (nVW f πH V W h) (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom (resH (H := H) h).hom)) :=
  isPullback_bcMap _ _ _ _ _ _

theorem preimage_mono {V W : H.Opens} (h : W ≤ V) : (pullback.snd f πH) ⁻¹ᵁ W ≤ (pullback.snd f πH) ⁻¹ᵁ V :=
  fun _ hx => h hx

theorem eV_homOfLE (V W : H.affineOpens) (h : W.1 ≤ V.1) :
    (eV f πH W).hom ≫ (pullback f πH).homOfLE (preimage_mono f πH h) = nVW f πH V W h ≫ (eV f πH V).hom := by
  rw [← cancel_mono ((pullback.snd f πH) ⁻¹ᵁ V.1).ι, Category.assoc, Scheme.homOfLE_ι, eV_hom_ι, Category.assoc, eV_hom_ι,
    nVW_mV]

end chart

section models

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

theorem eV_hom_morphismRestrict (V : H.affineOpens) :
    (eV f πH V).hom ≫ (pullback.snd f πH ∣_ V.1) = pullback.snd f (V.2.fromSpec ≫ πH) ≫ V.2.isoSpec.inv := by
  rw [← cancel_mono V.1.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, eV_hom_ι, mV_snd, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι]

include hnat in

theorem restrict_model (V W : H.affineOpens) (hWV : W.1 ≤ V.1)
    (Z : Scheme.{u}) (ι : Z ⟶ pullback f (V.2.fromSpec ≫ πH)) (hcl : IsClosedImmersion ι)
    (hfl : Flat (ι ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
    (hpt : pt Γ(H, V.1) (V.2.fromSpec ≫ πH) Z ι hcl hfl hfp = ⟨V.2.fromSpec, rfl⟩) :
    ∃ (Z' : Scheme.{u}) (ι' : Z' ⟶ pullback f (W.2.fromSpec ≫ πH)) (hcl' : IsClosedImmersion ι')
      (hfl' : Flat (ι' ≫ pullback.snd f (W.2.fromSpec ≫ πH)))
      (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f (W.2.fromSpec ≫ πH))),
      pt Γ(H, W.1) (W.2.fromSpec ≫ πH) Z' ι' hcl' hfl' hfp' = ⟨W.2.fromSpec, rfl⟩ ∧
      (ι ≫ (eV f πH V).hom).ker.comap ((pullback f πH).homOfLE (preimage_mono f πH hWV)) = (ι' ≫ (eV f πH W).hom).ker := by
  haveI := hcl
  let n := nVW f πH V W hWV
  let Z' := pullback n ι
  let ι' : Z' ⟶ pullback f (W.2.fromSpec ≫ πH) := pullback.fst n ι

  have P : IsPullback (pullback.snd n ι) (ι' ≫ pullback.snd f (W.2.fromSpec ≫ πH)) (ι ≫ pullback.snd f (V.2.fromSpec ≫ πH))
      (Spec.map (CommRingCat.ofHom (resH (H := H) hWV).hom)) :=
    (IsPullback.of_hasPullback n ι).flip.paste_vert (isPullback_nVW f πH V W hWV)
  have hcl' : IsClosedImmersion ι' := inferInstance
  have hfl' : Flat (ι' ≫ pullback.snd f (W.2.fromSpec ≫ πH)) := MorphismProperty.of_isPullback P hfl
  have hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f (W.2.fromSpec ≫ πH)) :=
    MorphismProperty.of_isPullback P hfp
  have hs : Spec.map (CommRingCat.ofHom (resH (H := H) hWV).hom) ≫ (V.2.fromSpec ≫ πH) = W.2.fromSpec ≫ πH := by
    rw [CommRingCat.ofHom_hom, ← Category.assoc, spec_resH_fromSpec]
  have hn := hnat Γ(H, V.1) Γ(H, W.1) (resH (H := H) hWV).hom (V.2.fromSpec ≫ πH) (W.2.fromSpec ≫ πH) hs
    Z ι hcl hfl hfp Z' ι' hcl' hfl' hfp' (pullback.snd n ι) P pullback.condition
  refine ⟨Z', ι', hcl', hfl', hfp', ?_, ?_⟩
  · apply Subtype.ext
    rw [hn, hpt]
    show Spec.map (CommRingCat.ofHom (resH (H := H) hWV).hom) ≫ V.2.fromSpec = W.2.fromSpec
    rw [CommRingCat.ofHom_hom, spec_resH_fromSpec]
  ·
    have Q : IsPullback (ι' ≫ (eV f πH W).hom) (pullback.snd n ι) ((pullback f πH).homOfLE (preimage_mono f πH hWV))
        (ι ≫ (eV f πH V).hom) := by
      refine IsPullback.of_iso (IsPullback.of_hasPullback n ι) (Iso.refl _) (eV f πH W) (Iso.refl _) (eV f πH V) ?_ ?_ ?_ ?_
      · simp [ι']
      · simp
      · exact (eV_homOfLE f πH V W hWV).symm
      · simp
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← Q.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end models

theorem idealSheafData_ext_of_opens {Y : Scheme.{u}} (O : Y.Opens) {κ : Type u} (Wf : κ → Y.Opens) (hWO : ∀ k, Wf k ≤ O)
    (hcov : ∀ y : Y, y ∈ O → ∃ k, y ∈ Wf k) (I J : (↑O : Scheme.{u}).IdealSheafData)
    (h : ∀ k, I.comap (Y.homOfLE (hWO k)) = J.comap (Y.homOfLE (hWO k))) : I = J := by
  classical
  let Uof : (Σ k : κ, (↑(Wf k) : Scheme.{u}).affineOpens) → (↑O : Scheme.{u}).affineOpens :=
    fun i => ⟨(Y.homOfLE (hWO i.1)) ''ᵁ i.2.1, i.2.2.image_of_isOpenImmersion _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top Uof ?_ fun i => ?_
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨k, hyk⟩ := hcov y hy
    obtain ⟨U₀, hU₀aff, hyU₀, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp ((↑(Wf k) : Scheme.{u}).isBasis_affineOpens))
      (show (⟨y, hyk⟩ : ↑(Wf k)) ∈ (⊤ : (↑(Wf k) : Scheme.{u}).Opens) from trivial)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, ⟨U₀, hU₀aff⟩⟩, ?_⟩
    exact ⟨⟨y, hyk⟩, hyU₀, show (Y.homOfLE (hWO k)) ⟨y, hyk⟩ = ⟨y, hy⟩ from Y.homOfLE_apply' _ y hyk⟩
  · have hk := congrArg (fun I' : (↑(Wf i.1) : Scheme.{u}).IdealSheafData => I'.ideal i.2) (h i.1)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hk
    exact Ideal.comap_injective_of_surjective _
      ((Y.homOfLE (hWO i.1)).appIso i.2.1).symm.commRingCatIsoToRingEquiv.surjective hk

section compat

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

include hnat hinj in

theorem ker_comap_eq_of_le (Z : H.affineOpens → Scheme.{u}) (ι : ∀ V : H.affineOpens, Z V ⟶ pullback f (V.2.fromSpec ≫ πH))
    (hcl : ∀ V : H.affineOpens, IsClosedImmersion (ι V)) (hfl : ∀ V : H.affineOpens, Flat (ι V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
    (hfp : ∀ V : H.affineOpens, LocallyOfFinitePresentation (ι V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
    (hpt : ∀ V : H.affineOpens, pt Γ(H, V.1) (V.2.fromSpec ≫ πH) (Z V) (ι V) (hcl V) (hfl V) (hfp V) = ⟨V.2.fromSpec, rfl⟩)
    (V V' W : H.affineOpens) (hWV : W.1 ≤ V.1) (hWV' : W.1 ≤ V'.1) :
    (ι V ≫ (eV f πH V).hom).ker.comap ((pullback f πH).homOfLE (preimage_mono f πH hWV)) =
    (ι V' ≫ (eV f πH V').hom).ker.comap ((pullback f πH).homOfLE (preimage_mono f πH hWV')) := by
  obtain ⟨Z₁, ι₁, hcl₁, hfl₁, hfp₁, hpt₁, hker₁⟩ :=
    restrict_model S f πH pt hnat V W hWV (Z V) (ι V) (hcl V) (hfl V) (hfp V) (hpt V)
  obtain ⟨Z₂, ι₂, hcl₂, hfl₂, hfp₂, hpt₂, hker₂⟩ :=
    restrict_model S f πH pt hnat V' W hWV' (Z V') (ι V') (hcl V') (hfl V') (hfp V') (hpt V')
  rw [hker₁, hker₂]
  obtain ⟨e, he⟩ := hinj Γ(H, W.1) (W.2.fromSpec ≫ πH) Z₁ Z₂ ι₁ ι₂ hcl₁ hcl₂ hfl₁ hfl₂ hfp₁ hfp₂ (hpt₁.trans hpt₂.symm)
  rw [← he, Category.assoc, Scheme.Hom.ker_comp_of_isIso]

include hnat hinj in

theorem ker_comap_inf_eq (Z : H.affineOpens → Scheme.{u}) (ι : ∀ V : H.affineOpens, Z V ⟶ pullback f (V.2.fromSpec ≫ πH))
    (hcl : ∀ V : H.affineOpens, IsClosedImmersion (ι V)) (hfl : ∀ V : H.affineOpens, Flat (ι V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
    (hfp : ∀ V : H.affineOpens, LocallyOfFinitePresentation (ι V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
    (hpt : ∀ V : H.affineOpens, pt Γ(H, V.1) (V.2.fromSpec ≫ πH) (Z V) (ι V) (hcl V) (hfl V) (hfp V) = ⟨V.2.fromSpec, rfl⟩)
    (V V' : H.affineOpens) :
    (ι V ≫ (eV f πH V).hom).ker.comap ((pullback f πH).homOfLE
        (inf_le_left : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V.1)) =
    (ι V' ≫ (eV f πH V').hom).ker.comap ((pullback f πH).homOfLE
        (inf_le_right : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V'.1)) := by
  refine idealSheafData_ext_of_opens ((pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1)
    (κ := {W : H.affineOpens // W.1 ≤ V.1 ⊓ V'.1}) (fun W => (pullback.snd f πH) ⁻¹ᵁ W.1.1)
    (fun W => le_inf (preimage_mono f πH (W.2.trans inf_le_left)) (preimage_mono f πH (W.2.trans inf_le_right)))
    (fun y hy => ?_) _ _ fun W => ?_
  · obtain ⟨W₀, hW₀aff, hyW₀, hW₀le⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp H.isBasis_affineOpens) (show pullback.snd f πH y ∈ V.1 ⊓ V'.1 from hy)
    exact ⟨⟨⟨W₀, hW₀aff⟩, hW₀le⟩, hyW₀⟩
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_homOfLE,
      Scheme.homOfLE_homOfLE]
    exact ker_comap_eq_of_le S f πH pt hnat hinj Z ι hcl hfl hfp hpt V V' W.1 (W.2.trans inf_le_left) (W.2.trans inf_le_right)

end compat

end USbSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol"

open USbSol in
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
    ∃ (ZV : H.affineOpens → Scheme.{u})
      (ιV : ∀ V : H.affineOpens, ZV V ⟶ pullback f (V.2.fromSpec ≫ πH))
      (hclV : ∀ V : H.affineOpens, IsClosedImmersion (ιV V))
      (hflV : ∀ V : H.affineOpens, Flat (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (hfpV : ∀ V : H.affineOpens, LocallyOfFinitePresentation (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (jV : ∀ V : H.affineOpens, ZV V ⟶ ↑((pullback.snd f πH) ⁻¹ᵁ V.1)),
      (∀ V : H.affineOpens,
        pt Γ(H, V.1) (V.2.fromSpec ≫ πH) (ZV V) (ιV V) (hclV V) (hflV V) (hfpV V) = ⟨V.2.fromSpec, rfl⟩) ∧
      (∀ V : H.affineOpens, IsClosedImmersion (jV V)) ∧
      (∀ V : H.affineOpens,
        jV V ≫ ((pullback.snd f πH) ⁻¹ᵁ V.1).ι =
          ιV V ≫ pullback.map f (V.2.fromSpec ≫ πH) f πH (𝟙 X) V.2.fromSpec (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id])) ∧
      (∀ V : H.affineOpens, Flat (jV V ≫ (pullback.snd f πH) ∣_ V.1)) ∧
      (∀ V : H.affineOpens, LocallyOfFinitePresentation (jV V ≫ (pullback.snd f πH) ∣_ V.1)) ∧
      (∀ V V' : H.affineOpens,
        (jV V).ker.comap ((pullback f πH).homOfLE
            (inf_le_left : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V.1)) =
        (jV V').ker.comap ((pullback f πH).homOfLE
            (inf_le_right : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V'.1))) := by
  classical

  choose Z ι hcl hfl hfp hpt using fun V : H.affineOpens =>
    hsurj Γ(H, V.1) (V.2.fromSpec ≫ πH) ⟨V.2.fromSpec, rfl⟩
  refine ⟨Z, ι, hcl, hfl, hfp, fun V => ι V ≫ (eV f πH V).hom, hpt, fun V => ?_, fun V => ?_, fun V => ?_, fun V => ?_,
    fun V V' => ker_comap_inf_eq S f πH pt hnat hinj Z ι hcl hfl hfp hpt V V'⟩
  · haveI := hcl V; infer_instance
  · rw [Category.assoc, eV_hom_ι]
  · rw [Category.assoc, eV_hom_morphismRestrict, ← Category.assoc]
    haveI := hfl V; infer_instance
  · rw [Category.assoc, eV_hom_morphismRestrict, ← Category.assoc]
    haveI := hfp V; infer_instance

end S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point
end P2MW
export P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point (solution)
