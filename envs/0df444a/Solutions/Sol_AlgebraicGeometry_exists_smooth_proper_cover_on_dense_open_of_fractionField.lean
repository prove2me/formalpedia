-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T15:38:20.826235+00:00
-- url     : https://prove2.me/submissions/be273702-bd2f-4fe0-8b61-2e563b55aa85

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_principal_localization_hom_of_fractionField

universe u
noncomputable section
set_option linter.style.haveILetI false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponGenericSurjectivity

/-- A closed image containing the generic fibre of a flat family contains
the whole family. -/
lemma surjective_of_generic_fibre_contained
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [UniversallyClosed f] [Flat q]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hf : ∀ y : Y, q y = η → y ∈ Set.range f) :
    Function.Surjective f := by
  intro y
  have hy := hη.specializes (Set.mem_univ (q y))
  obtain ⟨z, hzy, hz⟩ := Flat.generalizingMap q hy
  have hzF : z ∈ Set.range f := hf z hz
  exact hzy.mem_closed f.isClosedMap.isClosed_range hzF

/-- Surjectivity after flat generic base change suffices for a closed map
into a flat family. The original generic-cover map is retained. -/
lemma surjective_of_surjective_generic_cover
    {X Y S C D T : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ S) (b : T ⟶ S)
    (eY : D ⟶ Y) (qE : D ⟶ T) (hpb : IsPullback eY qE q b)
    (eX : C ⟶ X) (g : C ⟶ D) (hg : Function.Surjective g)
    (hrec : eX ≫ f = g ≫ eY)
    [UniversallyClosed f] [Flat q]
    (η : S) (hη : IsGenericPoint η Set.univ) (hb : η ∈ Set.range b) :
    Function.Surjective f := by
  apply surjective_of_generic_fibre_contained f q η hη
  intro y hy
  obtain ⟨t, ht⟩ := hb
  obtain ⟨z, hzy, _⟩ := Scheme.Pullback.exists_preimage_pullback y t (hy.trans ht.symm)
  let d := hpb.isoPullback.inv z
  have hd : eY d = y := by
    change (hpb.isoPullback.inv ≫ eY) z = y
    rw [hpb.isoPullback_inv_fst]
    exact hzy
  obtain ⟨c, hc⟩ := hg d
  refine ⟨eX c, ?_⟩
  change (eX ≫ f) c = y
  rw [hrec, Scheme.Hom.comp_apply, hc, hd]

/-- The image point of an injective ring map to a field is the actual
spectrum's generic point, expressed without a chosen field isomorphism. -/
lemma generic_of_injective_fieldMap
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    (γ : A →+* E) (hγ : Function.Injective γ) :
    IsGenericPoint
      ((Spec.map (CommRingCat.ofHom γ)) (genericPoint (Spec (.of E)))) Set.univ := by
  let b := Spec.map (CommRingCat.ofHom γ)
  haveI : IsDominant b := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical γ).mpr
    rw [(RingHom.injective_iff_ker_eq_bot γ).mp hγ]
    exact bot_le
  have h := (genericPoint_spec (Spec (.of E))).image b.continuous
  simpa only [isGenericPoint_def, Set.image_univ, b.denseRange.closure_range, closure_univ] using h

end PhilipponGenericSurjectivity


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericMorphismSpread

/-- Canonical comparison of two pullbacks with compatible base maps. -/
def changeBase {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    pullback f a ⟶ pullback f b :=
  pullback.lift (pullback.fst f a) (pullback.snd f a ≫ c)
    (by rw [Category.assoc, hc]; exact pullback.condition)

@[reassoc (attr := simp)] lemma changeBase_fst {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.fst f b = pullback.fst f a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma changeBase_snd {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.snd f b = pullback.snd f a ≫ c :=
  pullback.lift_snd _ _ _


end PhilipponGenericMorphismSpread

namespace PhilipponFractionFieldCoefficients
lemma fractionRing_of_injective_tower
    {B A E : Type u} [CommRing B] [CommRing A] [Field E]
    [Algebra B A] [Algebra B E] [Algebra A E] [IsScalarTower B A E]
    [IsFractionRing B E] (h : Function.Injective (algebraMap A E)) :
    IsFractionRing A E := by
  haveI : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr h
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _hb, hx⟩ := IsFractionRing.div_surjective B x
  refine ⟨algebraMap B A a, algebraMap B A b, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply B A E] using hx.symm

end PhilipponFractionFieldCoefficients

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponProperCoverSpread

lemma changeBase_isPullback {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    IsPullback (changeBase f a b c hc) (pullback.snd f a) (pullback.snd f b) c := by
  refine IsPullback.of_right ?_ (changeBase_snd _ _ _ _ _) (IsPullback.of_hasPullback f b)
  rw [changeBase_fst, hc]
  exact IsPullback.of_hasPullback f a

/-- A surjective generic map extends to a proper surjection over a principal
localization if the source is proper and the target is separated and flat. -/
theorem exists_proper_surjective_hom_of_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [Flat f₂] [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hgs : Function.Surjective g) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          IsProper g₀ ∧ Function.Surjective g₀ ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by
  obtain ⟨s, hs, γ, hγ, g₀, hg₀, hrec⟩ :=
    AlgebraicGeometry.exists_principal_localization_hom_of_fractionField B E f₁ f₂ g hg
  let A := Localization.Away s
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let d := Spec.map (CommRingCat.ofHom γ.toRingHom)
  have hd : d ≫ bA = bE := by
    dsimp only [d, bA, bE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  let q₁ := changeBase f₁ bE bA d hd
  let q₂ := changeBase f₂ bE bA d hd
  have hrec' : q₁ ≫ g₀ = g ≫ q₂ :=
    hrec q₁ q₂ (changeBase_fst _ _ _ _ _) (changeBase_snd _ _ _ _ _)
      (changeBase_fst _ _ _ _ _) (changeBase_snd _ _ _ _ _)
  haveI : IsProper (g₀ ≫ pullback.snd f₂ bA) := by rw [hg₀]; infer_instance
  have hpr : IsProper g₀ := IsProper.of_comp g₀ (pullback.snd f₂ bA)
  haveI : IsProper g₀ := hpr
  haveI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  let e := genericPoint (Spec (.of E))
  have hη := PhilipponGenericSurjectivity.generic_of_injective_fieldMap A E γ.toRingHom hγ
  have hsur : Function.Surjective g₀ :=
    PhilipponGenericSurjectivity.surjective_of_surjective_generic_cover
      g₀ (pullback.snd f₂ bA) d q₂ (pullback.snd f₂ bE)
      (changeBase_isPullback f₂ bE bA d hd) q₁ g hgs hrec' (d e) hη ⟨e, rfl⟩
  exact ⟨s, hs, γ, hγ, g₀, hg₀, hpr, hsur, hrec⟩

end PhilipponProperCoverSpread


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponSmoothFamilyOpen

lemma smooth_of_comp_openImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion j] [LocallyOfFinitePresentation f] [Smooth (f ≫ j)] :
    Smooth f := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  have hx : x ∈ (f ≫ j).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (j.stalkMap (f x)) (f.stalkMap x)).mp
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact hx

/-- Smoothness of a flatly covered fibre of a proper finitely presented
morphism extends over a neighbourhood of that fibre's base point. -/
lemma exists_open_of_smooth_pullback
    {Y S C T : Scheme.{u}} (f : Y ⟶ S) (p : C ⟶ T)
    (b : T ⟶ S) (g : C ⟶ Y) (hpb : IsPullback g p f b)
    [IsProper f] [LocallyOfFinitePresentation f] [Smooth p] [Flat b]
    (η : S) (hη : η ∈ Set.range b) :
    ∃ U : S.Opens, η ∈ U ∧ Smooth (f ∣_ U) := by
  let bad : Set Y := (f.smoothLocus : Set Y)ᶜ
  have hbad : IsClosed bad := f.smoothLocus.isOpen.isClosed_compl
  let U : S.Opens := ⟨(f '' bad)ᶜ, (f.isClosedMap bad hbad).isOpen_compl⟩
  have hηU : η ∈ U := by
    rintro ⟨y, hy, hyη⟩
    obtain ⟨t, ht⟩ := hη
    obtain ⟨z, hzy, _⟩ := Scheme.Pullback.exists_preimage_pullback y t (hyη.trans ht.symm)
    let c := hpb.isoPullback.inv z
    have hc : g c = y := by
      change (hpb.isoPullback.inv ≫ g) z = y
      rw [hpb.isoPullback_inv_fst]
      exact hzy
    have hs := Scheme.Hom.smoothLocus_le_preimage_of_isPullback hpb
    have hcS : c ∈ p.smoothLocus := by rw [p.smoothLocus_eq_top]; trivial
    have hyS : y ∈ f.smoothLocus := by simpa only [Scheme.Hom.mem_preimage, hc] using hs hcS
    exact hy hyS
  have hle : f ⁻¹ᵁ U ≤ f.smoothLocus := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hc : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact hle x.property
  have hcomp : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    (isPullback_morphismRestrict f U).w
  haveI : Smooth ((f ∣_ U) ≫ U.ι) := by rw [hcomp]; exact hc
  exact ⟨U, hηU, smooth_of_comp_openImmersion (f ∣_ U) U.ι⟩

end PhilipponSmoothFamilyOpen

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponFamilyCoverRestrict

/-- Restriction of a proper surjective map of families to a base open keeps
the same source and target open subschemes and both covering properties. -/
lemma exists_restrict_cover
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    (hf : f ≫ q = p) [IsProper f] (hs : Function.Surjective f) (U : S.Opens) :
    ∃ g : ((p ⁻¹ᵁ U) : Scheme) ⟶ ((q ⁻¹ᵁ U) : Scheme),
      g ≫ (q ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ f ∧
      g ≫ (q ∣_ U) = (p ∣_ U) ∧ IsProper g ∧ Function.Surjective g := by
  have hPQ : p ⁻¹ᵁ U = f ⁻¹ᵁ (q ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hf]
  let g := f.resLE (q ⁻¹ᵁ U) (p ⁻¹ᵁ U) hPQ.le
  have hg : g ≫ (q ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
  have hpb : IsPullback (p ⁻¹ᵁ U).ι g f (q ⁻¹ᵁ U).ι := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback g (p ⁻¹ᵁ U).ι (q ⁻¹ᵁ U).ι f hg.symm
    simpa only [Scheme.Opens.opensRange_ι] using hPQ.symm
  haveI : Surjective f := ⟨hs⟩
  have hpr : IsProper g := MorphismProperty.of_isPullback hpb inferInstance
  have hsu : Surjective g := MorphismProperty.of_isPullback hpb inferInstance
  have hover : g ≫ (q ∣_ U) = (p ∣_ U) := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, (isPullback_morphismRestrict q U).w,
      ← Category.assoc, hg, Category.assoc, hf]
    exact (isPullback_morphismRestrict p U).w.symm
  exact ⟨g, hg, hover, hpr, hsu.1⟩

end PhilipponFamilyCoverRestrict

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponSmoothCoverSpread

/-- A smooth proper generic cover spreads to a smooth proper covering family
on a dense open, retaining the actual generic morphism and the given base. -/
theorem exists_smooth_proper_cover_on_dense_open
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁] [Flat f₂] [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hgs : Function.Surjective g)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          IsProper g₀ ∧ Function.Surjective g₀ ∧
          (∃ U : (Spec (.of (Localization.Away s))).Opens,
            Dense (U : Set (Spec (.of (Localization.Away s)))) ∧
            Set.range (Spec.map (CommRingCat.ofHom γ.toRingHom)) ⊆ U ∧
            Smooth ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away s))))) ∣_ U) ∧
            IsProper ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away s))))) ∣_ U) ∧
            ∃ h : ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U : Scheme) ⟶
                  ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U : Scheme),
              h ≫ ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U).ι =
                ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U).ι ≫ g₀ ∧
              h ≫ ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                (algebraMap B (Localization.Away s))))) ∣_ U) =
                ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away s))))) ∣_ U) ∧
              IsProper h ∧ Function.Surjective h) ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by
  obtain ⟨s, hs, γ, hγ, g₀, hg₀, hpr, hsu, hrec⟩ :=
    PhilipponProperCoverSpread.exists_proper_surjective_hom_of_fractionField B E f₁ f₂ g hg hgs
  let A := Localization.Away s
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B A E := IsScalarTower.of_algebraMap_eq fun b => (γ.commutes b).symm
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγ
  haveI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let d := Spec.map (CommRingCat.ofHom γ.toRingHom)
  have hd : d ≫ bA = bE := by
    dsimp only [d, bA, bE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  let q₁ := changeBase f₁ bE bA d hd
  have hp₁ := PhilipponProperCoverSpread.changeBase_isPullback f₁ bE bA d hd
  letI : Module.Flat A E := IsLocalization.flat E (nonZeroDivisors A)
  letI : Flat d := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let e : Spec (.of E) := default
  obtain ⟨U, hU, hsm⟩ :=
    PhilipponSmoothFamilyOpen.exists_open_of_smooth_pullback
      (pullback.snd f₁ bA) (pullback.snd f₁ bE) d q₁ hp₁ (d e) ⟨e, rfl⟩
  have hrange : Set.range d ⊆ U := by
    rintro x ⟨e', rfl⟩
    change d e' ∈ U
    rw [Subsingleton.elim e' e]
    exact hU
  have hdense : Dense (U : Set (Spec (.of A))) := U.isOpen.dense ⟨d e, hU⟩
  haveI : IsProper g₀ := hpr
  obtain ⟨h, hι, hover, hproper, hsurj⟩ :=
    PhilipponFamilyCoverRestrict.exists_restrict_cover g₀
      (pullback.snd f₁ bA) (pullback.snd f₂ bA) hg₀ hsu U
  exact ⟨s, hs, γ, hγ, g₀, hg₀, hpr, hsu,
    ⟨U, hdense, hrange, hsm, inferInstance, h, hι, hover, hproper, hsurj⟩, hrec⟩

end PhilipponSmoothCoverSpread

theorem solution
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁] [Flat f₂] [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hgs : Function.Surjective g)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          IsProper g₀ ∧ Function.Surjective g₀ ∧
          (∃ U : (Spec (.of (Localization.Away s))).Opens,
            Dense (U : Set (Spec (.of (Localization.Away s)))) ∧
            Set.range (Spec.map (CommRingCat.ofHom γ.toRingHom)) ⊆ U ∧
            Smooth ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away s))))) ∣_ U) ∧
            IsProper ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away s))))) ∣_ U) ∧
            ∃ h : ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U : Scheme) ⟶
                  ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U : Scheme),
              h ≫ ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U).ι =
                ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U).ι ≫ g₀ ∧
              h ≫ ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                (algebraMap B (Localization.Away s))))) ∣_ U) =
                ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away s))))) ∣_ U) ∧
              IsProper h ∧ Function.Surjective h) ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by
  exact PhilipponSmoothCoverSpread.exists_smooth_proper_cover_on_dense_open B E f₁ f₂ g hg hgs
