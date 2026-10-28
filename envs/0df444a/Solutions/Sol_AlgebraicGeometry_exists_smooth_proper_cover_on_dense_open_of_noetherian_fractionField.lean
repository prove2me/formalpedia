-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_noetherian_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T17:52:53.828963+00:00
-- url     : https://prove2.me/submissions/bcf28fc8-0eca-4cf2-936c-6bc8737f1d9d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_ne_zero_flat_principal_baseChange_of_finiteType
import Theorems.Thm_AlgebraicGeometry_exists_smooth_proper_cover_on_dense_open_of_fractionField

universe u
noncomputable section
set_option linter.style.haveILetI false


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


end PhilipponProperCoverSpread

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
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponFractionFieldLocalization

/-- A prescribed nonzero principal localization embeds into the same actual
fraction field, with its specified base-algebra structure. -/
lemma exists_embedding
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E] (s : B) (hs : s ≠ 0) :
    ∃ γ : Localization.Away s →ₐ[B] E, Function.Injective γ := by
  let γ : Localization.Away s →ₐ[B] E := IsLocalization.Away.liftAlgHom s
    (f := Algebra.ofId B E) (isUnit_iff_ne_zero.mpr (by
      change algebraMap B E s ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective B E).ne hs))
  refine ⟨γ, ?_⟩
  have hM : Submonoid.powers s ≤ nonZeroDivisors B := by
    intro b hb
    obtain ⟨n, rfl⟩ := hb
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs)
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s) γ.toRingHom).mpr
  intro x y
  change algebraMap B (Localization.Away s) x = _ ↔
    γ (algebraMap B (Localization.Away s) x) = γ (algebraMap B (Localization.Away s) y)
  rw [γ.commutes, γ.commutes]
  exact (IsLocalization.injective _ hM).eq_iff.trans
    (IsFractionRing.injective B E).eq_iff.symm

end PhilipponFractionFieldLocalization

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericCoverComparison

/-- Cartesian generic models transport a smooth surjective cover to the
actual pullback families, keeping an exact recovery equation. -/
lemma transport_smooth_surjective_cover
    {C₁ C₂ Y₁ Y₂ T U : Scheme.{u}}
    (p₁ : C₁ ⟶ T) (p₂ : C₂ ⟶ T) (f₁ : Y₁ ⟶ U) (f₂ : Y₂ ⟶ U)
    (b : T ⟶ U) (q₁ : C₁ ⟶ Y₁) (q₂ : C₂ ⟶ Y₂)
    (hp₁ : IsPullback q₁ p₁ f₁ b) (hp₂ : IsPullback q₂ p₂ f₂ b)
    (g : C₁ ⟶ C₂) (hg : g ≫ p₂ = p₁) (hgs : Function.Surjective g) [Smooth p₁] :
    ∃ g' : pullback f₁ b ⟶ pullback f₂ b,
      g' ≫ pullback.snd f₂ b = pullback.snd f₁ b ∧
      Function.Surjective g' ∧ Smooth (pullback.snd f₁ b) ∧
      hp₁.isoPullback.hom ≫ g' = g ≫ hp₂.isoPullback.hom := by
  let e₁ := hp₁.isoPullback
  let e₂ := hp₂.isoPullback
  let g' := e₁.inv ≫ g ≫ e₂.hom
  haveI : Surjective g := ⟨hgs⟩
  have hsur' : Surjective (e₁.inv ≫ g ≫ e₂.hom) := inferInstance
  have hsur : Function.Surjective g' := hsur'.1
  have hscomp : Smooth (e₁.hom ≫ pullback.snd f₁ b) := by
    rw [hp₁.isoPullback_hom_snd]
    infer_instance
  have hsm : Smooth (pullback.snd f₁ b) :=
    (MorphismProperty.cancel_left_of_respectsIso @Smooth e₁.hom _).mp hscomp
  have hover : g' ≫ pullback.snd f₂ b = pullback.snd f₁ b := by
    dsimp only [g', e₂]
    rw [Category.assoc, Category.assoc, hp₂.isoPullback_hom_snd, hg]
    exact hp₁.isoPullback_inv_snd
  refine ⟨g', hover, hsur, hsm, ?_⟩
  dsimp only [g', e₁, e₂]
  simp

end PhilipponGenericCoverComparison

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponGenericMorphismSpread
namespace PhilipponIteratedGenericCover

/-- A further base change retains the given cartesian generic model and
its comparison with the canonical pullback. -/
lemma exists_further_comparison
    {C Y T S V : Scheme.{u}} (p : C ⟶ T) (f : Y ⟶ S) (b : T ⟶ S)
    (q : C ⟶ Y) (hp : IsPullback q p f b)
    (j : V ⟶ S) (c : T ⟶ V) (hc : c ≫ j = b) :
    ∃ r : C ⟶ pullback f j,
      IsPullback r p (pullback.snd f j) c ∧
      r = hp.isoPullback.hom ≫ changeBase f b j c hc ∧
      r ≫ pullback.fst f j = q ∧ r ≫ pullback.snd f j = p ≫ c := by
  let r := hp.isoPullback.hom ≫ changeBase f b j c hc
  have hrf : r ≫ pullback.fst f j = q := by
    dsimp only [r]
    rw [Category.assoc, changeBase_fst, hp.isoPullback_hom_fst]
  have hrs : r ≫ pullback.snd f j = p ≫ c := by
    dsimp only [r]
    rw [Category.assoc, changeBase_snd, ← Category.assoc, hp.isoPullback_hom_snd]
  have hpr : IsPullback r p (pullback.snd f j) c := by
    refine IsPullback.of_right ?_ hrs (IsPullback.of_hasPullback f j)
    rw [hrf, hc]
    exact hp
  exact ⟨r, hpr, rfl, hrf, hrs⟩

end PhilipponIteratedGenericCover

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponGenericMorphismSpread
namespace PhilipponNoetherianCoverSpread

/-- Smooth proper generic covers spread over a dense base open without a
separate target-flatness assumption, retaining the exact original map. -/
theorem exists_smooth_proper_cover_on_dense_open
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} [CompactSpace X₂]
    (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁]
    [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (hgs : Function.Surjective g)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of B)),
      IsOpenImmersion j ∧ DenseRange j ∧
      ∃ (Y₁ Y₂ : Scheme.{u}) (p₁ : Y₁ ⟶ S) (p₂ : Y₂ ⟶ S)
        (t₁ : Y₁ ⟶ X₁) (t₂ : Y₂ ⟶ X₂),
        IsPullback t₁ p₁ f₁ j ∧ IsPullback t₂ p₂ f₂ j ∧ Flat p₂ ∧
        ∃ (h : Y₁ ⟶ Y₂), h ≫ p₂ = p₁ ∧
          Smooth p₁ ∧ IsProper p₁ ∧ IsProper h ∧ Function.Surjective h ∧
          ∃ (b : Spec (.of E) ⟶ S)
            (e₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₁)
            (e₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₂),
            b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B E)) ∧
            IsPullback e₁ (pullback.snd f₁ _) p₁ b ∧
            IsPullback e₂ (pullback.snd f₂ _) p₂ b ∧
            e₁ ≫ t₁ = pullback.fst f₁ _ ∧ e₂ ≫ t₂ = pullback.fst f₂ _ ∧
            e₁ ≫ h = g ≫ e₂ := by
  obtain ⟨a, ha, hflat⟩ := AlgebraicGeometry.exists_ne_zero_flat_principal_baseChange_of_finiteType B f₂
  obtain ⟨γ, hγ⟩ := PhilipponFractionFieldLocalization.exists_embedding B E a ha
  let A := Localization.Away a
  letI : Algebra A E := γ.toRingHom.toAlgebra
  letI : IsScalarTower B A E := IsScalarTower.of_algebraMap_eq fun x => (γ.commutes x).symm
  letI : IsFractionRing A E :=
    PhilipponFractionFieldCoefficients.fractionRing_of_injective_tower (B := B) (A := A) hγ
  haveI : IsDomain A := Function.Injective.isDomain γ.toRingHom hγ
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let dE := Spec.map (CommRingCat.ofHom γ.toRingHom)
  have hdE : dE ≫ bA = bE := by
    dsimp only [dE, bA, bE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) γ.comp_algebraMap
  let p₁ := pullback.snd f₁ bA
  let p₂ := pullback.snd f₂ bA
  haveI : Flat p₂ := hflat
  let q₁ := changeBase f₁ bE bA dE hdE
  let q₂ := changeBase f₂ bE bA dE hdE
  have hp₁ := PhilipponProperCoverSpread.changeBase_isPullback f₁ bE bA dE hdE
  have hp₂ := PhilipponProperCoverSpread.changeBase_isPullback f₂ bE bA dE hdE
  obtain ⟨gA, hgA, hgAs, hsmA, hrecA⟩ :=
    PhilipponGenericCoverComparison.transport_smooth_surjective_cover
      (pullback.snd f₁ bE) (pullback.snd f₂ bE) p₁ p₂ dE q₁ q₂ hp₁ hp₂ g hg hgs
  haveI : Smooth (pullback.snd p₁ dE) := hsmA
  obtain ⟨s, hs, δ, hδ, gD, hgD, _hprD, _hsuD,
    ⟨U, _hdU, hrange, hsmU, hprU, h, hι, hover, hproper, hsurj⟩, hrecD⟩ :=
    AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_fractionField A E p₁ p₂ gA hgA hgAs
  let D := Localization.Away s
  let bD := Spec.map (CommRingCat.ofHom (algebraMap A D))
  let dD := Spec.map (CommRingCat.ofHom δ.toRingHom)
  have hdD : dD ≫ bD = dE := by
    dsimp only [dD, bD, dE]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) δ.comp_algebraMap
  obtain ⟨r₁, hpr₁, hr₁, hrf₁, hrs₁⟩ :=
    PhilipponIteratedGenericCover.exists_further_comparison
      (pullback.snd f₁ bE) p₁ dE q₁ hp₁ bD dD hdD
  obtain ⟨r₂, hpr₂, hr₂, hrf₂, hrs₂⟩ :=
    PhilipponIteratedGenericCover.exists_further_comparison
      (pullback.snd f₂ bE) p₂ dE q₂ hp₂ bD dD hdD
  have hrcover : r₁ ≫ gD = g ≫ r₂ := by
    rw [hr₁, hr₂, Category.assoc]
    have H := hrecD (changeBase p₁ dE bD dD hdD) (changeBase p₂ dE bD dD hdD)
      (changeBase_fst _ _ _ _ _) (changeBase_snd _ _ _ _ _)
      (changeBase_fst _ _ _ _ _) (changeBase_snd _ _ _ _ _)
    rw [H, ← Category.assoc, hrecA, Category.assoc]
  let b := IsOpenImmersion.lift U.ι dD (by simpa only [Scheme.Opens.range_ι] using hrange)
  have hb : b ≫ U.ι = dD := IsOpenImmersion.lift_fac _ _ _
  let j := (U.ι ≫ bD) ≫ bA
  haveI : IsOpenImmersion bA := IsOpenImmersion.of_isLocalization a
  haveI : IsOpenImmersion bD := IsOpenImmersion.of_isLocalization s
  haveI : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hne : Nonempty (U : Scheme) := ⟨⟨dD default, hrange ⟨default, rfl⟩⟩⟩
  letI := hne
  have hdense : DenseRange j := j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
  let Y₁ := ((pullback.snd p₁ bD) ⁻¹ᵁ U : (pullback p₁ bD).Opens)
  let Y₂ := ((pullback.snd p₂ bD) ⁻¹ᵁ U : (pullback p₂ bD).Opens)
  let f₁U := (pullback.snd p₁ bD) ∣_ U
  let f₂U := (pullback.snd p₂ bD) ∣_ U
  let t₁ := (Y₁.ι ≫ pullback.fst p₁ bD) ≫ pullback.fst f₁ bA
  let t₂ := (Y₂.ι ≫ pullback.fst p₂ bD) ≫ pullback.fst f₂ bA
  let hu₁ := (isPullback_morphismRestrict (pullback.snd p₁ bD) U).flip
  let hu₂ := (isPullback_morphismRestrict (pullback.snd p₂ bD) U).flip
  have ht₁ : IsPullback t₁ f₁U f₁ j :=
    (hu₁.paste_horiz (IsPullback.of_hasPullback p₁ bD)).paste_horiz (IsPullback.of_hasPullback f₁ bA)
  have ht₂ : IsPullback t₂ f₂U f₂ j :=
    (hu₂.paste_horiz (IsPullback.of_hasPullback p₂ bD)).paste_horiz (IsPullback.of_hasPullback f₂ bA)
  have hw₁ : r₁ ≫ pullback.snd p₁ bD = ((pullback.snd f₁ bE) ≫ b) ≫ U.ι := by
    rw [Category.assoc, hb]; exact hrs₁
  have hw₂ : r₂ ≫ pullback.snd p₂ bD = ((pullback.snd f₂ bE) ≫ b) ≫ U.ι := by
    rw [Category.assoc, hb]; exact hrs₂
  let e₁ := hu₁.lift r₁ ((pullback.snd f₁ bE) ≫ b) hw₁
  let e₂ := hu₂.lift r₂ ((pullback.snd f₂ bE) ≫ b) hw₂
  have he₁ : IsPullback e₁ (pullback.snd f₁ bE) f₁U b := by
    refine IsPullback.of_right ?_ (hu₁.lift_snd _ _ _) hu₁
    rw [hu₁.lift_fst, hb]; exact hpr₁
  have he₂ : IsPullback e₂ (pullback.snd f₂ bE) f₂U b := by
    refine IsPullback.of_right ?_ (hu₂.lift_snd _ _ _) hu₂
    rw [hu₂.lift_fst, hb]; exact hpr₂
  have hbj : b ≫ j = bE := by
    dsimp only [j]
    calc
      b ≫ ((U.ι ≫ bD) ≫ bA) = ((b ≫ U.ι) ≫ bD) ≫ bA := by simp only [Category.assoc]
      _ = bE := by rw [hb, hdD, hdE]
  have het₁ : e₁ ≫ t₁ = pullback.fst f₁ bE := by
    dsimp only [t₁]
    rw [← Category.assoc, ← Category.assoc, hu₁.lift_fst, hrf₁]
    exact changeBase_fst _ _ _ _ _
  have het₂ : e₂ ≫ t₂ = pullback.fst f₂ bE := by
    dsimp only [t₂]
    rw [← Category.assoc, ← Category.assoc, hu₂.lift_fst, hrf₂]
    exact changeBase_fst _ _ _ _ _
  have hrecover : e₁ ≫ h = g ≫ e₂ := by
    apply (cancel_mono Y₂.ι).mp
    rw [Category.assoc, hι, ← Category.assoc, hu₁.lift_fst,
      hrcover, Category.assoc, hu₂.lift_fst]
  exact ⟨U, j, inferInstance, hdense, Y₁, Y₂, f₁U, f₂U, t₁, t₂, ht₁, ht₂, inferInstance,
    h, hover, hsmU, hprU, hproper, hsurj, b, e₁, e₂, hbj, he₁, he₂, het₁, het₂, hrecover⟩

end PhilipponNoetherianCoverSpread

theorem solution
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} [CompactSpace X₂]
    (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁]
    [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (hgs : Function.Surjective g)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of B)),
      IsOpenImmersion j ∧ DenseRange j ∧
      ∃ (Y₁ Y₂ : Scheme.{u}) (p₁ : Y₁ ⟶ S) (p₂ : Y₂ ⟶ S)
        (t₁ : Y₁ ⟶ X₁) (t₂ : Y₂ ⟶ X₂),
        IsPullback t₁ p₁ f₁ j ∧ IsPullback t₂ p₂ f₂ j ∧ Flat p₂ ∧
        ∃ (h : Y₁ ⟶ Y₂), h ≫ p₂ = p₁ ∧
          Smooth p₁ ∧ IsProper p₁ ∧ IsProper h ∧ Function.Surjective h ∧
          ∃ (b : Spec (.of E) ⟶ S)
            (e₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₁)
            (e₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₂),
            b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B E)) ∧
            IsPullback e₁ (pullback.snd f₁ _) p₁ b ∧
            IsPullback e₂ (pullback.snd f₂ _) p₂ b ∧
            e₁ ≫ t₁ = pullback.fst f₁ _ ∧ e₂ ≫ t₂ = pullback.fst f₂ _ ∧
            e₁ ≫ h = g ≫ e₂ := by
  exact PhilipponNoetherianCoverSpread.exists_smooth_proper_cover_on_dense_open B E f₁ f₂ g hg hgs
